//! Differential tests: the optimal machine against the reference reducer.
//!
//! Three properties are checked, on every closed term up to a small size, on
//! random larger terms, and on a corpus of classic examples:
//!
//! 1. reading back a freshly translated net gives the term back;
//! 2. the machine and the reference reducer agree on the normal form, and the
//!    machine fires exactly one beta interaction per redex family;
//! 3. no rule other than beta changes the term a net stands for.

use levy_core::machine::readback;
use levy_core::translate::translate;
use levy_core::{Halt, Machine, Rule, Term, parse_with, reference};

/// Budget of the reference reducer, in beta-steps plus copied nodes.
const REFERENCE_BUDGET: u64 = 20_000;
/// Fuel of the machine, in interactions.
const MACHINE_FUEL: u64 = 5_000_000;

/// Runs `test` on a thread with a stack large enough for deep terms.
///
/// Terms are trees walked by recursion, and a Church numeral nests as deep
/// as its value, which is more than the default stack of a test thread
/// allows.
fn with_deep_stack(test: impl FnOnce() + Send + 'static) {
    let thread = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(test)
        .expect("the test thread starts");
    if let Err(panic) = thread.join() {
        std::panic::resume_unwind(panic);
    }
}

/// All terms with exactly `size` nodes and free de Bruijn indices below
/// `depth`.
fn terms(size: usize, depth: usize) -> Vec<Term> {
    const NAMES: [&str; 8] = ["a", "b", "c", "d", "e", "f", "g", "h"];
    let mut found = Vec::new();
    match size {
        0 => {}
        1 => found.extend((0..depth).map(Term::Var)),
        _ => {
            let name = NAMES[depth % NAMES.len()];
            found.extend(
                terms(size - 1, depth + 1)
                    .into_iter()
                    .map(|body| Term::lam(name, body)),
            );
            for left in 1..size - 1 {
                let args = terms(size - 1 - left, depth);
                for func in terms(left, depth) {
                    found.extend(args.iter().map(|arg| Term::app(func.clone(), arg.clone())));
                }
            }
        }
    }
    found
}

/// All closed terms with at most `size` nodes, smallest first.
fn closed_terms(size: usize) -> impl Iterator<Item = Term> {
    (1..=size).flat_map(|size| terms(size, 0))
}

/// A SplitMix64 generator: small, seedable and good enough to scatter terms.
struct Random(u64);

impl Random {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let value = (self.0 ^ (self.0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        let value = (value ^ (value >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        value ^ (value >> 31)
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % bound as u64).expect("a value below a usize fits in one")
    }

    /// A random term of roughly `size` nodes with free indices below `depth`.
    ///
    /// `redexes` is the chance in ten that an application gets an abstraction
    /// as its function, which makes it a redex.
    fn term(&mut self, size: usize, depth: usize, redexes: usize) -> Term {
        if size <= 1 && depth > 0 {
            Term::Var(self.below(depth))
        } else if size <= 2 || depth == 0 || self.below(5) < 2 {
            self.abstraction(size, depth, redexes)
        } else {
            let left = 1 + self.below(size - 2);
            let func = if self.below(10) < redexes {
                self.abstraction(left, depth, redexes)
            } else {
                self.term(left, depth, redexes)
            };
            Term::app(func, self.term(size - 1 - left, depth, redexes))
        }
    }

    fn abstraction(&mut self, size: usize, depth: usize, redexes: usize) -> Term {
        Term::lam("x", self.term(size.saturating_sub(1), depth + 1, redexes))
    }
}

/// What a comparison between the two reducers saw.
#[derive(Default)]
struct Tally {
    /// Terms the reference reducer brought to normal form.
    compared: u64,
    /// Terms it gave up on.
    skipped: u64,
    /// Beta-steps of normal order, over the compared terms.
    normal_order_steps: u64,
    /// Beta interactions of the machine, over the compared terms.
    optimal_steps: u64,
    /// Compared terms on which sharing saved at least one step.
    shared: u64,
}

impl Tally {
    /// Runs both reducers on `term` and checks them against each other.
    fn compare(&mut self, term: &Term, budget: u64) {
        let mut machine = Machine::new(term).expect("the term is closed");
        let Ok(expected) = reference::normalize(term, budget) else {
            // The term diverges or explodes under substitution. The machine
            // may still succeed, but whatever it does it must keep the net
            // sound.
            let outcome = machine.normalize(10_000);
            assert!(
                !matches!(outcome, Err(Halt::Malformed(_))),
                "{term}: {outcome:?}"
            );
            assert_eq!(machine.net().check(), Ok(()), "{term}");
            self.skipped += 1;
            return;
        };
        let actual = machine.normalize(MACHINE_FUEL);
        assert_eq!(actual.as_ref(), Ok(&expected.normal_form), "{term}");
        assert_eq!(machine.net().check(), Ok(()), "{term}");
        assert_eq!(
            machine.stats().beta,
            expected.families,
            "{term}: beta interactions differ from redex families ({} normal-order steps)",
            expected.beta_steps
        );
        self.compared += 1;
        self.normal_order_steps += expected.beta_steps;
        self.optimal_steps += expected.families;
        self.shared += u64::from(expected.families < expected.beta_steps);
    }

    fn report(&self, what: &str) {
        println!(
            "{what}: {} compared, {} skipped, {} normal-order steps, {} optimal steps, \
             sharing helped on {}",
            self.compared, self.skipped, self.normal_order_steps, self.optimal_steps, self.shared
        );
    }
}

#[test]
fn readback_inverts_translation() {
    with_deep_stack(check_readback_inverts_translation);
}

fn check_readback_inverts_translation() {
    for term in closed_terms(9) {
        let net = translate(&term).expect("the term is closed");
        assert_eq!(net.check(), Ok(()), "{term}");
        assert_eq!(readback(&net), Ok(term.clone()), "{term}");
    }
}

#[test]
fn small_terms_agree_with_the_reference() {
    with_deep_stack(check_small_terms_agree_with_the_reference);
}

fn check_small_terms_agree_with_the_reference() {
    let mut tally = Tally::default();
    for term in closed_terms(10) {
        tally.compare(&term, REFERENCE_BUDGET);
    }
    tally.report("closed terms up to size 10");
    assert!(
        tally.compared > 9 * tally.skipped,
        "too few terms were compared"
    );
    assert!(tally.shared > 0, "no term exercised sharing");
}

#[test]
fn random_terms_agree_with_the_reference() {
    with_deep_stack(check_random_terms_agree_with_the_reference);
}

fn check_random_terms_agree_with_the_reference() {
    let mut random = Random(0x5EED);
    for redexes in [0, 5, 9] {
        let mut tally = Tally::default();
        for _ in 0..20_000 {
            let size = 10 + random.below(40);
            tally.compare(&random.term(size, 0, redexes), REFERENCE_BUDGET);
        }
        tally.report(&format!("random terms, redex bias {redexes}/10"));
        assert!(
            tally.compared > tally.skipped,
            "too few terms were compared"
        );
        assert!(tally.shared > 0, "no term exercised sharing");
    }
}

#[test]
fn only_beta_changes_the_term() {
    with_deep_stack(check_only_beta_changes_the_term);
}

fn check_only_beta_changes_the_term() {
    for term in closed_terms(8) {
        let expected = reference::normalize(&term, REFERENCE_BUDGET).ok();
        let mut machine = Machine::new(&term).expect("the term is closed");
        let mut current = term.clone();
        for _ in 0..400 {
            let Some(rule) = machine
                .step()
                .unwrap_or_else(|halt| panic!("{term}: {halt}"))
            else {
                break;
            };
            assert_eq!(machine.net().check(), Ok(()), "{term}");
            let next = machine
                .readback()
                .unwrap_or_else(|halt| panic!("{term}: after {rule:?}: {halt}"));
            if rule == Rule::Beta {
                // The step must stay within the reduction of the term.
                if let Some(expected) = &expected {
                    let reduct = reference::normalize(&next, REFERENCE_BUDGET * 10)
                        .unwrap_or_else(|_| panic!("{term}: {next} does not normalize"));
                    assert_eq!(reduct.normal_form, expected.normal_form, "{term}");
                }
            } else {
                assert_eq!(next, current, "{term}: {rule:?} changed the term");
            }
            current = next;
        }
    }
}

#[test]
fn collecting_garbage_changes_nothing() {
    with_deep_stack(check_collecting_garbage_changes_nothing);
}

fn check_collecting_garbage_changes_nothing() {
    let mut random = Random(0xC0FFEE);
    let mut sample: Vec<Term> = closed_terms(8).collect();
    for _ in 0..3_000 {
        let size = 10 + random.below(30);
        sample.push(random.term(size, 0, 5));
    }
    let mut removed = 0;
    for term in sample {
        let mut direct = Machine::new(&term).expect("the term is closed");
        let Ok(expected) = direct.normalize(20_000) else {
            continue;
        };
        // The same reduction, with a collection after every interaction.
        let mut stepped = Machine::new(&term).expect("the term is closed");
        while let Some(rule) = stepped
            .step()
            .unwrap_or_else(|halt| panic!("{term}: {halt}"))
        {
            stepped.collect();
            assert_eq!(stepped.net().check(), Ok(()), "{term}: after {rule:?}");
        }
        assert_eq!(stepped.readback(), Ok(expected), "{term}");
        assert_eq!(stepped.stats().beta, direct.stats().beta, "{term}");
        assert_eq!(
            stepped.stats().interactions(),
            direct.stats().interactions(),
            "{term}"
        );
        removed += stepped.stats().collected;
    }
    println!("collected {removed} nodes");
    assert!(removed > 0, "no term left garbage behind");
}

/// Definitions shared by the corpus, in dependency order.
const PRELUDE: [(&str, &str); 14] = [
    ("id", r"\x. x"),
    ("true", r"\a b. a"),
    ("false", r"\a b. b"),
    ("succ", r"\n f x. f (n f x)"),
    ("plus", r"\m n f x. m f (n f x)"),
    ("times", r"\m n f. m (n f)"),
    ("iszero", r"\n. n (\x. false) true"),
    ("pred", r"\n f x. n (\g h. h (g f)) (\u. x) (\u. u)"),
    ("pair", r"\a b s. s a b"),
    ("fst", r"\p. p true"),
    ("snd", r"\p. p false"),
    ("fix", r"\f. (\x. f (x x)) (\x. f (x x))"),
    ("fact", r"fix (\r n. iszero n 1 (times n (r (pred n))))"),
    (
        "fib",
        r"\n. fst (n (\p. pair (snd p) (plus (fst p) (snd p))) (pair 0 1))",
    ),
];

fn corpus_term(source: &str) -> Term {
    let mut definitions: Vec<(&str, Term)> = Vec::new();
    let parse = |source: &str, definitions: &[(&str, Term)]| {
        let lookup = |name: &str| {
            definitions
                .iter()
                .find(|(defined, _)| *defined == name)
                .map(|(_, term)| term.clone())
        };
        parse_with(source, &lookup).unwrap_or_else(|error| panic!("{source}: {error}"))
    };
    for (name, body) in PRELUDE {
        let term = parse(body, &definitions);
        definitions.push((name, term));
    }
    parse(source, &definitions)
}

#[test]
fn classic_examples_agree_with_the_reference() {
    with_deep_stack(check_classic_examples_agree_with_the_reference);
}

fn check_classic_examples_agree_with_the_reference() {
    let mut tally = Tally::default();
    for source in [
        // From the Lambdascope reference implementation.
        r"3 2 2 id id",
        r"(\g. g (g (\x. x))) (\h. (\f. f (f (\z. z))) (\w. h (w (\y. y))))",
        r"(\x. x (\i. i)) (\y. (\d. d d) (y z))",
        r"(\twice. twice twice inc) (\f x. f (f x))",
        // Sharing under binders, where copying an abstraction copies a redex.
        r"(\f. f (f a)) (\x. (\y. y) x)",
        r"(\x. x x) (\y. (\z. z) y)",
        r"\v. (\f. f (f (f v))) ((\x. \y. x y) (\z. z))",
        // Erasure next to divergence.
        r"(\x. \y. y) ((\x. x x) (\x. x x))",
        r"fst (pair a ((\x. x x) (\x. x x)))",
        // Arithmetic.
        r"2 2 2",
        r"2 2 2 2",
        r"3 3",
        r"plus 2 3",
        r"times 3 4",
        r"pred 5",
        r"iszero 0 a b",
        r"iszero 2 a b",
        r"fib 7",
        // Recursion through a fixed-point combinator.
        r"fact 3",
        r"fact 4",
    ] {
        tally.compare(&corpus_term(source), 50_000_000);
        assert_eq!(tally.skipped, 0, "{source} did not normalize");
    }
    tally.report("classic examples");
}

#[test]
fn optimal_sharing_beats_normal_order() {
    with_deep_stack(check_optimal_sharing_beats_normal_order);
}

fn check_optimal_sharing_beats_normal_order() {
    // Each of the `n` nested applications of `2` doubles the work of normal
    // order, but all the copies it makes fall in the same families.
    let term = corpus_term(r"2 2 2 2 id id");
    let expected = reference::normalize(&term, 50_000_000).expect("the term normalizes");
    let mut machine = Machine::new(&term).expect("the term is closed");
    assert_eq!(machine.normalize(MACHINE_FUEL), Ok(expected.normal_form));
    assert_eq!(machine.stats().beta, expected.families);
    assert!(
        expected.beta_steps > 3 * expected.families,
        "{} steps, {} families",
        expected.beta_steps,
        expected.families
    );
}
