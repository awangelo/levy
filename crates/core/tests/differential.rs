//! Differential tests: the optimal machine against the reference reducer.
//!
//! Four properties are checked, on every closed term up to a small size, on
//! random larger terms with and without free variables, and on a corpus of
//! classic examples:
//!
//! 1. reading back a freshly translated net gives the term back;
//! 2. the machine and the reference reducer agree on the normal form, and the
//!    machine fires exactly one beta interaction per redex family;
//! 3. no rule other than beta changes the term a net stands for;
//! 4. it makes no difference whether a reduction runs in one go, one
//!    interaction at a time, in slices of fuel, or with garbage collected
//!    at every turn.
//!
//! The random terms come from a fixed seed, so a failure can be reproduced.
//! Set `LEVY_TEST_SEED` to a number to try other terms.
//!
//! Nothing here asks for a large stack: the engine does not recurse, and
//! these tests would overflow the stack of a test thread if it did.

use std::collections::BTreeMap;

use levy_core::machine::readback;
use levy_core::net::Kind;
use levy_core::translate::translate;
use levy_core::{Definitions, Halt, Machine, Rule, Term, reference};

/// Budget of the reference reducer, in beta-steps plus copied nodes.
const REFERENCE_BUDGET: u64 = 20_000;
/// Fuel of the machine, in steps of its walk.
const MACHINE_FUEL: u64 = 5_000_000;
/// Fuel of the machine on a term the reference reducer gives up on. Such a
/// term diverges as a rule, so this is what the machine is expected to burn.
const DIVERGENCE_FUEL: u64 = 10_000;

/// The seed of the random terms: fixed, unless the environment gives one.
fn seed(default: u64) -> u64 {
    match std::env::var("LEVY_TEST_SEED") {
        Ok(text) => {
            let given: u64 = text.parse().expect("LEVY_TEST_SEED is a number");
            println!("random terms from LEVY_TEST_SEED={given}");
            given ^ default
        }
        Err(_) => default,
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

/// What the random terms look like.
#[derive(Clone, Copy, Debug)]
struct Shape {
    /// The chance in ten that an application gets an abstraction as its
    /// function, which makes it a redex.
    redexes: usize,
    /// The chance in ten that a variable is a free one.
    free: usize,
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
    /// The top of the term is as likely to be an application as anything
    /// below it is.
    fn term(&mut self, size: usize, depth: usize, shape: Shape) -> Term {
        const FREE: [&str; 3] = ["p", "q", "r"];
        if size <= 1 {
            if self.below(10) < shape.free {
                Term::free(FREE[self.below(FREE.len())])
            } else if depth > 0 {
                Term::Var(self.below(depth))
            } else {
                // A closed term has no variable to put here.
                Term::lam("x", Term::Var(0))
            }
        } else if size == 2 || self.below(5) < 2 {
            self.abstraction(size, depth, shape)
        } else {
            let left = 1 + self.below(size - 2);
            let func = if self.below(10) < shape.redexes {
                self.abstraction(left, depth, shape)
            } else {
                self.term(left, depth, shape)
            };
            Term::app(func, self.term(size - 1 - left, depth, shape))
        }
    }

    fn abstraction(&mut self, size: usize, depth: usize, shape: Shape) -> Term {
        Term::lam("x", self.term(size.saturating_sub(1), depth + 1, shape))
    }
}

/// The interaction a pair of nodes is about to have, as a short name.
fn variant(machine: &Machine) -> Option<String> {
    let name = |kind: Kind| match kind {
        Kind::Root => "root",
        Kind::Lam { .. } => "abstraction",
        Kind::App => "application",
        Kind::Fan { .. } => "fan",
        Kind::Delim { .. } => "delimiter",
        Kind::Eraser => "eraser",
        Kind::Free { .. } => "free variable",
    };
    let redex = machine.next().expect("the net is sound")?;
    let (upper, lower) = (
        machine.net().kind(redex.upper),
        machine.net().kind(redex.lower),
    );
    let mut pair = [name(upper), name(lower)];
    pair.sort_unstable();
    let rule = match (redex.rule, upper, lower) {
        (Rule::Annihilate, Kind::Delim { count: a, .. }, Kind::Delim { count: b, .. })
            if a != b =>
        {
            "annihilate in part".to_owned()
        }
        (rule, ..) => format!("{rule:?}").to_lowercase(),
    };
    Some(format!("{rule}: {} and {}", pair[0], pair[1]))
}

/// Every way two nodes can interact.
const VARIANTS: [&str; 14] = [
    "beta: abstraction and application",
    "annihilate: fan and fan",
    "annihilate: delimiter and delimiter",
    "annihilate in part: delimiter and delimiter",
    "commute: fan and fan",
    "commute: delimiter and fan",
    "commute: delimiter and delimiter",
    "commute: abstraction and fan",
    "commute: application and fan",
    "commute: abstraction and delimiter",
    "commute: application and delimiter",
    "commute: fan and free variable",
    "dissolve: delimiter and free variable",
    "dissolve: delimiter and root",
];

/// Reduces `term` one interaction at a time and checks that nothing but a
/// beta changes the term the net stands for, and that every beta keeps it
/// within the reduction to `normal`, if that is known. Counts the kinds of
/// interaction it sees.
fn check_steps(term: &Term, normal: Option<&Term>, seen: &mut BTreeMap<String, u64>) {
    let mut machine = Machine::new(term).expect("the term has no unbound index");
    let mut current = term.clone();
    for _ in 0..400 {
        let Some(expected) = variant(&machine) else {
            assert_eq!(machine.step(), Ok(None), "{term}");
            break;
        };
        let rule = machine
            .step()
            .unwrap_or_else(|halt| panic!("{term}: {halt}"))
            .unwrap_or_else(|| panic!("{term}: {expected} was announced and nothing fired"));
        assert!(
            expected.starts_with(&format!("{rule:?}").to_lowercase()),
            "{term}: {expected} was announced and {rule:?} fired"
        );
        *seen.entry(expected).or_default() += 1;
        assert_eq!(machine.net().check(), Ok(()), "{term}");
        let next = machine
            .readback()
            .unwrap_or_else(|halt| panic!("{term}: after {rule:?}: {halt}"));
        if rule == Rule::Beta {
            if let Some(normal) = normal {
                let reduct = reference::normalize(&next, REFERENCE_BUDGET * 10)
                    .unwrap_or_else(|_| panic!("{term}: {next} does not normalize"));
                assert_eq!(&reduct.normal_form, normal, "{term}");
            }
        } else {
            assert_eq!(next, current, "{term}: {rule:?} changed the term");
        }
        current = next;
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
    /// Compared terms that took more than five beta interactions.
    long: u64,
    /// Nodes the machine collected as garbage on its way.
    collected: u64,
}

impl Tally {
    /// Runs both reducers on `term` and checks them against each other.
    fn compare(&mut self, term: &Term, budget: u64) {
        let mut machine = Machine::new(term).expect("the term has no unbound index");
        let Ok(expected) = reference::normalize(term, budget) else {
            // The term diverges or explodes under substitution. The machine
            // may still succeed, but whatever it does it must keep the net
            // sound, and its fuel must stop it.
            let outcome = machine.normalize(DIVERGENCE_FUEL);
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
        self.long += u64::from(expected.families > 5);
        self.collected += machine.stats().collected;
    }

    fn report(&self, what: &str) {
        println!(
            "{what}: {} compared, {} skipped, {} normal-order steps, {} optimal steps, \
             sharing helped on {}, {} took more than 5 steps",
            self.compared,
            self.skipped,
            self.normal_order_steps,
            self.optimal_steps,
            self.shared,
            self.long
        );
    }
}

#[test]
fn readback_inverts_translation() {
    for term in closed_terms(9) {
        let net = translate(&term).expect("the term is closed");
        assert_eq!(net.check(), Ok(()), "{term}");
        assert_eq!(readback(&net), Ok(term.clone()), "{term}");
    }
    let mut random = Random(seed(0x0BAC));
    for round in 0..4_000 {
        let shape = Shape {
            redexes: round % 10,
            free: round % 4,
        };
        let size = 10 + random.below(190);
        let term = random.term(size, 0, shape);
        let net = translate(&term).expect("the term has no unbound index");
        assert_eq!(net.check(), Ok(()), "{term}");
        assert_eq!(readback(&net), Ok(term.clone()), "{term}");
    }
}

#[test]
fn small_terms_agree_with_the_reference() {
    let mut tally = Tally::default();
    for term in closed_terms(10) {
        tally.compare(&term, REFERENCE_BUDGET);
    }
    tally.report("closed terms up to size 10");
    assert_eq!(tally.compared + tally.skipped, 10_180);
    // The four that are skipped are the ones that diverge.
    assert!(tally.skipped <= 4, "too few terms were compared");
    assert!(tally.shared >= 5, "too few terms exercised sharing");
}

#[test]
fn random_terms_agree_with_the_reference() {
    let mut random = Random(seed(0x5EED));
    let mut total = Tally::default();
    for redexes in [0, 5, 9] {
        for free in [0, 3] {
            let shape = Shape { redexes, free };
            let mut tally = Tally::default();
            for _ in 0..10_000 {
                let size = 10 + random.below(40);
                tally.compare(&random.term(size, 0, shape), REFERENCE_BUDGET);
            }
            tally.report(&format!("random terms, {shape:?}"));
            assert!(
                tally.compared > 20 * tally.skipped,
                "too few terms were compared"
            );
            total.compared += tally.compared;
            total.shared += tally.shared;
            total.long += tally.long;
        }
    }
    // The terms are worth their while only if they are not all trivial.
    assert!(
        total.shared * 100 > total.compared,
        "too few terms exercised sharing: {} of {}",
        total.shared,
        total.compared
    );
    assert!(
        total.long * 20 > total.compared,
        "too few terms took a while: {} of {}",
        total.long,
        total.compared
    );
}

#[test]
fn large_random_terms_agree_with_the_reference() {
    let mut random = Random(seed(0x1A26E));
    let mut tally = Tally::default();
    for round in 0..3_000 {
        let shape = Shape {
            redexes: [3, 6, 9][round % 3],
            free: [0, 1, 4][round % 3],
        };
        let size = 50 + random.below(150);
        tally.compare(&random.term(size, 0, shape), REFERENCE_BUDGET);
    }
    tally.report("random terms of 50 to 200 nodes");
    assert!(
        tally.compared > 5 * tally.skipped,
        "too few terms were compared"
    );
    assert!(
        tally.long * 2 > tally.compared,
        "too few terms took a while"
    );
}

#[test]
fn only_beta_changes_the_term() {
    let mut seen = BTreeMap::new();
    for term in closed_terms(8) {
        let expected = reference::normalize(&term, REFERENCE_BUDGET).ok();
        check_steps(
            &term,
            expected.as_ref().map(|it| &it.normal_form),
            &mut seen,
        );
    }
    let mut random = Random(seed(0x0B5E));
    for round in 0..1_500 {
        let shape = Shape {
            redexes: [2, 5, 9][round % 3],
            free: [0, 3][round % 2],
        };
        let size = 10 + random.below(50);
        let term = random.term(size, 0, shape);
        let expected = reference::normalize(&term, REFERENCE_BUDGET).ok();
        check_steps(
            &term,
            expected.as_ref().map(|it| &it.normal_form),
            &mut seen,
        );
    }
    for source in [
        r"2 2 2",
        r"plus 2 3",
        r"pred 3",
        r"(\x. x x) (\y. (\z. z) y) w",
        r"fst (pair a ((\x. x x) (\x. x x)))",
        r"(\twice. twice twice inc) (\f x. f (f x))",
    ] {
        let term = corpus_term(source);
        let expected = reference::normalize(&term, REFERENCE_BUDGET * 10).ok();
        check_steps(
            &term,
            expected.as_ref().map(|it| &it.normal_form),
            &mut seen,
        );
    }
    println!("{seen:#?}");
    // Every kind of interaction has been watched, and not just once.
    for variant in VARIANTS {
        let count = seen.get(variant).copied().unwrap_or(0);
        assert!(count >= 20, "`{variant}` fired {count} times");
    }
    assert_eq!(seen.len(), VARIANTS.len(), "an interaction nobody listed");
}

#[test]
fn how_a_reduction_is_driven_makes_no_difference() {
    let mut random = Random(seed(0xD21FE));
    let mut sample: Vec<Term> = closed_terms(7).collect();
    for round in 0..800 {
        let shape = Shape {
            redexes: [2, 5, 9][round % 3],
            free: [0, 3][round % 2],
        };
        let size = 10 + random.below(60);
        sample.push(random.term(size, 0, shape));
    }
    sample.extend(["fact 3", "fib 7", "2 2 2 2 id id", "pred 5"].map(corpus_term));
    let mut finished = 0;
    for term in sample {
        let machine = || Machine::new(&term).expect("the term has no unbound index");
        let mut direct = machine();
        let outcome = direct.normalize(200_000);

        // One interaction at a time.
        let mut stepped = machine();
        let mut steps = 0;
        while steps < direct.stats().interactions() && stepped.step().unwrap().is_some() {
            steps += 1;
        }
        assert_eq!(stepped.stats(), direct.stats(), "{term}");
        if outcome.is_ok() {
            assert_eq!(stepped.step(), Ok(None), "{term}");
            assert_eq!(stepped.readback(), outcome, "{term}");
        }

        // In batches of uneven size, some of which stop at a beta.
        let mut batched = machine();
        while batched.stats().interactions() < direct.stats().interactions() {
            let left = direct.stats().interactions() - batched.stats().interactions();
            let batch = 1 + random.below(40) as u64;
            let fired = batched.advance(batch.min(left), random.below(3) == 0);
            assert!(fired.unwrap().is_some(), "{term}");
        }
        assert_eq!(batched.stats(), direct.stats(), "{term}");

        let Ok(normal) = outcome else {
            continue;
        };
        finished += 1;
        assert_eq!(batched.readback().as_ref(), Ok(&normal), "{term}");

        // In slices of fuel, each taking up the walk where the last stopped.
        let mut sliced = machine();
        let slice = 1 + random.below(60) as u64;
        let resumed = loop {
            match sliced.normalize(slice) {
                Err(Halt::OutOfFuel) => {}
                outcome => break outcome,
            }
        };
        assert_eq!(resumed.as_ref(), Ok(&normal), "{term}: slices of {slice}");
        assert_eq!(sliced.stats(), direct.stats(), "{term}: slices of {slice}");

        // With a collection after every interaction.
        let mut collected = machine();
        while let Some(rule) = collected.step().unwrap() {
            collected.collect();
            assert_eq!(collected.net().check(), Ok(()), "{term}: after {rule:?}");
        }
        assert_eq!(collected.readback().as_ref(), Ok(&normal), "{term}");
        // Once the run in one go has collected what it left lying about,
        // even the count of what was collected is the same.
        direct.collect();
        assert_eq!(collected.stats(), direct.stats(), "{term}");
    }
    assert!(finished > 800, "only {finished} terms have a normal form");
}

#[test]
fn collecting_garbage_changes_nothing() {
    let mut random = Random(seed(0xC0FFEE));
    let mut sample: Vec<Term> = closed_terms(8).collect();
    for _ in 0..3_000 {
        let size = 10 + random.below(30);
        let shape = Shape {
            redexes: 5,
            free: 0,
        };
        sample.push(random.term(size, 0, shape));
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
        direct.collect();
        assert_eq!(stepped.stats(), direct.stats(), "{term}");
        removed += stepped.stats().collected;
    }
    println!("collected {removed} nodes");
    assert!(removed > 0, "no term left garbage behind");
}

/// The definitions of `examples/prelude.lam`, which the corpus is written
/// with. Loading the file itself keeps it tested.
fn prelude() -> Definitions {
    let mut definitions = Definitions::new();
    let terms = definitions.load(include_str!("../../../examples/prelude.lam"));
    assert_eq!(terms, Ok(Vec::new()), "the prelude only defines");
    for (name, term) in definitions.iter() {
        assert!(
            term.free_names().is_empty(),
            "prelude: `{name}` has free variables"
        );
    }
    definitions
}

fn corpus_term(source: &str) -> Term {
    prelude()
        .parse(source)
        .unwrap_or_else(|error| panic!("{source}: {error}"))
}

#[test]
fn classic_examples_agree_with_the_reference() {
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
        r"power 2 5",
        r"power 3 0",
        r"minus 5 3",
        r"pred 5",
        r"iszero 0 a b",
        r"iszero 2 a b",
        r"and true (not false) a b",
        r"or false false a b",
        r"leq 2 5 a b",
        r"eq 3 3 a b",
        r"eq 3 4 a b",
        r"lt 4 4 a b",
        r"gt 5 2 a b",
        r"neq 3 4 a b",
        r"compose succ (const 2) 7",
        r"fib 7",
        r"fib 12",
        // Recursion through a fixed-point combinator.
        r"fact 3",
        r"fact 4",
    ] {
        tally.compare(&corpus_term(source), 50_000_000);
        assert_eq!(tally.skipped, 0, "{source} did not normalize");
    }
    tally.report("classic examples");
    // Some of these are large enough for the machine to collect garbage in
    // the middle of its walk, which the small terms never make it do.
    assert!(tally.collected > 0, "no garbage was collected on the way");
}

#[test]
fn divergence_costs_no_more_than_the_fuel() {
    // Terms without a normal form whose result, as far as it gets, takes an
    // ever longer way to read. The fuel must bound the walk as well as the
    // interactions, or these run until memory is gone.
    for source in [
        r"fix f",
        r"fix succ",
        r"\x. (\a. a a) (\a. (\b. x) (\b. a) (a a))",
        r"fix (\self n. plus n (self (pred n))) 3",
        r"(\x. x x x) (\x. x x x)",
    ] {
        let mut machine = Machine::new(&corpus_term(source)).unwrap();
        assert_eq!(machine.normalize(200_000), Err(Halt::OutOfFuel), "{source}");
        assert_eq!(machine.net().check(), Ok(()), "{source}");
    }
}

#[test]
fn optimal_sharing_beats_normal_order() {
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
