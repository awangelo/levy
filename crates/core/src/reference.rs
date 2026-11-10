//! Reference reducer: plain normal-order β-reduction on Lévy-labelled terms.
//!
//! This is the yardstick the optimal machine is measured against. It works by
//! substitution, copies arguments freely, and reports three things: the normal
//! form, the number of β-steps it took, and the number of redex *families* it
//! contracted. The last one is the number of β-steps an optimal reducer needs.
//!
//! Families are found with Lévy's labelled λ-calculus. Every subterm carries a
//! label, and contracting `((λx. M)^a N)^b` yields `b·⌈a⌉·M[x := ⌊a⌋·N]`: the
//! label `a` of the abstraction is the *degree* of the redex, and two redexes
//! belong to the same family exactly when their degrees are equal. Labels grow
//! exponentially, so they are kept as fingerprints: a pair of polynomial
//! hashes that is cheap to concatenate. Two different labels sharing a
//! fingerprint is possible in principle and negligible in practice.

use std::collections::HashSet;
use std::rc::Rc;

use crate::term::Term;

/// What the reference reducer found.
#[derive(Clone, Debug)]
pub struct Outcome {
    pub normal_form: Term,
    /// β-steps taken by normal-order reduction.
    pub beta_steps: u64,
    /// Distinct redex families contracted along the way.
    pub families: u64,
}

/// The reducer gave up before reaching a normal form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BudgetExhausted;

impl std::fmt::Display for BudgetExhausted {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("the reference reducer ran out of budget")
    }
}

impl std::error::Error for BudgetExhausted {}

/// Reduces `term` to normal form in normal order.
///
/// `budget` bounds the work: each β-step costs one unit, and so does each
/// node copied by a substitution.
pub fn normalize(term: &Term, budget: u64) -> Result<Outcome, BudgetExhausted> {
    let mut reducer = Reducer {
        budget,
        beta_steps: 0,
        degrees: HashSet::new(),
    };
    let mut next_atom = 0;
    let labelled = Labelled::from_term(term, &mut next_atom);
    let normal = reducer.normalize(labelled)?;
    Ok(Outcome {
        normal_form: normal.into_term(),
        beta_steps: reducer.beta_steps,
        families: reducer.degrees.len() as u64,
    })
}

const MODULUS: u64 = (1 << 61) - 1;
const BASES: [u64; 2] = [0x1B03_7387_12FA_D5C9, 0x0A2F_5C4D_8E91_B3A7];
const SALTS: [u64; 2] = [0x6A09_E667_F3BC_C908, 0xBB67_AE85_84CA_A73B];

fn mul_mod(a: u64, b: u64) -> u64 {
    let product = u128::from(a) * u128::from(b) % u128::from(MODULUS);
    u64::try_from(product).expect("a value reduced modulo a 61-bit prime fits in 64 bits")
}

/// The finalizer of the SplitMix64 generator, used to scatter bits.
fn mix(value: u64) -> u64 {
    let value = value.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let value = (value ^ (value >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    let value = (value ^ (value >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    value ^ (value >> 31)
}

/// The fingerprint of a Lévy label, seen as a word over an alphabet of atoms
/// and of overlined and underlined sub-labels.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Label {
    /// Polynomial hashes of the word, one per base.
    digest: [u64; 2],
    /// Each base raised to the length of the word.
    weight: [u64; 2],
}

impl Label {
    /// A one-letter word.
    fn letter(code: u64) -> Label {
        Label {
            digest: SALTS.map(|salt| 1 + mix(code ^ salt) % (MODULUS - 1)),
            weight: BASES,
        }
    }

    fn atom(index: u64) -> Label {
        Label::letter(mix(index))
    }

    /// The concatenation of `self` and `next`.
    fn then(self, next: Label) -> Label {
        let mut result = self;
        for k in 0..2 {
            result.digest[k] = (mul_mod(self.digest[k], next.weight[k]) + next.digest[k]) % MODULUS;
            result.weight[k] = mul_mod(self.weight[k], next.weight[k]);
        }
        result
    }

    /// Wraps the whole word into a single letter.
    fn sealed(self, tag: u64) -> Label {
        let parts = [
            self.digest[0],
            self.digest[1],
            self.weight[0],
            self.weight[1],
        ];
        Label::letter(parts.iter().fold(mix(tag), |acc, &part| mix(acc ^ part)))
    }

    fn overlined(self) -> Label {
        self.sealed(1)
    }

    fn underlined(self) -> Label {
        self.sealed(2)
    }
}

struct Labelled {
    label: Label,
    shape: Shape,
}

enum Shape {
    Var(usize),
    Free(Rc<str>),
    Lam(Rc<str>, Box<Labelled>),
    App(Box<Labelled>, Box<Labelled>),
}

impl Labelled {
    fn from_term(term: &Term, next_atom: &mut u64) -> Labelled {
        let label = Label::atom(*next_atom);
        *next_atom += 1;
        let shape = match term {
            Term::Var(index) => Shape::Var(*index),
            Term::Free(name) => Shape::Free(name.as_str().into()),
            Term::Lam(name, body) => Shape::Lam(
                name.as_str().into(),
                Box::new(Labelled::from_term(body, next_atom)),
            ),
            Term::App(func, arg) => Shape::App(
                Box::new(Labelled::from_term(func, next_atom)),
                Box::new(Labelled::from_term(arg, next_atom)),
            ),
        };
        Labelled { label, shape }
    }

    fn into_term(self) -> Term {
        match self.shape {
            Shape::Var(index) => Term::Var(index),
            Shape::Free(name) => Term::Free(name.as_ref().to_owned()),
            Shape::Lam(name, body) => Term::lam(name.as_ref(), body.into_term()),
            Shape::App(func, arg) => Term::app(func.into_term(), arg.into_term()),
        }
    }
}

struct Reducer {
    budget: u64,
    beta_steps: u64,
    degrees: HashSet<Label>,
}

impl Reducer {
    fn spend(&mut self) -> Result<(), BudgetExhausted> {
        self.budget = self.budget.checked_sub(1).ok_or(BudgetExhausted)?;
        Ok(())
    }

    fn normalize(&mut self, term: Labelled) -> Result<Labelled, BudgetExhausted> {
        let Labelled { label, shape } = self.head_normalize(term)?;
        let shape = match shape {
            Shape::Lam(name, body) => Shape::Lam(name, Box::new(self.normalize(*body)?)),
            Shape::App(func, arg) => {
                let func = self.normalize(*func)?;
                let arg = self.normalize(*arg)?;
                Shape::App(Box::new(func), Box::new(arg))
            }
            leaf => leaf,
        };
        Ok(Labelled { label, shape })
    }

    /// Contracts head redexes until the term is an abstraction or is stuck on
    /// a variable.
    fn head_normalize(&mut self, term: Labelled) -> Result<Labelled, BudgetExhausted> {
        // The applications above the head, outermost first, each as its label
        // and its argument.
        let mut spine: Vec<(Label, Box<Labelled>)> = Vec::new();
        let mut head = term;
        loop {
            head = match head.shape {
                Shape::App(func, arg) => {
                    spine.push((head.label, arg));
                    *func
                }
                Shape::Lam(name, body) => {
                    let Some((label, arg)) = spine.pop() else {
                        head.shape = Shape::Lam(name, body);
                        break;
                    };
                    self.spend()?;
                    self.beta_steps += 1;
                    self.degrees.insert(head.label);
                    let mut result = self.substitute(*body, 0, &arg, head.label.underlined())?;
                    result.label = label.then(head.label.overlined()).then(result.label);
                    result
                }
                leaf => {
                    head.shape = leaf;
                    break;
                }
            };
        }
        Ok(spine
            .into_iter()
            .rev()
            .fold(head, |func, (label, arg)| Labelled {
                label,
                shape: Shape::App(Box::new(func), arg),
            }))
    }

    /// Replaces the variable bound `depth` binders up by `arg`, whose label
    /// gets `mark` in front at every occurrence.
    fn substitute(
        &mut self,
        target: Labelled,
        depth: usize,
        arg: &Labelled,
        mark: Label,
    ) -> Result<Labelled, BudgetExhausted> {
        let Labelled { label, shape } = target;
        let shape = match shape {
            Shape::Var(index) if index == depth => {
                let copy = self.lifted(arg, depth, 0)?;
                return Ok(Labelled {
                    label: label.then(mark).then(copy.label),
                    shape: copy.shape,
                });
            }
            Shape::Var(index) if index > depth => Shape::Var(index - 1),
            Shape::Lam(name, body) => Shape::Lam(
                name,
                Box::new(self.substitute(*body, depth + 1, arg, mark)?),
            ),
            Shape::App(func, operand) => {
                let func = self.substitute(*func, depth, arg, mark)?;
                let operand = self.substitute(*operand, depth, arg, mark)?;
                Shape::App(Box::new(func), Box::new(operand))
            }
            leaf => leaf,
        };
        Ok(Labelled { label, shape })
    }

    /// Copies `term`, raising by `by` the variables that point `cutoff` or
    /// more binders up.
    fn lifted(
        &mut self,
        term: &Labelled,
        by: usize,
        cutoff: usize,
    ) -> Result<Labelled, BudgetExhausted> {
        self.spend()?;
        let shape = match &term.shape {
            Shape::Var(index) if *index >= cutoff => Shape::Var(index + by),
            Shape::Var(index) => Shape::Var(*index),
            Shape::Free(name) => Shape::Free(name.clone()),
            Shape::Lam(name, body) => {
                Shape::Lam(name.clone(), Box::new(self.lifted(body, by, cutoff + 1)?))
            }
            Shape::App(func, arg) => Shape::App(
                Box::new(self.lifted(func, by, cutoff)?),
                Box::new(self.lifted(arg, by, cutoff)?),
            ),
        };
        Ok(Labelled {
            label: term.label,
            shape,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    fn run(source: &str) -> Outcome {
        normalize(&parse(source).unwrap(), 1_000_000).unwrap()
    }

    #[test]
    fn concatenation_is_associative() {
        let [a, b, c] = [0, 1, 2].map(Label::atom);
        assert_eq!(a.then(b).then(c), a.then(b.then(c)));
        assert_ne!(a.then(b), b.then(a));
        assert_ne!(a.overlined(), a.underlined());
        assert_ne!(a.then(b).overlined(), a.overlined().then(b.overlined()));
    }

    #[test]
    fn reduces_in_normal_order() {
        assert_eq!(run(r"(\x. x) y").normal_form, Term::free("y"));
        assert_eq!(run(r"(\x. \y. x) a b").normal_form, Term::free("a"));
        // The argument diverges but is never needed.
        let outcome = run(r"(\x. y) ((\x. x x) (\x. x x))");
        assert_eq!(outcome.normal_form, Term::free("y"));
        assert_eq!(outcome.beta_steps, 1);
    }

    #[test]
    fn substitution_shifts_under_binders() {
        let outcome = run(r"\a. (\x. \y. x) a");
        assert_eq!(outcome.normal_form, parse(r"\a. \y. a").unwrap());
        let outcome = run(r"\a. \b. (\x. \y. x y) (a b)");
        assert_eq!(outcome.normal_form, parse(r"\a. \b. \y. a b y").unwrap());
    }

    #[test]
    fn church_arithmetic() {
        assert_eq!(run("2 2").normal_form.as_church(), Some(4));
        assert_eq!(run("3 2").normal_form.as_church(), Some(8));
        assert_eq!(run("2 2 2").normal_form.as_church(), Some(16));
        let plus = r"(\m n f x. m f (n f x))";
        assert_eq!(run(&format!("{plus} 3 4")).normal_form.as_church(), Some(7));
    }

    #[test]
    fn copies_of_a_redex_form_one_family() {
        // The redex `I a` is copied by the outer step, so normal order
        // contracts it twice, but both copies belong to one family.
        let outcome = run(r"(\x. f x x) ((\y. y) a)");
        assert_eq!(outcome.beta_steps, 3);
        assert_eq!(outcome.families, 2);
    }

    #[test]
    fn independent_redexes_are_separate_families() {
        let outcome = run(r"f ((\x. x) a) ((\x. x) a)");
        assert_eq!(outcome.beta_steps, 2);
        assert_eq!(outcome.families, 2);
    }

    #[test]
    fn gives_up_on_divergence() {
        let omega = parse(r"(\x. x x) (\x. x x)").unwrap();
        assert_eq!(normalize(&omega, 1_000).unwrap_err(), BudgetExhausted);
    }
}
