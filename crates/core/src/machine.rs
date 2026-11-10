//! The reduction machine.
//!
//! The machine walks the net from the root the way one reads a term: down
//! through abstractions, along the function side of applications to the head,
//! then through the arguments from left to right. Whenever the walk crosses a
//! wire between two principal ports it rewrites that pair and resumes from
//! just above it. Nothing else is ever rewritten.
//!
//! This order is leftmost-outermost, so only needed redexes are contracted,
//! and the net shares everything a redex family has in common, so each family
//! is contracted once. Together that makes the number of beta interactions
//! optimal in Lévy's sense.
//!
//! The same walk, with rewriting turned off, reads the net back as a term at
//! any point of the reduction.

use std::fmt;

use crate::context::Context;
use crate::net::{Kind, Net, NodeId, Port, Symbol, slot};
use crate::rules::{self, Rule};
use crate::term::Term;
use crate::translate::{UnboundIndex, translate};

/// How many times each rule has fired.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    pub beta: u64,
    pub annihilations: u64,
    pub commutations: u64,
    pub dissolutions: u64,
}

impl Stats {
    /// All interactions, of any rule.
    pub fn interactions(&self) -> u64 {
        self.beta + self.bookkeeping()
    }

    /// Interactions that only move sharing and scopes around.
    pub fn bookkeeping(&self) -> u64 {
        self.annihilations + self.commutations + self.dissolutions
    }

    fn record(&mut self, rule: Rule) {
        match rule {
            Rule::Beta => self.beta += 1,
            Rule::Annihilate => self.annihilations += 1,
            Rule::Commute => self.commutations += 1,
            Rule::Dissolve => self.dissolutions += 1,
        }
    }
}

/// Why a walk stopped before producing a term.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Halt {
    /// The interaction allowance ran out. The machine can be resumed.
    OutOfFuel,
    /// The net does not represent a term. This points at a bug in the rules.
    Malformed(&'static str),
}

impl fmt::Display for Halt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Halt::OutOfFuel => f.write_str("ran out of fuel"),
            Halt::Malformed(reason) => write!(f, "malformed net: {reason}"),
        }
    }
}

impl std::error::Error for Halt {}

/// A net under reduction.
#[derive(Clone, Debug)]
pub struct Machine {
    net: Net,
    stats: Stats,
}

impl Machine {
    /// Loads a term into a fresh machine.
    pub fn new(term: &Term) -> Result<Machine, UnboundIndex> {
        Ok(Machine {
            net: translate(term)?,
            stats: Stats::default(),
        })
    }

    pub fn net(&self) -> &Net {
        &self.net
    }

    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// Reduces to normal form and returns it, firing at most `fuel`
    /// interactions.
    pub fn normalize(&mut self, fuel: u64) -> Result<Term, Halt> {
        let mut reduce = Reduce {
            machine: self,
            fuel,
            last: None,
        };
        walk(&mut reduce)
    }

    /// Fires the next interaction of the reduction and reports its rule, or
    /// returns `None` if the net is in normal form.
    pub fn step(&mut self) -> Result<Option<Rule>, Halt> {
        let mut reduce = Reduce {
            machine: self,
            fuel: 1,
            last: None,
        };
        match walk(&mut reduce) {
            Ok(_) | Err(Halt::OutOfFuel) => Ok(reduce.last),
            Err(halt) => Err(halt),
        }
    }

    /// The term the net stands for right now.
    pub fn readback(&self) -> Result<Term, Halt> {
        readback(&self.net)
    }
}

/// Reads a net as a term without rewriting anything.
pub fn readback(net: &Net) -> Result<Term, Halt> {
    walk(&mut Observe(net))
}

/// What a walk does with the active pairs it comes across.
trait Policy {
    fn net(&self) -> &Net;

    /// Rewrites the pair if it interacts and this policy reduces. Reports
    /// whether the net changed.
    fn fire(&mut self, upper: NodeId, lower: NodeId) -> Result<bool, Halt>;
}

/// Leaves the net alone.
struct Observe<'a>(&'a Net);

impl Policy for Observe<'_> {
    fn net(&self) -> &Net {
        self.0
    }

    fn fire(&mut self, _upper: NodeId, _lower: NodeId) -> Result<bool, Halt> {
        Ok(false)
    }
}

/// Rewrites every active pair on the way, while the fuel lasts.
struct Reduce<'a> {
    machine: &'a mut Machine,
    fuel: u64,
    last: Option<Rule>,
}

impl Policy for Reduce<'_> {
    fn net(&self) -> &Net {
        &self.machine.net
    }

    fn fire(&mut self, upper: NodeId, lower: NodeId) -> Result<bool, Halt> {
        let net = &mut self.machine.net;
        if rules::rule_for(net.kind(upper), net.kind(lower)).is_none() {
            return Ok(false);
        }
        self.fuel = self.fuel.checked_sub(1).ok_or(Halt::OutOfFuel)?;
        if let Some(rule) = rules::apply(net, upper, lower) {
            self.machine.stats.record(rule);
            self.last = Some(rule);
        }
        Ok(true)
    }
}

fn walk(policy: &mut impl Policy) -> Result<Term, Halt> {
    let root = policy.net().root().principal();
    let mut walker = Walker {
        policy,
        binders: Vec::new(),
    };
    walker.term(root, Context::default())
}

/// A point on the way down: the port the walk leaves a node by, and the
/// context it carries from there.
struct Frame {
    exit: Port,
    context: Context,
}

/// What the walk finds at the head of a term.
enum Head {
    Lam(NodeId, Symbol),
    Bound(NodeId),
    Free(Symbol),
}

struct Walker<'a, P> {
    policy: &'a mut P,
    /// The abstractions around the current position, innermost last.
    binders: Vec<NodeId>,
}

impl<P: Policy> Walker<'_, P> {
    /// Reads the term hanging from `from`.
    fn term(&mut self, from: Port, context: Context) -> Result<Term, Halt> {
        // The frames passed on the way to the head, the starting one first.
        let mut passed: Vec<Frame> = Vec::new();
        let mut top = Frame {
            exit: from,
            context,
        };
        let head = loop {
            let entry = self.policy.net().peer(top.exit);
            if top.exit.is_principal()
                && entry.is_principal()
                && self.policy.fire(top.exit.node, entry.node)?
            {
                // The node of the top frame is gone. Whatever replaced it
                // hangs from the frame before, so resume there. The starting
                // frame is only ever the root, which survives.
                if let Some(previous) = passed.pop() {
                    top = previous;
                }
                continue;
            }
            let node = entry.node;
            let context = &top.context;
            let next = match (self.policy.net().kind(node), entry.slot) {
                (Kind::Lam { name }, slot::PRINCIPAL) => break Head::Lam(node, name),
                (Kind::Lam { .. }, slot::VAR) => break Head::Bound(node),
                (Kind::Free { name }, _) => break Head::Free(name),
                (Kind::App, slot::RESULT) => Frame {
                    exit: node.principal(),
                    context: context.clone(),
                },
                (Kind::Fan { level }, slot::PRINCIPAL) => {
                    let (branch, context) = context
                        .recall_branch(level)
                        .ok_or(Halt::Malformed("a fan is entered with no branch on record"))?;
                    Frame {
                        exit: node.port(branch),
                        context,
                    }
                }
                (Kind::Fan { level }, branch) => Frame {
                    exit: node.principal(),
                    context: context.take_branch(level, branch),
                },
                (Kind::Delim { level }, slot::PRINCIPAL) => Frame {
                    exit: node.port(slot::INSIDE),
                    context: context.enter_scope(level),
                },
                (Kind::Delim { level }, _) => Frame {
                    exit: node.principal(),
                    context: context.leave_scope(level),
                },
                (Kind::Lam { .. }, _) => {
                    return Err(Halt::Malformed("an abstraction is entered from its body"));
                }
                (Kind::App, _) => {
                    return Err(Halt::Malformed("an application is entered from below"));
                }
                (Kind::Eraser, _) => return Err(Halt::Malformed("the walk ran into an eraser")),
                (Kind::Root, _) => return Err(Halt::Malformed("the walk came back to the root")),
            };
            passed.push(std::mem::replace(&mut top, next));
        };

        let mut term = match head {
            Head::Lam(node, name) => {
                let name = self.policy.net().name(name).to_owned();
                self.binders.push(node);
                let body = self.term(node.port(slot::BODY), top.context.enter_abstraction())?;
                self.binders.pop();
                Term::lam(name, body)
            }
            Head::Bound(node) => {
                let index = self
                    .binders
                    .iter()
                    .rev()
                    .position(|&binder| binder == node)
                    .ok_or(Halt::Malformed("a variable occurs outside its binder"))?;
                Term::Var(index)
            }
            Head::Free(name) => Term::free(self.policy.net().name(name)),
        };

        // Unwind: every application passed on the way takes its argument.
        passed.push(top);
        for frame in passed.into_iter().skip(1).rev() {
            let node = frame.exit.node;
            if frame.exit.is_principal() && self.policy.net().kind(node) == Kind::App {
                let arg = self.term(node.port(slot::ARG), frame.context)?;
                term = Term::app(term, arg);
            }
        }
        Ok(term)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    fn machine(source: &str) -> Machine {
        Machine::new(&parse(source).unwrap()).unwrap()
    }

    fn normal_form(source: &str) -> Term {
        let mut machine = machine(source);
        let term = machine.normalize(1_000_000).unwrap();
        assert_eq!(machine.net().check(), Ok(()), "{source}");
        term
    }

    #[test]
    fn readback_inverts_translation() {
        for source in [
            r"\x. x",
            r"\x. \y. x",
            r"\x. x x",
            r"\f x. f (f (f x))",
            r"(\x. x x) (\x. x x)",
            r"\x. \y. \z. x z (y z)",
            r"\a. (\x. \y. x y a) (\z. z a) b",
            r"f (\x. g x y) y",
        ] {
            let term = parse(source).unwrap();
            assert_eq!(machine(source).readback(), Ok(term), "{source}");
        }
    }

    #[test]
    fn reduces_simple_redexes() {
        assert_eq!(normal_form(r"(\x. x) y"), Term::free("y"));
        assert_eq!(normal_form(r"(\x. \y. x) a b"), Term::free("a"));
        assert_eq!(normal_form(r"(\x. \y. y) a b"), Term::free("b"));
        assert_eq!(normal_form(r"(\x. x x) (\y. y)"), parse(r"\y. y").unwrap());
    }

    #[test]
    fn reduces_under_binders() {
        assert_eq!(normal_form(r"\a. (\x. x) a"), parse(r"\a. a").unwrap());
        assert_eq!(
            normal_form(r"\a. \b. (\x. \y. x y) (a b)"),
            parse(r"\a. \b. \y. a b y").unwrap()
        );
    }

    #[test]
    fn church_arithmetic() {
        assert_eq!(normal_form("2 2").as_church(), Some(4));
        assert_eq!(normal_form("2 3").as_church(), Some(9));
        assert_eq!(normal_form("3 2").as_church(), Some(8));
        assert_eq!(normal_form("2 2 2").as_church(), Some(16));
        let plus = r"(\m n f x. m f (n f x))";
        let times = r"(\m n f. m (n f))";
        assert_eq!(normal_form(&format!("{plus} 3 4")).as_church(), Some(7));
        assert_eq!(normal_form(&format!("{times} 3 4")).as_church(), Some(12));
    }

    #[test]
    fn unneeded_arguments_are_never_reduced() {
        let mut machine = machine(r"(\x. y) ((\x. x x) (\x. x x))");
        assert_eq!(machine.normalize(1_000), Ok(Term::free("y")));
        assert_eq!(machine.stats().beta, 1);
    }

    #[test]
    fn a_shared_redex_is_contracted_once() {
        let mut machine = machine(r"(\x. f x x) ((\y. y) a)");
        let expected = parse("f a a").unwrap();
        assert_eq!(machine.normalize(1_000), Ok(expected));
        assert_eq!(machine.stats().beta, 2);
    }

    #[test]
    fn divergence_runs_out_of_fuel_and_can_resume() {
        let mut machine = machine(r"(\x. x x) (\x. x x)");
        assert_eq!(machine.normalize(500), Err(Halt::OutOfFuel));
        assert_eq!(machine.stats().interactions(), 500);
        assert_eq!(machine.normalize(500), Err(Halt::OutOfFuel));
        assert_eq!(machine.stats().interactions(), 1_000);
        assert_eq!(machine.net().check(), Ok(()));
    }

    #[test]
    fn stepping_reaches_the_same_normal_form() {
        let source = r"(\f. f (f (\x. x))) (\g. g (\y. y))";
        let mut stepped = machine(source);
        let mut steps = 0;
        while stepped.step().unwrap().is_some() {
            steps += 1;
        }
        let mut direct = machine(source);
        let expected = direct.normalize(1_000_000).unwrap();
        assert_eq!(stepped.readback(), Ok(expected));
        assert_eq!(stepped.stats(), direct.stats());
        assert_eq!(steps, direct.stats().interactions());
    }
}
