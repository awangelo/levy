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
//! Delimiters that pile up on the way are merged into one node as the walk
//! passes them, which is what keeps the bookkeeping within bounds.
//!
//! The same walk, with rewriting turned off, reads the net back as a term at
//! any point of the reduction.

use std::fmt;

use crate::context::{Context, Mark};
use crate::gc;
use crate::net::{Kind, Net, NodeId, Port, Symbol, slot};
use crate::rules::{self, Rule};
use crate::term::Term;
use crate::translate::{UnboundIndex, translate};

/// How many times each rule has fired.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Beta interactions: the steps that count for optimality.
    pub beta: u64,
    /// Pairs of fans or delimiters that cancelled each other.
    pub annihilations: u64,
    /// Pairs that passed through each other.
    pub commutations: u64,
    /// Delimiters that vanished at the root or at a free variable.
    pub dissolutions: u64,
    /// Nodes removed as garbage.
    pub collected: u64,
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
    /// The allowance of work ran out. The machine can be resumed.
    OutOfFuel,
    /// The caller asked the walk to stop. The machine can be resumed.
    Interrupted,
    /// The net does not represent a term. This points at a bug in the rules.
    Malformed(&'static str),
}

impl fmt::Display for Halt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Halt::OutOfFuel => f.write_str("ran out of fuel"),
            Halt::Interrupted => f.write_str("interrupted"),
            Halt::Malformed(reason) => write!(f, "malformed net: {reason}"),
        }
    }
}

impl std::error::Error for Halt {}

/// An active pair the reduction is about to rewrite.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Redex {
    /// The node the walk comes from.
    pub upper: NodeId,
    /// The node the walk runs into.
    pub lower: NodeId,
    /// The rule that will rewrite the pair.
    pub rule: Rule,
}

/// The net is collected once it has grown by this factor since last time.
const GROWTH_BEFORE_COLLECTION: usize = 4;
/// Nets smaller than this are not worth collecting.
const SMALLEST_COLLECTION: usize = 4_096;

/// A net under reduction.
#[derive(Clone, Debug)]
pub struct Machine {
    net: Net,
    stats: Stats,
    /// The size at which `normalize` collects garbage next.
    collect_at: usize,
    /// How far the reduction has got.
    progress: Progress,
}

/// How far a reduction has got.
#[derive(Clone, Debug)]
enum Progress {
    /// No walk is under way: the next one starts at the root.
    Idle,
    /// A walk stopped half way, to be taken up again.
    Suspended(Suspended),
    /// A walk has read the whole term and found nothing left to rewrite.
    /// Nothing changes the net from here on, so this is for good.
    Normal,
}

impl Machine {
    /// Loads a term into a fresh machine.
    pub fn new(term: &Term) -> Result<Machine, UnboundIndex> {
        Ok(Machine {
            net: translate(term)?,
            stats: Stats::default(),
            collect_at: SMALLEST_COLLECTION,
            progress: Progress::Idle,
        })
    }

    /// What a copy of the machine costs, in places for nodes: those of the
    /// net, and the context of a walk under way counted in the same unit.
    pub fn slots(&self) -> usize {
        let walk = match &self.progress {
            Progress::Suspended(state) => state.context.bytes().div_ceil(Net::SLOT_BYTES),
            Progress::Idle | Progress::Normal => 0,
        };
        self.net.slots() + walk
    }

    /// The net as it stands.
    pub fn net(&self) -> &Net {
        &self.net
    }

    /// How many times each rule has fired so far.
    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// Reduces to normal form and returns it.
    ///
    /// `fuel` bounds the work, and with it the time and the memory the call
    /// takes: every node of the net the walk comes to costs one unit, whether
    /// it is rewritten there or only passed. A normal form of `n` nodes
    /// therefore needs at least `n` units. When the fuel runs out the call
    /// returns [`Halt::OutOfFuel`], and a later call takes up the reduction
    /// where this one stopped.
    pub fn normalize(&mut self, fuel: u64) -> Result<Term, Halt> {
        self.normalize_unless(fuel, &|| false)
    }

    /// Like [`normalize`](Machine::normalize), but asks `interrupted` every
    /// thousand units or so whether to give up, and returns
    /// [`Halt::Interrupted`] once it says yes.
    pub fn normalize_unless(
        &mut self,
        fuel: u64,
        interrupted: &dyn Fn() -> bool,
    ) -> Result<Term, Halt> {
        if matches!(self.progress, Progress::Normal) {
            // There is nothing left to rewrite, only the result to read.
            let state = Suspended::at_root(&self.net);
            let mut walker = Walker {
                policy: &mut Observe(&self.net),
                state,
                fuel,
                interrupted: Some(interrupted),
            };
            return walker.term();
        }
        self.reduce(u64::MAX, false, fuel, Some(interrupted)).0
    }

    /// Fires the next interaction of the reduction and reports its rule, or
    /// returns `None` if the net is in normal form.
    pub fn step(&mut self) -> Result<Option<Rule>, Halt> {
        self.advance(1, false)
    }

    /// Fires up to `interactions` interactions, and with `until_beta` stops
    /// after the first beta among them. Reports the rule fired last, or
    /// `None` if the net was in normal form already.
    ///
    /// The walk stops in front of the next pair and goes on from there in
    /// the next call, so stepping costs no more than running.
    pub fn advance(&mut self, interactions: u64, until_beta: bool) -> Result<Option<Rule>, Halt> {
        if matches!(self.progress, Progress::Normal) {
            return Ok(None);
        }
        match self.reduce(interactions, until_beta, u64::MAX, None) {
            (Ok(_) | Err(Halt::OutOfFuel), last) => Ok(last),
            (Err(halt), _) => Err(halt),
        }
    }

    /// Takes up the walk where it stopped, or starts one at the root, and
    /// rewrites what it comes across within the limits given. Returns what
    /// became of the walk, and the rule fired last.
    fn reduce(
        &mut self,
        interactions: u64,
        until_beta: bool,
        fuel: u64,
        interrupted: Option<&dyn Fn() -> bool>,
    ) -> (Result<Term, Halt>, Option<Rule>) {
        let state = match std::mem::replace(&mut self.progress, Progress::Idle) {
            Progress::Suspended(state) => state,
            Progress::Idle | Progress::Normal => Suspended::at_root(&self.net),
        };
        let mut reduce = Reduce {
            machine: self,
            interactions,
            until_beta,
            last: None,
        };
        let mut walker = Walker {
            policy: &mut reduce,
            state,
            fuel,
            interrupted,
        };
        let outcome = walker.term();
        let state = walker.state;
        let last = reduce.last;
        // A walk that only ran out of allowance stands in front of a node it
        // has not looked at yet, and nothing but the walk itself changes the
        // net in the meantime, so it can go on from there.
        self.progress = match outcome {
            Err(Halt::OutOfFuel | Halt::Interrupted) => Progress::Suspended(state),
            Ok(_) => Progress::Normal,
            Err(Halt::Malformed(_)) => Progress::Idle,
        };
        (outcome, last)
    }

    /// The active pair that `step` would rewrite, or `None` if the net is in
    /// normal form.
    pub fn next(&self) -> Result<Option<Redex>, Halt> {
        if matches!(self.progress, Progress::Normal) {
            return Ok(None);
        }
        // A walk that stopped for want of allowance stands in front of the
        // very pair it would have rewritten next.
        if let Progress::Suspended(Suspended { top, .. }) = &self.progress {
            let (upper, lower) = (*top, self.net.peer(*top));
            if upper.is_principal()
                && lower.is_principal()
                && let Some(rule) =
                    rules::rule_for(self.net.kind(upper.node), self.net.kind(lower.node))
            {
                return Ok(Some(Redex {
                    upper: upper.node,
                    lower: lower.node,
                    rule,
                }));
            }
        }
        let mut scout = Scout {
            net: &self.net,
            found: None,
        };
        match read(&mut scout, u64::MAX) {
            Ok(_) | Err(Halt::OutOfFuel) => Ok(scout.found),
            Err(halt) => Err(halt),
        }
    }

    /// The term the net stands for right now.
    ///
    /// A small net can stand for a huge term. Use
    /// [`readback_within`](Machine::readback_within) to bound the work.
    pub fn readback(&self) -> Result<Term, Halt> {
        readback(&self.net)
    }

    /// The term the net stands for right now, or `None` if reading it takes
    /// more than `fuel` units of work, counted as in
    /// [`normalize`](Machine::normalize).
    pub fn readback_within(&self, fuel: u64) -> Result<Option<Term>, Halt> {
        match read(&mut Observe(&self.net), fuel) {
            Ok(term) => Ok(Some(term)),
            Err(Halt::OutOfFuel) => Ok(None),
            Err(halt) => Err(halt),
        }
    }

    /// Removes the nodes the result no longer depends on and returns how
    /// many there were.
    pub fn collect(&mut self) -> usize {
        let removed = gc::collect(&mut self.net);
        self.stats.collected += removed as u64;
        self.collect_at = (self.net.len() * GROWTH_BEFORE_COLLECTION).max(SMALLEST_COLLECTION);
        removed
    }
}

/// Reads a net as a term without rewriting anything.
pub fn readback(net: &Net) -> Result<Term, Halt> {
    read(&mut Observe(net), u64::MAX)
}

/// What a walk does with the active pairs it comes across.
trait Policy {
    fn net(&self) -> &Net;

    /// Rewrites the pair if it interacts and this policy reduces. Reports
    /// whether the net changed.
    fn fire(&mut self, upper: NodeId, lower: NodeId) -> Result<bool, Halt>;

    /// Merges into the delimiter at `exit` the one stacked on it, if there is
    /// one and this policy reduces. Returns the level and the height of what
    /// was merged in.
    fn merge(&mut self, _exit: Port) -> Option<(u32, u32)> {
        None
    }
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

/// Rewrites nothing, and stops at the first pair that could be rewritten: a
/// reducer with no allowance that remembers what it wanted to rewrite.
struct Scout<'a> {
    net: &'a Net,
    found: Option<Redex>,
}

impl Policy for Scout<'_> {
    fn net(&self) -> &Net {
        self.net
    }

    fn fire(&mut self, upper: NodeId, lower: NodeId) -> Result<bool, Halt> {
        match rules::rule_for(self.net.kind(upper), self.net.kind(lower)) {
            Some(rule) => {
                self.found = Some(Redex { upper, lower, rule });
                Err(Halt::OutOfFuel)
            }
            None => Ok(false),
        }
    }
}

/// Rewrites every active pair on the way, while its allowance lasts.
struct Reduce<'a> {
    machine: &'a mut Machine,
    /// How many more interactions may fire.
    interactions: u64,
    /// Whether to fire nothing more once a beta has fired.
    until_beta: bool,
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
        // The walk stops at the pair it may not rewrite, not right after the
        // last one it did: the delimiters in between are merged by then, so
        // the next walk finds the net as `next` describes it.
        self.interactions = self.interactions.checked_sub(1).ok_or(Halt::OutOfFuel)?;
        if let Some(rule) = rules::apply(net, upper, lower) {
            self.machine.stats.record(rule);
            self.last = Some(rule);
            if self.until_beta && rule == Rule::Beta {
                self.interactions = 0;
            }
        }
        // Everything the walk holds on to is reachable from the root, so
        // collecting in the middle of it is safe.
        if self.machine.net.len() >= self.machine.collect_at {
            self.machine.collect();
        }
        Ok(true)
    }

    fn merge(&mut self, exit: Port) -> Option<(u32, u32)> {
        rules::merge(&mut self.machine.net, exit)
    }
}

/// Reads the term a net stands for from the root, spending at most `fuel`.
fn read(policy: &mut impl Policy, fuel: u64) -> Result<Term, Halt> {
    let state = Suspended::at_root(policy.net());
    let mut walker = Walker {
        policy,
        state,
        fuel,
        interrupted: None,
    };
    walker.term()
}

/// A point passed on the way down: the port the walk left a node by, and the
/// mark of the context it carried from there.
#[derive(Clone, Copy, Debug)]
struct Frame {
    exit: Port,
    mark: Mark,
}

/// What the walk finds at the head of a term.
enum Head {
    Lam(NodeId, Symbol),
    Bound(NodeId),
    Free(Symbol),
}

/// What is left to do once the term being read is complete.
#[derive(Clone, Debug)]
enum Pending {
    /// Read the argument of this application, in the context of this mark,
    /// and apply the term to it.
    Argument(NodeId, Mark),
    /// The term is the body of an abstraction of this name: close it.
    Body(String),
    /// The term is an argument: apply this function to it.
    Function(Term),
}

/// Where a walk is, and all it needs to go on from there.
#[derive(Clone, Debug)]
struct Suspended {
    /// The abstractions around the current position, outermost first.
    binders: Vec<NodeId>,
    /// The frames passed on the way to the head being looked for, the
    /// starting one first.
    passed: Vec<Frame>,
    /// The port the walk goes on from.
    top: Port,
    /// The context it carries from there.
    context: Context,
    /// What waits for the term being read, the innermost last.
    pending: Vec<Pending>,
    /// How many of `pending` are arguments, which need their marks kept.
    arguments: usize,
}

impl Suspended {
    /// A walk that has not left the root yet.
    fn at_root(net: &Net) -> Suspended {
        Suspended {
            binders: Vec::new(),
            passed: Vec::new(),
            top: net.root().principal(),
            context: Context::default(),
            pending: Vec::new(),
            arguments: 0,
        }
    }
}

/// How often, in units of fuel, a walk asks whether it was interrupted.
const INTERRUPT_CHECK: u64 = 1 << 10;

/// Reads the term a net stands for, letting its policy rewrite on the way.
struct Walker<'a, P> {
    policy: &'a mut P,
    state: Suspended,
    /// How many more nodes the walk may come to.
    fuel: u64,
    /// Asked now and then whether to give up.
    interrupted: Option<&'a dyn Fn() -> bool>,
}

impl<P: Policy> Walker<'_, P> {
    /// Reads the term from where the walk stands.
    ///
    /// The term can be nested deeper than any call stack, so what is left to
    /// do is kept in a list, not in recursive calls. That list is also what
    /// lets a walk that ran out of fuel be taken up again: an error leaves
    /// the state in front of the node it stopped at.
    fn term(&mut self) -> Result<Term, Halt> {
        loop {
            let head = self.head()?;
            let state = &mut self.state;
            let mut term = match head {
                Head::Lam(node, name) => {
                    let name = self.policy.net().name(name).to_owned();
                    state.pending.push(Pending::Body(name));
                    state.top = node.port(slot::BODY);
                    state.context.enter_abstraction(state.binders.len());
                    state.binders.push(node);
                    continue;
                }
                Head::Bound(node) => {
                    // A shared abstraction can occur inside a copy of itself,
                    // so the node alone does not say which copy binds the
                    // variable. The scope the walk is in does.
                    let binder = state
                        .context
                        .binder()
                        .filter(|&binder| state.binders.get(binder) == Some(&node))
                        .ok_or(Halt::Malformed("a variable occurs outside its binder"))?;
                    Term::Var(state.binders.len() - 1 - binder)
                }
                Head::Free(name) => Term::free(self.policy.net().name(name)),
            };
            // The term is complete: hand it to whatever waits for it, until
            // something needs another term read first.
            loop {
                match state.pending.pop() {
                    None => return Ok(term),
                    Some(Pending::Argument(app, mark)) => {
                        state.context.restore(mark);
                        state.arguments -= 1;
                        if state.arguments == 0 {
                            // No earlier context will be needed again.
                            state.context.forget();
                        }
                        state.pending.push(Pending::Function(term));
                        state.top = app.port(slot::ARG);
                        break;
                    }
                    Some(Pending::Body(name)) => {
                        state.binders.pop();
                        term = Term::lam(name, term);
                    }
                    Some(Pending::Function(func)) => term = Term::app(func, term),
                }
            }
        }
    }

    /// Goes down from the top frame to the head of the term there, rewriting
    /// the active pairs on the way if the policy does. Returns the head,
    /// leaves the context as it is there, and adds the applications passed
    /// to what is pending, the outermost first.
    fn head(&mut self) -> Result<Head, Halt> {
        let head = loop {
            self.spend()?;
            let state = &mut self.state;
            let top = state.top;
            let entry = self.policy.net().peer(top);
            if top.is_principal()
                && entry.is_principal()
                && self.policy.fire(top.node, entry.node)?
            {
                // The node of the top frame is gone. Whatever replaced it
                // hangs from the frame before, so resume there. The starting
                // frame is only ever the root, which survives.
                if let Some(previous) = state.passed.pop() {
                    state.top = previous.exit;
                    state.context.restore(previous.mark);
                }
                continue;
            }
            if let Some((level, height)) = self.policy.merge(top) {
                // The delimiter of the top frame took in the one stacked on
                // it, and the walk has now passed that one's scopes as well.
                if top.is_principal() {
                    state.context.leave_scopes(level, height);
                } else {
                    state.context.enter_scopes(level, height);
                }
                continue;
            }
            let node = entry.node;
            let mark = state.context.mark();
            let context = &mut state.context;
            let next = match (self.policy.net().kind(node), entry.slot) {
                (Kind::Lam { name }, slot::PRINCIPAL) => break Head::Lam(node, name),
                (Kind::Lam { .. }, slot::VAR) => break Head::Bound(node),
                (Kind::Free { name }, _) => break Head::Free(name),
                (Kind::App, slot::RESULT) => node.principal(),
                (Kind::Fan { level }, slot::PRINCIPAL) => {
                    let branch = context
                        .recall_branch(level)
                        .ok_or(Halt::Malformed("a fan is entered with no branch on record"))?;
                    node.port(branch)
                }
                (Kind::Fan { level }, branch) => {
                    context.take_branch(level, branch);
                    node.principal()
                }
                (Kind::Delim { level, count }, slot::PRINCIPAL) => {
                    context.enter_scopes(level, count);
                    node.port(slot::INSIDE)
                }
                (Kind::Delim { level, count }, _) => {
                    context.leave_scopes(level, count);
                    node.principal()
                }
                (Kind::Lam { .. }, _) => {
                    return Err(Halt::Malformed("an abstraction is entered from its body"));
                }
                (Kind::App, _) => {
                    return Err(Halt::Malformed("an application is entered from below"));
                }
                (Kind::Eraser, _) => return Err(Halt::Malformed("the walk ran into an eraser")),
                (Kind::Root, _) => return Err(Halt::Malformed("the walk came back to the root")),
            };
            state.passed.push(Frame { exit: top, mark });
            state.top = next;
        };
        // Nothing on this stretch will be rewritten any more, so only the
        // applications are still of interest: each takes an argument once
        // the head is done.
        let state = &mut self.state;
        let net = self.policy.net();
        let top = Frame {
            exit: state.top,
            mark: state.context.mark(),
        };
        for Frame { exit, mark } in state.passed.drain(..).chain([top]) {
            if exit.is_principal() && net.kind(exit.node) == Kind::App {
                state.pending.push(Pending::Argument(exit.node, mark));
                state.arguments += 1;
            }
        }
        if state.arguments == 0 {
            // No earlier context will be needed again.
            state.context.forget();
        }
        Ok(head)
    }

    /// Pays for one node the walk comes to.
    fn spend(&mut self) -> Result<(), Halt> {
        self.fuel = self.fuel.checked_sub(1).ok_or(Halt::OutOfFuel)?;
        if self.fuel.is_multiple_of(INTERRUPT_CHECK)
            && let Some(interrupted) = self.interrupted
            && interrupted()
        {
            return Err(Halt::Interrupted);
        }
        Ok(())
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
    fn a_shared_abstraction_can_occur_inside_itself() {
        // `g` is applied to a copy of the abstraction it lives in, so the
        // node for `λy` ends up nested inside itself, once per copy. Each
        // variable must find the copy that binds it.
        assert_eq!(
            normal_form(r"\x. (\f. f f) (\g. x (\y. g y))"),
            parse(r"\x. x (\y. x (\z. y z))").unwrap()
        );
    }

    #[test]
    fn divergence_runs_out_of_fuel_and_can_resume() {
        let mut machine = machine(r"(\x. x x) (\x. x x)");
        assert_eq!(machine.normalize(500), Err(Halt::OutOfFuel));
        let first = machine.stats().interactions();
        assert!(first > 100 && first <= 500, "{first}");
        assert_eq!(machine.normalize(500), Err(Halt::OutOfFuel));
        assert!(machine.stats().interactions() > first);
        assert_eq!(machine.net().check(), Ok(()));
    }

    #[test]
    fn fuel_bounds_the_reading_of_an_endless_result() {
        // `fix f` unfolds to `f (f (f ...))`. Every unfolding takes a handful
        // of interactions but a longer and longer way to reach, so it is the
        // walk that has to be bounded, not the interactions alone.
        let mut machine = machine(r"(\x. f (x x)) (\x. f (x x))");
        assert_eq!(machine.normalize(2_000_000), Err(Halt::OutOfFuel));
        assert!(machine.stats().interactions() < 100_000);
    }

    #[test]
    fn fuel_bounds_the_size_of_the_result() {
        // Four nested doublings: 4 beta-steps, and a result of 61 nodes.
        let source = r"(\x. f x x) ((\x. f x x) ((\x. f x x) ((\x. f x x) a)))";
        assert_eq!(machine(source).normalize(60), Err(Halt::OutOfFuel));
        assert_eq!(machine(source).normalize(1_000).unwrap().size(), 61);
    }

    #[test]
    fn deep_results_need_no_deep_stack() {
        // A numeral of 65,536 nested applications, read, compared, measured
        // and dropped on the small stack of a test thread.
        let mut machine = machine("2 2 2 2");
        let term = machine.normalize(10_000_000).unwrap();
        assert_eq!(term.as_church(), Some(65_536));
        assert_eq!(term, Term::church(65_536));
        assert_eq!(term.size(), 2 * 65_536 + 3);
    }

    #[test]
    fn an_interrupted_walk_stops_and_can_resume() {
        let mut machine = machine("2 2 2 2");
        assert_eq!(
            machine.normalize_unless(10_000_000, &|| true),
            Err(Halt::Interrupted)
        );
        assert_eq!(machine.net().check(), Ok(()));
        let term = machine.normalize(10_000_000).unwrap();
        assert_eq!(term.as_church(), Some(65_536));
    }

    #[test]
    fn advancing_stops_after_a_beta() {
        let source = r"(\f. f (f (\x. x))) (\g. g (\y. y))";
        let mut direct = machine(source);
        let expected = direct.normalize(1_000_000).unwrap();
        let mut stepped = machine(source);
        let mut betas = 0;
        while let Some(rule) = stepped.advance(u64::MAX, true).unwrap() {
            // Only the last stretch, to the normal form, may end without one.
            if rule == Rule::Beta {
                betas += 1;
                assert_eq!(stepped.stats().beta, betas);
            }
        }
        assert_eq!(stepped.stats(), direct.stats());
        assert_eq!(stepped.readback(), Ok(expected));
        // A limit on the interactions is kept as well.
        let mut limited = machine(source);
        assert!(limited.advance(3, false).unwrap().is_some());
        assert_eq!(limited.stats().interactions(), 3);
    }

    #[test]
    fn a_finished_reduction_is_not_read_again_to_find_that_out() {
        let mut machine = machine("2 2 2 2");
        let term = machine.normalize(10_000_000).unwrap();
        let stats = machine.stats();
        // None of these walks the 131,075 nodes of the result again.
        for _ in 0..100_000 {
            assert_eq!(machine.step(), Ok(None));
            assert_eq!(machine.next(), Ok(None));
        }
        assert_eq!(machine.advance(u64::MAX, true), Ok(None));
        assert_eq!(machine.stats(), stats);
        // The result is still there for the asking, within the fuel given.
        assert_eq!(machine.normalize(10), Err(Halt::OutOfFuel));
        assert_eq!(machine.normalize(10_000_000), Ok(term));
        machine.collect();
        assert_eq!(machine.next(), Ok(None));
    }

    #[test]
    fn reading_back_can_be_bounded() {
        let machine = machine(r"\f x. f (f (f x))");
        assert_eq!(machine.readback_within(3), Ok(None));
        assert_eq!(machine.readback_within(100), Ok(Some(Term::church(3))));
    }

    #[test]
    fn next_names_the_pair_that_step_rewrites() {
        let mut machine = machine(r"(\x. x) y");
        let redex = machine.next().unwrap().expect("the term has a redex");
        assert_eq!(redex.rule, Rule::Beta);
        assert_eq!(machine.net().kind(redex.upper), Kind::App);
        assert!(matches!(machine.net().kind(redex.lower), Kind::Lam { .. }));
        assert_eq!(machine.step(), Ok(Some(Rule::Beta)));
        while let Some(redex) = machine.next().unwrap() {
            assert_eq!(machine.step(), Ok(Some(redex.rule)));
        }
        assert_eq!(machine.step(), Ok(None));
        assert_eq!(machine.readback(), Ok(Term::free("y")));
    }

    #[test]
    fn large_garbage_is_collected_along_the_way() {
        // The discarded argument is big enough to trigger a collection.
        let mut machine = machine(r"(\x. y) 3000");
        assert_eq!(machine.normalize(10), Ok(Term::free("y")));
        assert!(machine.stats().collected > 6_000);
        assert_eq!(machine.net().len(), 2);
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
