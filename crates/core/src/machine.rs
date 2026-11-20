//! The reduction machine.
//!
//! The machine reduces a net with the walk that reads it back: from the root
//! the way one reads a term, down through abstractions, along the function
//! side of applications to the head, then through the arguments from left to
//! right. Whenever the walk crosses a wire between two principal ports, the
//! machine rewrites that pair, and the walk resumes from just above it.
//! Nothing else is ever rewritten.
//!
//! This order is leftmost-outermost, so only needed redexes are contracted,
//! and the net shares everything a redex family has in common, so each family
//! is contracted once. Together that makes the number of beta interactions
//! optimal in Lévy's sense.
//!
//! Delimiters that pile up on the way are merged into one node as the walk
//! passes them, which is what keeps the bookkeeping within bounds.

use std::fmt;

use crate::gc;
use crate::net::{Net, NodeId, Port};
use crate::rules::{self, Rule};
use crate::term::Term;
use crate::translate::{UnboundIndex, translate};
use crate::walk::{self, Policy, Stop, Suspended, Walker};

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
    /// Nodes removed as garbage. The erasers that a collection plugs the
    /// ports it cut with are not counted when a later one removes them, as
    /// their number depends on when collections ran, so the net can shrink
    /// by more than this grows.
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
    /// The fuel that reducing has spent.
    spent: u64,
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
    /// A walk stopped half way, to be taken up again. Boxed, as it is many
    /// times the size of the other states.
    Suspended(Box<Suspended>),
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
            spent: 0,
            collect_at: SMALLEST_COLLECTION,
            progress: Progress::Idle,
        })
    }

    /// Roughly the bytes a copy of the machine takes: its net, and the walk
    /// under way if there is one, without the terms that walk has read.
    pub fn bytes(&self) -> usize {
        let walk = match &self.progress {
            Progress::Suspended(state) => state.bytes(),
            Progress::Idle | Progress::Normal => 0,
        };
        self.net.bytes() + walk
    }

    /// The net as it stands.
    pub fn net(&self) -> &Net {
        &self.net
    }

    /// How many times each rule has fired so far.
    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// The fuel that reducing has spent so far, over all the calls that
    /// reduced. With it, several calls can share one allowance. A walk pays
    /// for each node once, however many calls it is taken up in, so a
    /// reduction driven one interaction at a time spends what one call to
    /// [`normalize`](Machine::normalize) does.
    pub fn spent(&self) -> u64 {
        self.spent
    }

    /// Whether a walk has read the whole term and found nothing left to
    /// rewrite.
    pub fn is_normal(&self) -> bool {
        matches!(self.progress, Progress::Normal)
    }

    /// Reduces to normal form and returns it.
    ///
    /// `fuel` bounds the work: every node of the net the walk comes to costs
    /// one unit, whether it is rewritten there or only passed. A normal form
    /// of `n` nodes therefore needs at least `n` units. A unit stands for
    /// about the same time and memory everywhere but where scopes nest
    /// deeply: passing a stack of delimiters closes or opens a scope for each
    /// delimiter in it, and closing or opening a scope moves the scopes
    /// inside it. When the fuel runs out the call returns
    /// [`Halt::OutOfFuel`], and a later call takes up the reduction where
    /// this one stopped.
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
        if self.is_normal() {
            // There is nothing left to rewrite, only the result to read.
            return walk::read(&self.net, fuel, interrupted);
        }
        let (outcome, _) = self.reduce(u64::MAX, false, fuel, None, interrupted);
        outcome.map_err(Stop::halt)
    }

    /// Fires the next interaction and reports its rule, or returns `None` if
    /// the net is in normal form.
    ///
    /// Nothing bounds the walk from that interaction to the next, which can
    /// be as long as the term the net stands for is large. Use
    /// [`advance`](Machine::advance) to bound it.
    pub fn step(&mut self) -> Result<Option<Rule>, Halt> {
        self.advance(1, false, u64::MAX)
    }

    /// Fires up to `interactions` interactions, and with `until_beta` stops
    /// after the first beta among them. Reports the rule fired last, or
    /// `None` if none fired: the net was in normal form already, or no
    /// interaction was allowed.
    ///
    /// After an interaction the walk goes on to the pair that comes next and
    /// stops in front of it, so stepping costs no more than running, and
    /// [`next`](Machine::next) names that pair. Allowed no interactions, the
    /// call does only that.
    ///
    /// `fuel` is what one interaction may spend, counted as for
    /// [`normalize`](Machine::normalize): on the way to its pair, on the
    /// pair, and on the way to the pair after. A call that allows one
    /// interaction is bounded by it as a whole. One that allows more does
    /// what as many calls that allow one would do, up to the first whose
    /// walk stops short of the next pair, so where the walk stands after an
    /// interaction does not depend on how many were asked for at once. If
    /// the fuel runs out before anything has fired, the call returns
    /// [`Halt::OutOfFuel`], and a later call goes on from there.
    pub fn advance(
        &mut self,
        interactions: u64,
        until_beta: bool,
        fuel: u64,
    ) -> Result<Option<Rule>, Halt> {
        self.advance_unless(interactions, until_beta, fuel, &|| false)
    }

    /// Like [`advance`](Machine::advance), but asks `interrupted` every
    /// thousand units or so whether to give up. Once it says yes, the call
    /// returns [`Halt::Interrupted`] if nothing has fired yet, and otherwise
    /// the rule fired last, leaving the next call to stop at once.
    pub fn advance_unless(
        &mut self,
        interactions: u64,
        until_beta: bool,
        fuel: u64,
        interrupted: &dyn Fn() -> bool,
    ) -> Result<Option<Rule>, Halt> {
        if self.is_normal() {
            return Ok(None);
        }
        // An interaction with a call to itself pays for its pair out of the
        // fuel of that call and goes on with the rest. In a call it shares,
        // the walk has paid for the pair by the time it fires.
        let refill = Some(fuel.saturating_sub(1));
        match self.reduce(interactions, until_beta, fuel, refill, interrupted) {
            (Ok(_) | Err(Stop::Paused), last) => Ok(last),
            // What fired is reported, and the walk is left on its way to the
            // next pair, for a later call to take up.
            (Err(Stop::Halt(Halt::OutOfFuel | Halt::Interrupted)), last @ Some(_)) => Ok(last),
            (Err(Stop::Halt(halt)), _) => Err(halt),
        }
    }

    /// Takes up the walk where it stopped, or starts one at the root, and
    /// rewrites what it comes across within the limits given. `refill` is
    /// the fuel the walk has after each rewrite but its first, if it is not
    /// to make do with `fuel`. Returns what became of the walk, and the rule
    /// fired last.
    fn reduce(
        &mut self,
        interactions: u64,
        until_beta: bool,
        fuel: u64,
        refill: Option<u64>,
        interrupted: &dyn Fn() -> bool,
    ) -> (Result<Term, Stop>, Option<Rule>) {
        let state = match std::mem::replace(&mut self.progress, Progress::Idle) {
            Progress::Suspended(state) => *state,
            Progress::Idle | Progress::Normal => Suspended::at_root(&self.net),
        };
        let mut reduce = Reduce {
            machine: self,
            interactions,
            until_beta,
            last: None,
        };
        let mut walker = Walker::new(&mut reduce, state, fuel, refill, interrupted);
        let outcome = walker.term();
        let (state, spent) = walker.finish();
        let last = reduce.last;
        self.spent += spent;
        // A walk that stopped short of the end stands in front of a node it
        // has not looked at yet, and nothing but the walk itself changes the
        // net in the meantime, so it can go on from there.
        self.progress = match outcome {
            Ok(_) => Progress::Normal,
            Err(Stop::Halt(Halt::Malformed(_))) => Progress::Idle,
            Err(_) => Progress::Suspended(Box::new(state)),
        };
        (outcome, last)
    }

    /// The active pair the reduction stands in front of: the one its next
    /// interaction rewrites.
    ///
    /// `None` once the net is in normal form, and also while that pair is
    /// still to be found: before the first call that reduces, and after one
    /// whose fuel ran out on the way there. [`is_normal`](Machine::is_normal)
    /// tells the two apart, and [`advance`](Machine::advance) finds the pair,
    /// even when it is allowed no interactions.
    pub fn next(&self) -> Option<Redex> {
        let Progress::Suspended(state) = &self.progress else {
            return None;
        };
        let (upper, lower) = (state.top(), self.net.peer(state.top()));
        if !(upper.is_principal() && lower.is_principal()) {
            return None;
        }
        let rule = rules::rule_for(self.net.kind(upper.node), self.net.kind(lower.node))?;
        Some(Redex {
            upper: upper.node,
            lower: lower.node,
            rule,
        })
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
        match walk::read(&self.net, fuel, &|| false) {
            Ok(term) => Ok(Some(term)),
            Err(Halt::OutOfFuel) => Ok(None),
            Err(halt) => Err(halt),
        }
    }

    /// Removes the nodes the result no longer depends on and returns how
    /// many there were, as [`gc::collect`] counts them.
    pub fn collect(&mut self) -> usize {
        let removed = gc::collect(&mut self.net);
        self.stats.collected += removed as u64;
        self.collect_at = (self.net.len() * GROWTH_BEFORE_COLLECTION).max(SMALLEST_COLLECTION);
        removed
    }
}

/// Reads a net as a term without rewriting anything.
pub fn readback(net: &Net) -> Result<Term, Halt> {
    walk::read(net, u64::MAX, &|| false)
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

    fn fire(&mut self, upper: NodeId, lower: NodeId) -> Result<bool, Stop> {
        let net = &mut self.machine.net;
        let Some(rule) = rules::rule_for(net.kind(upper), net.kind(lower)) else {
            return Ok(false);
        };
        // The walk stops at the pair it may not rewrite, not right after the
        // last one it did: the delimiters in between are merged by then, so
        // the next walk finds the net as `next` describes it.
        self.interactions = self.interactions.checked_sub(1).ok_or(Stop::Paused)?;
        rules::rewrite(net, rule, upper, lower);
        self.machine.stats.record(rule);
        self.last = Some(rule);
        if self.until_beta && rule == Rule::Beta {
            self.interactions = 0;
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

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;
    use crate::net::Kind;
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
        while let Some(rule) = stepped.advance(u64::MAX, true, u64::MAX).unwrap() {
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
        assert!(limited.advance(3, false, u64::MAX).unwrap().is_some());
        assert_eq!(limited.stats().interactions(), 3);
    }

    #[test]
    fn fuel_bounds_the_walk_from_one_interaction_to_the_next() {
        // Forty doublings: a net of a few hundred nodes for a term of 2^41.
        // Before long nothing is left to rewrite, but only reading the whole
        // term would tell.
        let mut machine = machine(r"40 (\x. f x x) a");
        let mut calls = 0;
        let halt = loop {
            calls += 1;
            match machine.advance(1, false, 10_000) {
                Ok(Some(_)) => assert_eq!(machine.stats().interactions(), calls),
                other => break other,
            }
        };
        // The call that fired nothing says that its fuel is gone.
        assert_eq!(halt, Err(Halt::OutOfFuel));
        assert_eq!(machine.stats().beta, 42);
        assert!(machine.next().is_none() && !machine.is_normal());
        assert!(machine.spent() <= calls * 10_000, "{}", machine.spent());
        // The walk goes on from where it stopped, as far as it is let.
        let spent = machine.spent();
        assert_eq!(machine.advance(1, false, 500), Err(Halt::OutOfFuel));
        assert_eq!(machine.spent(), spent + 500);
        assert_eq!(machine.net().check(), Ok(()));
    }

    #[test]
    fn a_batch_leaves_the_machine_where_single_interactions_do() {
        // The net, the walk and the fuel spent.
        let state = |machine: &Machine| {
            let net = &machine.net;
            let nodes: Vec<_> = net
                .nodes()
                .map(|(id, kind)| (id, kind, net.serial(id)))
                .collect();
            let wires: Vec<_> = net.wires().collect();
            format!(
                "{nodes:?} {wires:?} {:?} {}",
                machine.progress, machine.spent
            )
        };
        for (source, fuel) in [
            (r"40 (\x. f x x) a", 10_000),
            (r"(\f. f (f (\x. x))) (\g. g (\y. y))", u64::MAX),
            (r"2 2 2 2", 1_000),
        ] {
            let mut single = machine(source);
            let mut batched = machine(source);
            for batch in [1, 2, 3, 5, 8, 13, 400, 100_000, 7] {
                let fired = batched.advance(batch, false, fuel);
                let mut singly = || {
                    let mut last = None;
                    for done in 0..batch {
                        // One call does not send on a walk that it saw stop
                        // short of the next pair.
                        if done > 0 && single.next().is_none() {
                            break;
                        }
                        match single.advance(1, false, fuel)? {
                            Some(rule) => last = Some(rule),
                            None => break,
                        }
                    }
                    Ok(last)
                };
                assert_eq!(fired, singly(), "{source}: a batch of {batch}");
                assert_eq!(batched.stats(), single.stats(), "{source}: {batch}");
                assert_eq!(state(&batched), state(&single), "{source}: {batch}");
            }
        }
    }

    #[test]
    fn one_interaction_at_a_time_spends_what_running_does() {
        for source in [
            r"(\x. x x) (\x. x) ((\y. y) (\z. z)) w",
            r"(\f. f (f (\x. x))) (\g. g (\y. y))",
            r"2 2 2 2",
        ] {
            let mut direct = machine(source);
            let expected = direct.normalize(u64::MAX).unwrap();
            let mut stepped = machine(source);
            while stepped.step().unwrap().is_some() {}
            assert_eq!(stepped.spent(), direct.spent(), "{source}");
            // Exactly that much is enough, one interaction at a time too.
            let mut budgeted = machine(source);
            let fuel = direct.spent();
            loop {
                let left = fuel - budgeted.spent();
                if budgeted.advance(1, false, left).unwrap().is_none() {
                    break;
                }
            }
            assert!(budgeted.is_normal(), "{source}");
            assert_eq!(budgeted.spent(), fuel, "{source}");
            assert_eq!(budgeted.readback(), Ok(expected), "{source}");
        }
    }

    #[test]
    fn an_interrupt_is_seen_however_the_fuel_is_refilled() {
        // Each interaction of this term walks a few nodes, after which a
        // refill puts the fuel back to one short of a multiple of the
        // interval between two looks at the interrupt.
        let mut machine = machine(r"(\x. x x) (\x. x x)");
        let fuel = 10 * crate::INTERRUPT_CHECK - 1;
        let interrupted = || true;
        let (outcome, _) = machine.reduce(100_000, false, fuel, Some(fuel), &interrupted);
        assert_eq!(outcome, Err(Stop::Halt(Halt::Interrupted)));
        assert!(machine.stats().interactions() < crate::INTERRUPT_CHECK);
        assert_eq!(machine.net().check(), Ok(()));
    }

    #[test]
    fn an_interrupt_after_an_interaction_stops_the_next_call() {
        let mut machine = machine("2 2 2 2");
        // Asked at the start of the call, and then a thousand units in, by
        // when interactions have fired.
        let asked = Cell::new(0);
        let late = || {
            asked.set(asked.get() + 1);
            asked.get() > 1
        };
        let fired = machine.advance_unless(u64::MAX, false, u64::MAX, &late);
        assert!(fired.unwrap().is_some());
        assert_eq!(asked.get(), 2);
        let stats = machine.stats();
        // The next call stops before it fires anything.
        assert_eq!(
            machine.advance_unless(1, false, u64::MAX, &|| true),
            Err(Halt::Interrupted)
        );
        assert_eq!(machine.stats(), stats);
        // Nothing is lost.
        let term = machine.normalize(10_000_000).unwrap();
        assert_eq!(term.as_church(), Some(65_536));
    }

    #[test]
    fn fuel_that_runs_out_after_an_interaction_stops_the_walk_short() {
        let source = r"(\f. f (f (\x. x))) (\g. g (\y. y))";
        let mut direct = machine(source);
        let expected = direct.normalize(1_000_000).unwrap();
        // Too little fuel to get from one pair to the next in one call.
        let mut starved = machine(source);
        let (mut fired, mut short) = (0, 0);
        loop {
            match starved.advance(1, false, 2) {
                Ok(Some(_)) => {
                    fired += 1;
                    short += u64::from(starved.next().is_none() && !starved.is_normal());
                }
                Ok(None) => break,
                Err(halt) => assert_eq!(halt, Halt::OutOfFuel),
            }
        }
        assert!(short > 0, "no call stopped short of the next pair");
        assert_eq!(fired, direct.stats().interactions());
        assert_eq!(starved.stats(), direct.stats());
        assert_eq!(starved.readback(), Ok(expected));
    }

    #[test]
    fn a_finished_reduction_is_not_read_again_to_find_that_out() {
        let mut machine = machine("2 2 2 2");
        let term = machine.normalize(10_000_000).unwrap();
        let stats = machine.stats();
        // None of these walks the 131,075 nodes of the result again.
        for _ in 0..100_000 {
            assert_eq!(machine.step(), Ok(None));
            assert_eq!(machine.next(), None);
        }
        assert!(machine.is_normal());
        assert_eq!(machine.advance(u64::MAX, true, 0), Ok(None));
        assert_eq!(machine.stats(), stats);
        // The result is still there for the asking, within the fuel given.
        assert_eq!(machine.normalize(10), Err(Halt::OutOfFuel));
        assert_eq!(machine.normalize(10_000_000), Ok(term));
        machine.collect();
        assert_eq!(machine.next(), None);
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
        // No walk has looked for the first pair yet. One that may fire
        // nothing goes up to it.
        assert!(machine.next().is_none() && !machine.is_normal());
        assert_eq!(machine.advance(0, false, u64::MAX), Ok(None));
        assert_eq!(machine.stats().interactions(), 0);
        let redex = machine.next().expect("the term has a redex");
        assert_eq!(redex.rule, Rule::Beta);
        assert_eq!(machine.net().kind(redex.upper), Kind::App);
        assert!(matches!(machine.net().kind(redex.lower), Kind::Lam { .. }));
        assert_eq!(machine.step(), Ok(Some(Rule::Beta)));
        while let Some(redex) = machine.next() {
            assert_eq!(machine.step(), Ok(Some(redex.rule)));
        }
        assert!(machine.is_normal());
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
