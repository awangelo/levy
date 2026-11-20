//! The walk: reading the term a net stands for.
//!
//! A walk goes from the root the way one reads a term: down through
//! abstractions, along the function side of applications to the head, then
//! through the arguments from left to right. One node can stand for several
//! places in the term, so the walk carries a [`Context`] that tells them
//! apart.
//!
//! A [`Policy`] says what happens at each active pair the walk crosses:
//! [`read`] leaves the pair alone, and the machine rewrites it and goes on
//! from just above it. A walk can stop half way, for lack of fuel, because it
//! was interrupted, or in front of a pair its policy may not rewrite, and be
//! taken up again from there.

use crate::context::{Context, Mark};
use crate::machine::Halt;
use crate::net::{Kind, Net, NodeId, Port, Symbol, slot};
use crate::term::Term;

/// Why a walk stopped before the end of the term.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Stop {
    /// It stands in front of an active pair that its policy may not rewrite.
    /// Nothing is wrong, and the walk can go on from there.
    Paused,
    /// It cannot go on, for a reason to tell the caller.
    Halt(Halt),
}

impl From<Halt> for Stop {
    fn from(halt: Halt) -> Stop {
        Stop::Halt(halt)
    }
}

impl Stop {
    /// The halt behind the stop of a walk that nothing held back from a
    /// pair: one that rewrites nothing, or all it finds.
    pub(crate) fn halt(self) -> Halt {
        match self {
            Stop::Halt(halt) => halt,
            Stop::Paused => unreachable!("nothing held the walk back from a pair"),
        }
    }
}

/// What a walk does with the active pairs it comes across.
pub(crate) trait Policy {
    fn net(&self) -> &Net;

    /// Rewrites the pair if it interacts and this policy reduces. Reports
    /// whether the net changed, or stops the walk in front of a pair that
    /// interacts and that this policy may not rewrite.
    fn fire(&mut self, upper: NodeId, lower: NodeId) -> Result<bool, Stop>;

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

    fn fire(&mut self, _upper: NodeId, _lower: NodeId) -> Result<bool, Stop> {
        Ok(false)
    }
}

/// Reads the term a net stands for from the root, without rewriting
/// anything and spending at most `fuel`.
pub(crate) fn read(net: &Net, fuel: u64, interrupted: &dyn Fn() -> bool) -> Result<Term, Halt> {
    let mut observe = Observe(net);
    let state = Suspended::at_root(net);
    let mut walker = Walker::new(&mut observe, state, fuel, None, interrupted);
    walker.term().map_err(Stop::halt)
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
pub(crate) struct Suspended {
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
    pub(crate) fn at_root(net: &Net) -> Suspended {
        Suspended {
            binders: Vec::new(),
            passed: Vec::new(),
            top: net.root().principal(),
            context: Context::default(),
            pending: Vec::new(),
            arguments: 0,
        }
    }

    /// The port the walk goes on from.
    pub(crate) fn top(&self) -> Port {
        self.top
    }

    /// Roughly the bytes a copy of the walk takes, without the terms it has
    /// read so far.
    pub(crate) fn bytes(&self) -> usize {
        self.context.bytes()
            + self.binders.len() * size_of::<NodeId>()
            + self.passed.len() * size_of::<Frame>()
            + self.pending.len() * size_of::<Pending>()
    }
}

/// Reads the term a net stands for, letting its policy rewrite on the way.
pub(crate) struct Walker<'a, P> {
    policy: &'a mut P,
    state: Suspended,
    /// How many more nodes the walk may come to.
    fuel: u64,
    /// The fuel the walk has after each rewrite but its first. With it, the
    /// fuel bounds what one interaction spends, as
    /// [`Machine::advance`](crate::machine::Machine::advance) has it.
    /// Without, it bounds the walk as a whole.
    refill: Option<u64>,
    /// Whether the walk has rewritten a pair.
    rewrote: bool,
    /// How many nodes the walk has paid for, which the fuel cannot tell once
    /// a refill has put it back up.
    spent: u64,
    /// Asked now and then whether to give up.
    interrupted: &'a dyn Fn() -> bool,
}

impl<'a, P: Policy> Walker<'a, P> {
    /// A walk that goes on from `state` with `fuel`, and with `refill` after
    /// each rewrite but its first if that is given.
    pub(crate) fn new(
        policy: &'a mut P,
        state: Suspended,
        fuel: u64,
        refill: Option<u64>,
        interrupted: &'a dyn Fn() -> bool,
    ) -> Self {
        Walker {
            policy,
            state,
            fuel,
            refill,
            rewrote: false,
            spent: 0,
            interrupted,
        }
    }

    /// Where the walk stopped, and the fuel it spent.
    pub(crate) fn finish(self) -> (Suspended, u64) {
        (self.state, self.spent)
    }

    /// Reads the term from where the walk stands.
    ///
    /// The term can be nested deeper than any call stack, so what is left to
    /// do is kept in a list, not in recursive calls. That list is also what
    /// lets a walk that stopped be taken up again: a stop leaves the state in
    /// front of the node it happened at.
    pub(crate) fn term(&mut self) -> Result<Term, Stop> {
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
    fn head(&mut self) -> Result<Head, Stop> {
        let head = loop {
            self.spend()?;
            let state = &mut self.state;
            let top = state.top;
            let entry = self.policy.net().peer(top);
            let fired = if top.is_principal() && entry.is_principal() {
                match self.policy.fire(top.node, entry.node) {
                    Err(Stop::Paused) => {
                        // The walk stops in front of the pair and pays for
                        // it when it goes on.
                        self.fuel += 1;
                        self.spent -= 1;
                        return Err(Stop::Paused);
                    }
                    fired => fired?,
                }
            } else {
                false
            };
            if fired {
                if std::mem::replace(&mut self.rewrote, true)
                    && let Some(fuel) = self.refill
                {
                    // An interaction after the first has fuel of its own. The
                    // walk was left no more than this by the one before, so
                    // nothing is taken from it.
                    self.fuel = fuel;
                }
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
                    return Err(Halt::Malformed("an abstraction is entered from its body").into());
                }
                (Kind::App, _) => {
                    return Err(Halt::Malformed("an application is entered from below").into());
                }
                (Kind::Eraser, _) => {
                    return Err(Halt::Malformed("the walk ran into an eraser").into());
                }
                (Kind::Root, _) => {
                    return Err(Halt::Malformed("the walk came back to the root").into());
                }
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

    /// Pays for one node the walk comes to, unless it is to give up first.
    fn spend(&mut self) -> Result<(), Halt> {
        if self.spent.is_multiple_of(crate::INTERRUPT_CHECK) && (self.interrupted)() {
            return Err(Halt::Interrupted);
        }
        self.fuel = self.fuel.checked_sub(1).ok_or(Halt::OutOfFuel)?;
        self.spent += 1;
        Ok(())
    }
}
