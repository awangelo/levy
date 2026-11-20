//! Contexts: what a walk down a net remembers in order to read it as a term.
//!
//! A net shares subterms, so one node can stand for several positions of the
//! term it represents. The context tells them apart. It has one entry per
//! enclosing scope, innermost first, and levels of fans and delimiters index
//! into it:
//!
//! - passing a fan from a branch towards its shared side records which branch
//!   was taken, and passing one the other way recalls it;
//! - entering an abstraction opens a fresh innermost scope, tagged with the
//!   abstraction so that its variable can later tell which copy it belongs to;
//! - leaving through a delimiter closes the scope at its level and suspends
//!   it in the scope around, and entering through a delimiter resumes the
//!   scope suspended last, or opens a fresh one if there is none.
//!
//! Every rule except beta leaves these readings unchanged, which is what
//! makes reading back independent of how far the net has been reduced.
//!
//! The walk goes back to earlier contexts only in the reverse of the order it
//! reached them, as a depth-first search does. So a context is changed in
//! place, and every change leaves a note on a trail of how to take it back: a
//! mark is a length of the trail, and restoring it takes back the changes
//! made since. Closing or opening a whole stack of scopes, as a stack of
//! delimiters does, is one change. Each change costs the same however deep
//! its level, except that closing or opening scopes moves the scopes inside
//! them.

/// Stands for no scope, no binder, or the end of a stack.
const NONE: u32 = u32::MAX;

/// What the walk remembers about one scope.
#[derive(Clone, Copy, Debug)]
struct Scope {
    /// The abstraction whose body this scope is, as the number of
    /// abstractions around it in the term being read. Scopes opened by
    /// delimiters have none.
    binder: u32,
    /// Fan branches taken at this level, most recent on top.
    branches: u32,
    /// Scopes directly inside this one that the walk has left, most recent
    /// on top.
    suspended: u32,
}

impl Default for Scope {
    fn default() -> Self {
        Scope {
            binder: NONE,
            branches: NONE,
            suspended: NONE,
        }
    }
}

/// One entry of a stack: a value and the cell below it.
#[derive(Clone, Copy, Debug)]
struct Cell {
    value: u32,
    below: u32,
}

/// Many stacks of numbers in one arena, each named by its top cell. Cells
/// popped off are reused, so that what the walk lets go of is not kept.
#[derive(Clone, Debug)]
struct Stacks {
    cells: Vec<Cell>,
    /// The first unused cell, and through `below` the others.
    free: u32,
}

impl Default for Stacks {
    fn default() -> Self {
        Stacks {
            cells: Vec::new(),
            free: NONE,
        }
    }
}

impl Stacks {
    fn push(&mut self, top: &mut u32, value: u32) {
        let cell = Cell { value, below: *top };
        *top = if self.free == NONE {
            self.cells.push(cell);
            index(self.cells.len() - 1)
        } else {
            let free = self.free;
            self.free = self.cells[free as usize].below;
            self.cells[free as usize] = cell;
            free
        };
    }

    fn pop(&mut self, top: &mut u32) -> Option<u32> {
        let cell = *self.cells.get(*top as usize)?;
        self.cells[*top as usize].below = self.free;
        self.free = *top;
        *top = cell.below;
        Some(cell.value)
    }
}

/// How to take back one change. Positions are indices into `Context::open`.
///
/// The trail holds one of these for nearly every node a walk passes, so they
/// are kept to eight bytes. The rare changes that need more go on a stack of
/// their own.
#[derive(Clone, Copy, Debug)]
enum Undo {
    /// This many implicit scopes were made explicit at the outer end.
    Reach(u32),
    /// An abstraction opened a new innermost scope.
    Abstraction,
    /// A branch was recorded in the scope at this position.
    Take(u32),
    /// This branch was recalled from the scope at this position.
    Recall(u32, u8),
    /// The scope at this position was closed and suspended in the one
    /// before it.
    Leave(u32),
    /// A scope was opened right after this position: the one suspended last
    /// in the scope there if `true`, a fresh one if `false`.
    Enter(u32, bool),
    /// Several scopes were closed or opened at once: the last of
    /// `Context::stacked` says how.
    Stacked,
}

const _: () = assert!(size_of::<Undo>() == 8);

/// How to take back a change to several scopes in a row, as a stack of
/// delimiters makes.
#[derive(Clone, Copy, Debug)]
enum Stacked {
    /// This many scopes in a row, those that stood from this position on,
    /// were closed: each was suspended in the one before it.
    Leave { first: u32, height: u32 },
    /// This many scopes were opened in a row right after this position, each
    /// the one suspended last in the scope before it, or a fresh one once
    /// there was none. The fresh ones come after the `resumed` ones.
    Enter { at: u32, height: u32, resumed: u32 },
}

/// A point to come back to, as returned by [`Context::mark`].
pub type Mark = usize;

/// The memory of a walk. Scopes that were never touched are implicit.
#[derive(Clone, Debug, Default)]
pub struct Context {
    /// The open scopes, outermost first, as indices into `scopes`: level `n`
    /// is `n` places from the end.
    open: Vec<u32>,
    /// Every scope, open or suspended. Scopes are made and unmade last in,
    /// first out, so this is a stack.
    scopes: Vec<Scope>,
    /// The branches and suspended scopes of all of them.
    stacks: Stacks,
    /// The changes that may still be taken back, oldest first.
    trail: Vec<Undo>,
    /// The details of the changes on the trail that are
    /// [`Undo::Stacked`], oldest first.
    stacked: Vec<Stacked>,
    /// How many changes came before the first one on the trail.
    forgotten: usize,
}

fn index(value: usize) -> u32 {
    u32::try_from(value).expect("fewer than 2^32 scopes")
}

impl Context {
    /// The point the context has reached, to [`restore`](Context::restore)
    /// later.
    pub fn mark(&self) -> Mark {
        self.forgotten + self.trail.len()
    }

    /// Takes back every change made since `mark`.
    pub fn restore(&mut self, mark: Mark) {
        let keep = mark
            .checked_sub(self.forgotten)
            .expect("the mark was not forgotten");
        while self.trail.len() > keep {
            let Some(undo) = self.trail.pop() else { break };
            self.undo(undo);
        }
    }

    /// The bytes a copy of the context takes.
    pub fn bytes(&self) -> usize {
        self.open.len() * size_of::<u32>()
            + self.scopes.len() * size_of::<Scope>()
            + self.stacks.cells.len() * size_of::<Cell>()
            + self.trail.len() * size_of::<Undo>()
            + self.stacked.len() * size_of::<Stacked>()
    }

    /// Gives up the means to restore any mark taken so far.
    pub fn forget(&mut self) {
        self.forgotten += self.trail.len();
        self.trail.clear();
        self.stacked.clear();
    }

    fn undo(&mut self, undo: Undo) {
        match undo {
            Undo::Reach(count) => {
                let count = count as usize;
                self.open.drain(..count);
                self.scopes.truncate(self.scopes.len() - count);
            }
            Undo::Abstraction => {
                self.open.pop();
                self.scopes.pop();
            }
            Undo::Take(at) => {
                let scope = self.open[at as usize] as usize;
                self.stacks.pop(&mut self.scopes[scope].branches);
            }
            Undo::Recall(at, branch) => {
                let scope = self.open[at as usize] as usize;
                self.stacks
                    .push(&mut self.scopes[scope].branches, u32::from(branch));
            }
            Undo::Leave(at) => {
                let at = at as usize;
                let around = self.open[at - 1] as usize;
                let scope = self
                    .stacks
                    .pop(&mut self.scopes[around].suspended)
                    .expect("the left scope is suspended");
                self.open.insert(at, scope);
            }
            Undo::Enter(at, resumed) => {
                let at = at as usize;
                let scope = self.open.remove(at + 1);
                if resumed {
                    let around = self.open[at] as usize;
                    self.stacks.push(&mut self.scopes[around].suspended, scope);
                } else {
                    self.scopes.pop();
                }
            }
            Undo::Stacked => {
                let stacked = self
                    .stacked
                    .pop()
                    .expect("a stacked change has its details");
                self.undo_stacked(stacked);
            }
        }
    }

    fn undo_stacked(&mut self, stacked: Stacked) {
        match stacked {
            Stacked::Leave { first, height } => {
                let (first, height) = (first as usize, height as usize);
                // Each comes back out of the one before it, the outermost
                // first.
                self.open
                    .splice(first..first, std::iter::repeat_n(NONE, height));
                for at in first..first + height {
                    let around = self.open[at - 1] as usize;
                    self.open[at] = self
                        .stacks
                        .pop(&mut self.scopes[around].suspended)
                        .expect("the left scope is suspended");
                }
            }
            Stacked::Enter {
                at,
                height,
                resumed,
            } => {
                let (at, height, resumed) = (at as usize, height as usize, resumed as usize);
                // The fresh scopes were made last, and go first.
                self.scopes.truncate(self.scopes.len() - (height - resumed));
                for at in (at + 1..=at + resumed).rev() {
                    let around = self.open[at - 1] as usize;
                    let scope = self.open[at];
                    self.stacks.push(&mut self.scopes[around].suspended, scope);
                }
                self.open.drain(at + 1..=at + height);
            }
        }
    }

    /// Makes the scopes up to `level + above` explicit, and returns the
    /// position of the one at `level`.
    fn reach(&mut self, level: u32, above: u32) -> usize {
        let needed = level as usize + above as usize + 1;
        if self.open.len() < needed {
            let count = needed - self.open.len();
            let first = index(self.scopes.len());
            self.scopes
                .resize_with(self.scopes.len() + count, Scope::default);
            self.open.splice(..0, first..first + index(count));
            self.trail.push(Undo::Reach(index(count)));
        }
        self.open.len() - 1 - level as usize
    }

    /// Opens a fresh innermost scope for the body of an abstraction that has
    /// `binder` abstractions around it.
    pub fn enter_abstraction(&mut self, binder: usize) {
        self.open.push(index(self.scopes.len()));
        self.scopes.push(Scope {
            binder: index(binder),
            ..Scope::default()
        });
        self.trail.push(Undo::Abstraction);
    }

    /// The abstraction whose body is the innermost scope, if that scope was
    /// opened by one.
    pub fn binder(&self) -> Option<usize> {
        let scope = *self.open.last()? as usize;
        let binder = self.scopes[scope].binder;
        (binder != NONE).then_some(binder as usize)
    }

    /// Records the branch by which the walk came into a fan of this level.
    pub fn take_branch(&mut self, level: u32, branch: u8) {
        let at = self.reach(level, 0);
        let scope = self.open[at] as usize;
        self.stacks
            .push(&mut self.scopes[scope].branches, u32::from(branch));
        self.trail.push(Undo::Take(index(at)));
    }

    /// Recalls the branch recorded last at this level, if there is one.
    pub fn recall_branch(&mut self, level: u32) -> Option<u8> {
        let at = self.open.len().checked_sub(level as usize + 1)?;
        let scope = self.open[at] as usize;
        let branch = self.stacks.pop(&mut self.scopes[scope].branches)? as u8;
        self.trail.push(Undo::Recall(index(at), branch));
        Some(branch)
    }

    /// Closes `count` scopes in a row at this level, as a stack of that many
    /// delimiters does: the one at the level and those around it, each
    /// suspended in the one around it.
    pub fn leave_scopes(&mut self, level: u32, count: u32) {
        match count {
            0 => {}
            // Most stacks are one delimiter high, and one scope is quicker to
            // close on its own.
            1 => {
                let at = self.reach(level, 1);
                let scope = self.open.remove(at);
                let around = self.open[at - 1] as usize;
                self.stacks.push(&mut self.scopes[around].suspended, scope);
                self.trail.push(Undo::Leave(index(at)));
            }
            _ => {
                // The scope that takes the outermost of them must be open
                // too.
                let at = self.reach(level, count);
                let first = at + 1 - count as usize;
                for at in (first..=at).rev() {
                    let around = self.open[at - 1] as usize;
                    let scope = self.open[at];
                    self.stacks.push(&mut self.scopes[around].suspended, scope);
                }
                self.open.drain(first..=at);
                self.stack(Stacked::Leave {
                    first: index(first),
                    height: count,
                });
            }
        }
    }

    /// Reopens `count` scopes in a row at this level, each the one suspended
    /// last in the scope before it, or a fresh one.
    pub fn enter_scopes(&mut self, level: u32, count: u32) {
        if count == 0 {
            return;
        }
        let at = self.reach(level, 0);
        if count == 1 {
            // As for leaving: one scope is quicker to open on its own.
            let around = self.open[at] as usize;
            let (scope, resumed) = match self.stacks.pop(&mut self.scopes[around].suspended) {
                Some(scope) => (scope, true),
                None => (self.fresh(), false),
            };
            self.open.insert(at + 1, scope);
            self.trail.push(Undo::Enter(index(at), resumed));
            return;
        }
        let height = count as usize;
        self.open
            .splice(at + 1..at + 1, std::iter::repeat_n(NONE, height));
        let mut resumed = 0;
        for at in at + 1..=at + height {
            let around = self.open[at - 1] as usize;
            self.open[at] = match self.stacks.pop(&mut self.scopes[around].suspended) {
                Some(scope) => {
                    resumed += 1;
                    scope
                }
                None => self.fresh(),
            };
        }
        self.stack(Stacked::Enter {
            at: index(at),
            height: count,
            resumed,
        });
    }

    /// Logs a change to several scopes in a row.
    fn stack(&mut self, stacked: Stacked) {
        self.stacked.push(stacked);
        self.trail.push(Undo::Stacked);
    }

    /// Makes a scope for a delimiter to open, and returns its index.
    fn fresh(&mut self) -> u32 {
        self.scopes.push(Scope::default());
        index(self.scopes.len() - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Chainable versions of the changes, to write contexts as expressions.
    impl Context {
        fn take(mut self, level: u32, branch: u8) -> Context {
            self.take_branch(level, branch);
            self
        }

        fn abstraction(mut self, binder: usize) -> Context {
            self.enter_abstraction(binder);
            self
        }

        fn leave(mut self, level: u32, count: u32) -> Context {
            self.leave_scopes(level, count);
            self
        }

        fn enter(mut self, level: u32, count: u32) -> Context {
            self.enter_scopes(level, count);
            self
        }

        /// Everything a walk could read from the context: each open scope,
        /// innermost first, with its binder, branches and suspended scopes.
        fn reading(&self) -> Vec<String> {
            self.open
                .iter()
                .rev()
                .map(|&scope| self.render(scope))
                .collect()
        }

        fn render(&self, scope: u32) -> String {
            let scope = self.scopes[scope as usize];
            let suspended: Vec<String> = self
                .values(scope.suspended)
                .into_iter()
                .map(|inner| self.render(inner))
                .collect();
            let branches = self.values(scope.branches);
            // Joined as they are: quoting them would quote the quotes of
            // the scopes inside them again, once per level.
            format!("{} {branches:?} [{}]", scope.binder, suspended.join(", "))
        }

        fn values(&self, mut top: u32) -> Vec<u32> {
            let mut values = Vec::new();
            while top != NONE {
                let cell = self.stacks.cells[top as usize];
                values.push(cell.value);
                top = cell.below;
            }
            values
        }
    }

    /// Recalls branches at `level` until none is left.
    fn drain(mut context: Context, level: u32) -> Vec<u8> {
        let mut branches = Vec::new();
        while let Some(branch) = context.recall_branch(level) {
            branches.push(branch);
        }
        branches
    }

    #[test]
    fn branches_come_back_in_reverse_order() {
        let context = Context::default().take(0, 1).take(0, 2);
        assert_eq!(drain(context, 0), [2, 1]);
        assert_eq!(drain(Context::default(), 3), []);
    }

    #[test]
    fn levels_are_independent() {
        let context = Context::default().take(2, 1).take(0, 2);
        assert_eq!(drain(context.clone(), 0), [2]);
        assert_eq!(drain(context.clone(), 1), []);
        assert_eq!(drain(context, 2), [1]);
    }

    #[test]
    fn abstractions_shift_outer_scopes() {
        let context = Context::default().take(0, 1).abstraction(0);
        assert_eq!(drain(context.clone(), 0), []);
        assert_eq!(drain(context, 1), [1]);
    }

    #[test]
    fn scopes_remember_their_abstraction() {
        let context = Context::default().abstraction(0);
        assert_eq!(context.binder(), Some(0));
        let inner = context.clone().take(0, 1).abstraction(1);
        assert_eq!(inner.binder(), Some(1));
        // Leaving the inner scope brings the outer abstraction back in view,
        // and coming back restores the inner one.
        assert_eq!(inner.clone().leave(0, 1).binder(), Some(0));
        assert_eq!(inner.leave(0, 1).enter(0, 1).binder(), Some(1));
        // A scope opened by a delimiter belongs to no abstraction.
        assert_eq!(context.enter(0, 1).binder(), None);
        assert_eq!(Context::default().binder(), None);
    }

    #[test]
    fn leaving_and_entering_a_scope_restores_it() {
        let inside = Context::default().take(0, 1).take(1, 2);
        let outside = inside.leave(0, 1);
        // Outside, the old level 1 is level 0 and the left scope is hidden.
        assert_eq!(drain(outside.clone(), 0), [2]);
        // Work done outside stays outside.
        let back = outside.take(0, 1).enter(0, 1);
        assert_eq!(drain(back.clone(), 0), [1]);
        assert_eq!(drain(back, 1), [1, 2]);
    }

    #[test]
    fn entering_an_unknown_scope_opens_a_fresh_one() {
        let context = Context::default().take(0, 1).enter(0, 1);
        assert_eq!(drain(context.clone(), 0), []);
        assert_eq!(drain(context, 1), [1]);
    }

    #[test]
    fn scopes_nest() {
        let context = Context::default()
            .take(0, 1)
            .leave(0, 1)
            .take(0, 2)
            .leave(0, 1)
            .enter(0, 1)
            .enter(0, 1);
        assert_eq!(drain(context.clone(), 0), [1]);
        assert_eq!(drain(context, 1), [2]);
    }

    #[test]
    fn stacks_of_scopes_open_and_close_together() {
        let inside = Context::default()
            .take(0, 1)
            .abstraction(0)
            .take(0, 2)
            .abstraction(1);
        let outside = inside.leave(0, 2);
        assert_eq!(outside.binder(), None);
        let back = outside.enter(0, 2);
        assert_eq!(back.binder(), Some(1));
        assert_eq!(drain(back.clone(), 1), [2]);
        assert_eq!(drain(back, 2), [1]);
    }

    #[test]
    fn a_stack_of_scopes_is_one_change() {
        // Seven scopes made explicit, so that nothing else is logged.
        let mut context = Context::default().take(6, 1);
        let mark = context.mark();
        let before = context.reading();
        context.leave_scopes(1, 4);
        assert_eq!(context.mark(), mark + 1);
        let outside = context.reading();
        context.enter_scopes(1, 6);
        assert_eq!(context.mark(), mark + 2);
        context.restore(mark + 1);
        assert_eq!(context.reading(), outside);
        context.restore(mark);
        assert_eq!(context.reading(), before);
    }

    #[test]
    fn restoring_a_mark_takes_back_every_change_since() {
        let mut state: u64 = 0x2545_f491_4f6c_dd1d;
        let mut random = |bound: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state % bound) as u32
        };
        // The same changes twice: as they come, and with every stack of
        // scopes taken one scope at a time.
        let mut context = Context::default();
        let mut single = Context::default();
        let mut saved: Vec<(Mark, Mark, Vec<String>)> = Vec::new();
        for step in 0..3_000 {
            if random(8) == 0 {
                let reading = context.reading();
                assert_eq!(single.reading(), reading, "step {step}");
                saved.push((context.mark(), single.mark(), reading));
            }
            let level = random(6);
            match random(6) {
                0 => {
                    let branch = random(2) as u8 + 1;
                    context.take_branch(level, branch);
                    single.take_branch(level, branch);
                }
                1 => {
                    assert_eq!(context.recall_branch(level), single.recall_branch(level));
                }
                2 => {
                    let height = random(5) + 1;
                    context.leave_scopes(level, height);
                    for _ in 0..height {
                        single.leave_scopes(level, 1);
                    }
                }
                3 => {
                    let height = random(5) + 1;
                    context.enter_scopes(level, height);
                    for _ in 0..height {
                        single.enter_scopes(level, 1);
                    }
                }
                4 => {
                    context.enter_abstraction(step);
                    single.enter_abstraction(step);
                }
                _ => {
                    // Go back to a random earlier mark, dropping the later
                    // ones, as the walk does.
                    if !saved.is_empty() {
                        let keep = random(saved.len() as u64) as usize;
                        let (mark, single_mark, reading) = saved[keep].clone();
                        saved.truncate(keep);
                        context.restore(mark);
                        single.restore(single_mark);
                        assert_eq!(context.reading(), reading, "step {step}");
                        assert_eq!(single.reading(), reading, "step {step}");
                    }
                }
            }
        }
        assert_eq!(context.reading(), single.reading());
        for mut context in [context, single] {
            context.restore(0);
            assert!(context.open.is_empty() && context.scopes.is_empty());
            assert!(context.stacked.is_empty());
            // Every cell is back on the free list.
            let mut free = 0;
            let mut cell = context.stacks.free;
            while cell != NONE {
                free += 1;
                cell = context.stacks.cells[cell as usize].below;
            }
            assert_eq!(free, context.stacks.cells.len());
        }
    }
}
