//! Contexts: what a walk down a net remembers in order to read it as a term.
//!
//! A net shares subterms, so one node can stand for several positions of the
//! term it represents. The context tells them apart. It has one entry per
//! enclosing scope, innermost first, and levels of fans and delimiters index
//! into it:
//!
//! - passing a fan from a branch towards its shared side records which branch
//!   was taken, and passing one the other way recalls it;
//! - entering an abstraction opens a fresh innermost scope;
//! - leaving through a delimiter closes the scope at its level and suspends
//!   it in the scope around, and entering through a delimiter resumes the
//!   scope suspended last, or opens a fresh one if there is none.
//!
//! Every rule except beta leaves these readings unchanged, which is what
//! makes reading back independent of how far the net has been reduced.

use std::rc::Rc;

/// A persistent stack: pushing and popping return new stacks that share
/// structure with the old one.
#[derive(Debug)]
struct Stack<T>(Option<Rc<Link<T>>>);

#[derive(Debug)]
struct Link<T> {
    head: T,
    tail: Stack<T>,
}

impl<T> Clone for Stack<T> {
    fn clone(&self) -> Self {
        Stack(self.0.clone())
    }
}

impl<T> Default for Stack<T> {
    fn default() -> Self {
        Stack(None)
    }
}

impl<T> Drop for Stack<T> {
    /// Unlinks iteratively, so that dropping a long stack cannot overflow the
    /// call stack.
    fn drop(&mut self) {
        let mut next = self.0.take();
        while let Some(link) = next {
            next = Rc::into_inner(link).and_then(|mut link| link.tail.0.take());
        }
    }
}

impl<T: Clone> Stack<T> {
    fn push(&self, head: T) -> Stack<T> {
        Stack(Some(Rc::new(Link {
            head,
            tail: self.clone(),
        })))
    }

    fn pop(&self) -> Option<(T, Stack<T>)> {
        self.0
            .as_ref()
            .map(|link| (link.head.clone(), link.tail.clone()))
    }
}

/// What the walk remembers about one scope.
#[derive(Clone, Debug, Default)]
struct Scope {
    /// Fan branches taken at this level, most recent first.
    branches: Stack<u8>,
    /// Scopes directly inside this one that the walk has left, most recent
    /// first.
    suspended: Stack<Scope>,
}

/// The memory of a walk. Scopes that were never touched are implicit.
#[derive(Clone, Debug, Default)]
pub struct Context {
    /// Innermost scope first.
    scopes: Stack<Scope>,
}

impl Context {
    /// Separates the `count` innermost scopes from the rest.
    fn split(&self, count: u32) -> (Vec<Scope>, Stack<Scope>) {
        let mut inner = Vec::new();
        let mut rest = self.scopes.clone();
        for _ in 0..count {
            let (scope, outer) = rest.pop().unwrap_or_default();
            inner.push(scope);
            rest = outer;
        }
        (inner, rest)
    }

    fn join(inner: Vec<Scope>, rest: Stack<Scope>) -> Context {
        let scopes = inner
            .into_iter()
            .rev()
            .fold(rest, |scopes, scope| scopes.push(scope));
        Context { scopes }
    }

    /// Opens a fresh innermost scope, for the body of an abstraction.
    pub fn enter_abstraction(&self) -> Context {
        Context {
            scopes: self.scopes.push(Scope::default()),
        }
    }

    /// Records the branch by which the walk came into a fan of this level.
    pub fn take_branch(&self, level: u32, branch: u8) -> Context {
        let (inner, rest) = self.split(level);
        let (mut scope, rest) = rest.pop().unwrap_or_default();
        scope.branches = scope.branches.push(branch);
        Context::join(inner, rest.push(scope))
    }

    /// Recalls the branch recorded last at this level, if there is one.
    pub fn recall_branch(&self, level: u32) -> Option<(u8, Context)> {
        let (inner, rest) = self.split(level);
        let (mut scope, rest) = rest.pop().unwrap_or_default();
        let (branch, branches) = scope.branches.pop()?;
        scope.branches = branches;
        Some((branch, Context::join(inner, rest.push(scope))))
    }

    /// Closes the scope at this level and suspends it in the one around.
    pub fn leave_scope(&self, level: u32) -> Context {
        let (inner, rest) = self.split(level);
        let (scope, rest) = rest.pop().unwrap_or_default();
        let (mut around, rest) = rest.pop().unwrap_or_default();
        around.suspended = around.suspended.push(scope);
        Context::join(inner, rest.push(around))
    }

    /// Reopens at this level the scope suspended last, or a fresh one.
    pub fn enter_scope(&self, level: u32) -> Context {
        let (inner, rest) = self.split(level);
        let (mut around, rest) = rest.pop().unwrap_or_default();
        let scope = match around.suspended.pop() {
            Some((scope, suspended)) => {
                around.suspended = suspended;
                scope
            }
            None => Scope::default(),
        };
        Context::join(inner, rest.push(around).push(scope))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Recalls branches at `level` until none is left.
    fn drain(mut context: Context, level: u32) -> Vec<u8> {
        let mut branches = Vec::new();
        while let Some((branch, rest)) = context.recall_branch(level) {
            branches.push(branch);
            context = rest;
        }
        branches
    }

    #[test]
    fn branches_come_back_in_reverse_order() {
        let context = Context::default().take_branch(0, 1).take_branch(0, 2);
        assert_eq!(drain(context, 0), [2, 1]);
        assert_eq!(drain(Context::default(), 3), []);
    }

    #[test]
    fn levels_are_independent() {
        let context = Context::default().take_branch(2, 1).take_branch(0, 2);
        assert_eq!(drain(context.clone(), 0), [2]);
        assert_eq!(drain(context.clone(), 1), []);
        assert_eq!(drain(context, 2), [1]);
    }

    #[test]
    fn abstractions_shift_outer_scopes() {
        let context = Context::default().take_branch(0, 1).enter_abstraction();
        assert_eq!(drain(context.clone(), 0), []);
        assert_eq!(drain(context, 1), [1]);
    }

    #[test]
    fn leaving_and_entering_a_scope_restores_it() {
        let inside = Context::default().take_branch(0, 1).take_branch(1, 2);
        let outside = inside.leave_scope(0);
        // Outside, the old level 1 is level 0 and the left scope is hidden.
        assert_eq!(drain(outside.clone(), 0), [2]);
        // Work done outside stays outside.
        let back = outside.take_branch(0, 1).enter_scope(0);
        assert_eq!(drain(back.clone(), 0), [1]);
        assert_eq!(drain(back, 1), [1, 2]);
    }

    #[test]
    fn entering_an_unknown_scope_opens_a_fresh_one() {
        let context = Context::default().take_branch(0, 1).enter_scope(0);
        assert_eq!(drain(context.clone(), 0), []);
        assert_eq!(drain(context, 1), [1]);
    }

    #[test]
    fn scopes_nest() {
        let context = Context::default()
            .take_branch(0, 1)
            .leave_scope(0)
            .take_branch(0, 2)
            .leave_scope(0)
            .enter_scope(0)
            .enter_scope(0);
        assert_eq!(drain(context.clone(), 0), [1]);
        assert_eq!(drain(context, 1), [2]);
    }

    #[test]
    fn long_stacks_drop_without_recursion() {
        let mut context = Context::default();
        for _ in 0..1_000_000 {
            context = context.take_branch(0, 1);
        }
        drop(context);
    }
}
