//! λ-terms in de Bruijn form.
//!
//! Binder names are kept only as hints for printing. Equality is
//! α-equivalence: two terms are equal when they differ at most in those hints.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, OnceLock};

/// An untyped λ-term.
///
/// Subterms are shared, so cloning a term is cheap whatever its size. Nothing
/// here recurses on the shape of a term: printing, comparing, measuring and
/// dropping all work on terms nested millions deep.
#[derive(Clone, Debug)]
pub enum Term {
    /// A bound variable, as a de Bruijn index (0 is the innermost binder).
    Var(usize),
    /// A free variable, identified by its name.
    Free(String),
    /// An abstraction. The name is a printing hint.
    Lam(String, Arc<Term>),
    /// An application of a function to an argument.
    App(Arc<Term>, Arc<Term>),
}

impl Term {
    /// The free variable called `name`.
    pub fn free(name: impl Into<String>) -> Term {
        Term::Free(name.into())
    }

    /// The abstraction `λname. body`. Index 0 in `body` refers to it.
    pub fn lam(name: impl Into<String>, body: Term) -> Term {
        Term::Lam(name.into(), Arc::new(body))
    }

    /// The application `func arg`.
    pub fn app(func: Term, arg: Term) -> Term {
        Term::App(Arc::new(func), Arc::new(arg))
    }

    /// The Church numeral `λf. λx. f (f ... (f x))` with `n` applications.
    pub fn church(n: u64) -> Term {
        let body = (0..n).fold(Term::Var(0), |acc, _| Term::app(Term::Var(1), acc));
        Term::lam("f", Term::lam("x", body))
    }

    /// Reads the term as a Church numeral, if it is one.
    pub fn as_church(&self) -> Option<u64> {
        let Term::Lam(_, outer) = self else {
            return None;
        };
        let Term::Lam(_, inner) = outer.as_ref() else {
            return None;
        };
        let mut body: &Term = inner;
        let mut count = 0;
        loop {
            match body {
                Term::Var(0) => return Some(count),
                Term::App(func, arg) if matches!(func.as_ref(), Term::Var(1)) => {
                    count += 1;
                    body = arg;
                }
                _ => return None,
            }
        }
    }

    /// The number of variables, abstractions and applications in the term,
    /// or `usize::MAX` if there are that many or more.
    ///
    /// A shared subterm counts once for every place it occurs, but is looked
    /// at only once: a chain of definitions that each use the one before
    /// twice doubles the size at every link, not the time to measure it.
    pub fn size(&self) -> usize {
        // The sizes of the shared subterms measured so far.
        let mut known: HashMap<*const Term, usize> = HashMap::new();
        let mut pending: Vec<Measure> = Vec::new();
        let mut size: usize = 0;
        let mut term = self;
        loop {
            size = size.saturating_add(1);
            match term {
                Term::Var(_) | Term::Free(_) => {}
                Term::Lam(_, body) => pending.push(Measure::Count(body)),
                Term::App(func, arg) => {
                    pending.push(Measure::Count(arg));
                    pending.push(Measure::Count(func));
                }
            }
            term = loop {
                match pending.pop() {
                    None => return size,
                    Some(Measure::Done(shared, before)) => {
                        known.insert(Arc::as_ptr(shared), size - before);
                    }
                    Some(Measure::Count(child)) if Arc::strong_count(child) == 1 => break child,
                    Some(Measure::Count(child)) => match known.get(&Arc::as_ptr(child)) {
                        Some(&measured) => size = size.saturating_add(measured),
                        None => {
                            pending.push(Measure::Done(child, size));
                            break child;
                        }
                    },
                }
            };
        }
    }

    /// The term as text, or a note of its size if it has more than `limit`
    /// nodes and so would be too long to be worth reading.
    pub fn abbreviated(&self, limit: usize) -> String {
        match self.size() {
            // `usize::MAX` may stand for more, which no limit allows.
            size if size > limit || size == usize::MAX => {
                format!("<a term of {}>", Nodes(size))
            }
            _ => self.to_string(),
        }
    }

    /// The names of the free variables, sorted and without repeats.
    pub fn free_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.free_name_set().into_iter().collect();
        names.sort_unstable();
        names
    }

    fn free_name_set(&self) -> HashSet<&str> {
        let mut names = HashSet::new();
        let mut pending: Vec<&Term> = vec![self];
        let mut seen: HashSet<*const Term> = HashSet::new();
        while let Some(term) = pending.pop() {
            match term {
                Term::Var(_) => {}
                Term::Free(name) => {
                    names.insert(name.as_str());
                }
                // A subterm can be shared, as a definition used twice is,
                // and what is free in it is the same wherever it sits. One
                // look is enough: a chain of definitions that each use the
                // one before twice would otherwise double the work each time.
                _ if !seen.insert(std::ptr::from_ref(term)) => {}
                Term::Lam(_, body) => pending.push(body),
                Term::App(func, arg) => {
                    pending.push(arg);
                    pending.push(func);
                }
            }
        }
        names
    }

    /// Moves the subterms that have subterms of their own into `pending`,
    /// leaving leaves in their place.
    fn detach(&mut self, pending: &mut Vec<Arc<Term>>) {
        let mut take = |child: &mut Arc<Term>| {
            if matches!(child.as_ref(), Term::Lam(..) | Term::App(..)) {
                pending.push(std::mem::replace(child, leaf()));
            }
        };
        match self {
            Term::Var(_) | Term::Free(_) => {}
            Term::Lam(_, body) => take(body),
            Term::App(func, arg) => {
                take(func);
                take(arg);
            }
        }
    }
}

/// A number of nodes as [`Term::size`] counts them, ready to be shown:
/// `usize::MAX` stands for that many or more.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Nodes(pub usize);

impl fmt::Display for Nodes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} nodes", self.0)?;
        if self.0 == usize::MAX {
            f.write_str(" or more")?;
        }
        Ok(())
    }
}

/// What is left to do while measuring a term.
enum Measure<'a> {
    /// Count the nodes of this subterm.
    Count(&'a Arc<Term>),
    /// This shared subterm is counted: the nodes counted since there were
    /// this many are its size.
    Done(&'a Arc<Term>, usize),
}

/// A leaf to put where a subterm was taken out.
fn leaf() -> Arc<Term> {
    static LEAF: OnceLock<Arc<Term>> = OnceLock::new();
    LEAF.get_or_init(|| Arc::new(Term::Var(0))).clone()
}

impl Drop for Term {
    /// Takes the term apart with a worklist, so that dropping a deep term
    /// cannot overflow the call stack.
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach(&mut pending);
        while let Some(child) = pending.pop() {
            // A subterm that something else still shares is left alone.
            if let Some(mut term) = Arc::into_inner(child) {
                term.detach(&mut pending);
            }
        }
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        let mut pending: Vec<(&Term, &Term)> = Vec::new();
        let mut pair = (self, other);
        loop {
            pair = match pair {
                (Term::Lam(_, a), Term::Lam(_, b)) => (a, b),
                (Term::App(f, a), Term::App(g, b)) => {
                    if !Arc::ptr_eq(a, b) {
                        pending.push((a, b));
                    }
                    (f, g)
                }
                (Term::Var(a), Term::Var(b)) if a == b => match pending.pop() {
                    Some(next) => next,
                    None => return true,
                },
                (Term::Free(a), Term::Free(b)) if a == b => match pending.pop() {
                    Some(next) => next,
                    None => return true,
                },
                _ => return false,
            };
        }
    }
}

impl Eq for Term {}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut printer = Printer {
            scope: Vec::new(),
            taken: self
                .free_name_set()
                .into_iter()
                .map(str::to_owned)
                .collect(),
            next_suffix: HashMap::new(),
        };
        printer.write(self, f)
    }
}

/// Where a subterm sits, which decides whether it needs parentheses.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Position {
    /// The whole term or the body of an abstraction.
    Body,
    /// The function side of an application.
    Function,
    /// The argument side of an application.
    Argument,
}

/// What is left to print.
enum Task<'a> {
    Term(&'a Term, Position),
    Text(&'static str),
    /// Forget the binders beyond this many: their abstraction is over.
    Leave(usize),
}

struct Printer {
    /// Names of the enclosing binders, innermost last.
    scope: Vec<String>,
    /// The names in `scope` and those of the free variables, none of which a
    /// new binder may take.
    taken: HashSet<String>,
    /// Per stem, a suffix below which every numbered name is taken.
    next_suffix: HashMap<String, u64>,
}

impl Printer {
    fn write(&mut self, term: &Term, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![Task::Term(term, Position::Body)];
        while let Some(task) = tasks.pop() {
            let (term, position) = match task {
                Task::Term(term, position) => (term, position),
                Task::Text(text) => {
                    f.write_str(text)?;
                    continue;
                }
                Task::Leave(depth) => {
                    self.leave(depth);
                    continue;
                }
            };
            match term {
                Term::Var(index) => {
                    let slot = index
                        .checked_add(1)
                        .and_then(|above| self.scope.len().checked_sub(above));
                    match slot {
                        Some(slot) => f.write_str(&self.scope[slot])?,
                        None => write!(f, "#{}", index - self.scope.len())?,
                    }
                }
                Term::Free(name) => f.write_str(name)?,
                Term::Lam(..) => {
                    let parenthesized = position != Position::Body;
                    if parenthesized {
                        f.write_str("(")?;
                        tasks.push(Task::Text(")"));
                    }
                    f.write_str("λ")?;
                    let depth = self.scope.len();
                    let mut inner = term;
                    while let Term::Lam(hint, body) = inner {
                        if self.scope.len() > depth {
                            f.write_str(" ")?;
                        }
                        let name = self.fresh(hint);
                        f.write_str(&name)?;
                        self.taken.insert(name.clone());
                        self.scope.push(name);
                        inner = body;
                    }
                    f.write_str(". ")?;
                    tasks.push(Task::Leave(depth));
                    tasks.push(Task::Term(inner, Position::Body));
                }
                Term::App(func, arg) => {
                    if position == Position::Argument {
                        f.write_str("(")?;
                        tasks.push(Task::Text(")"));
                    }
                    tasks.push(Task::Term(arg, Position::Argument));
                    tasks.push(Task::Text(" "));
                    tasks.push(Task::Term(func, Position::Function));
                }
            }
        }
        Ok(())
    }

    /// Picks a binder name close to `hint` that shadows nothing in scope.
    fn fresh(&mut self, hint: &str) -> String {
        let hint = if hint.is_empty() { "x" } else { hint };
        if !self.taken.contains(hint) {
            return hint.to_owned();
        }
        let stem = hint.trim_end_matches(|c: char| c.is_ascii_digit());
        let stem = if stem.is_empty() { "x" } else { stem };
        let mut suffix = self.next_suffix.get(stem).copied().unwrap_or(1);
        loop {
            let candidate = format!("{stem}{suffix}");
            suffix += 1;
            if !self.taken.contains(&candidate) {
                self.next_suffix.insert(stem.to_owned(), suffix);
                return candidate;
            }
        }
    }

    /// Forgets the binders beyond the first `depth`.
    fn leave(&mut self, depth: usize) {
        for name in self.scope.drain(depth..) {
            self.taken.remove(&name);
            // The name is free again, so a search for one like it must not
            // start beyond it.
            let stem = name.trim_end_matches(|c: char| c.is_ascii_digit());
            let Some(next) = self.next_suffix.get_mut(stem) else {
                continue;
            };
            if let Ok(suffix) = name[stem.len()..].parse::<u64>()
                && suffix < *next
                && format!("{stem}{suffix}") == name
            {
                *next = suffix;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equality_ignores_binder_names() {
        let a = Term::lam("x", Term::Var(0));
        let b = Term::lam("y", Term::Var(0));
        assert_eq!(a, b);
        assert_ne!(a, Term::lam("x", Term::free("x")));
    }

    #[test]
    fn large_terms_are_abbreviated() {
        assert_eq!(Term::church(2).abbreviated(7), "λf x. f (f x)");
        assert_eq!(Term::church(2).abbreviated(6), "<a term of 7 nodes>");
    }

    #[test]
    fn lists_free_names() {
        let term = Term::app(
            Term::lam("x", Term::app(Term::free("b"), Term::Var(0))),
            Term::app(Term::free("a"), Term::free("b")),
        );
        assert_eq!(term.free_names(), ["a", "b"]);
        assert!(Term::church(2).free_names().is_empty());
    }

    #[test]
    fn free_names_of_a_shared_subterm_are_looked_up_once() {
        // Each term holds the one before twice: 2^200 nodes as a tree, and
        // 200 as they are stored.
        let mut term = Term::lam("x", Term::app(Term::Var(0), Term::free("a")));
        for _ in 0..200 {
            term = Term::app(term.clone(), term);
        }
        assert_eq!(term.free_names(), ["a"]);
    }

    #[test]
    fn a_shared_subterm_is_measured_once() {
        // Each link holds the one before twice, and is twice its size and
        // one more: 3 × 2^n - 1 nodes as a tree.
        let mut term = Term::lam("x", Term::Var(0));
        for n in 1..=200 {
            term = Term::app(term.clone(), term);
            if n == 30 {
                assert_eq!(term.size(), 3 * (1 << 30) - 1);
                assert_eq!(term.abbreviated(10), "<a term of 3221225471 nodes>");
            }
        }
        assert_eq!(term.size(), usize::MAX);
        assert_eq!(
            term.abbreviated(10),
            format!("<a term of {} nodes or more>", usize::MAX)
        );
        // A subterm shared with something outside counts in full.
        let numeral = Term::church(5);
        let pair = Term::app(numeral.clone(), Term::app(numeral.clone(), numeral));
        assert_eq!(pair.size(), 3 * 13 + 2);
    }

    #[test]
    fn prints_with_minimal_parentheses() {
        let term = Term::lam(
            "f",
            Term::lam(
                "x",
                Term::app(
                    Term::app(Term::Var(1), Term::Var(0)),
                    Term::lam("y", Term::app(Term::Var(0), Term::Var(1))),
                ),
            ),
        );
        assert_eq!(term.to_string(), "λf x. f x (λy. y x)");
    }

    #[test]
    fn printing_avoids_capture() {
        let shadowing = Term::lam("x", Term::lam("x", Term::app(Term::Var(1), Term::Var(0))));
        assert_eq!(shadowing.to_string(), "λx x1. x x1");
        let free = Term::lam("y", Term::app(Term::free("y"), Term::Var(0)));
        assert_eq!(free.to_string(), "λy1. y y1");
    }

    #[test]
    fn church_numerals_round_trip() {
        assert_eq!(Term::church(0).to_string(), "λf x. x");
        assert_eq!(Term::church(3).to_string(), "λf x. f (f (f x))");
        for n in 0..5 {
            assert_eq!(Term::church(n).as_church(), Some(n));
        }
        assert_eq!(Term::lam("x", Term::Var(0)).as_church(), None);
    }

    #[test]
    fn names_are_reused_once_their_binder_is_closed() {
        let twice = Term::lam("x", Term::lam("x", Term::Var(0)));
        let term = Term::app(twice.clone(), twice);
        assert_eq!(term.to_string(), "(λx x1. x1) (λx x1. x1)");
        // A hint that is free again is taken as it is.
        let term = Term::lam(
            "y",
            Term::app(
                Term::lam("y1", Term::lam("y", Term::Var(0))),
                Term::lam("y", Term::lam("y", Term::Var(2))),
            ),
        );
        assert_eq!(term.to_string(), "λy. (λy1 y2. y2) (λy1 y2. y)");
    }

    #[test]
    fn many_binders_of_one_name_get_numbers_in_order() {
        let term = (0..3_000).fold(Term::Var(0), |body, _| Term::lam("y", body));
        let text = term.to_string();
        assert!(text.starts_with("λy y1 y2 y3 "), "{}", &text[..40]);
        assert!(
            text.ends_with(" y2998 y2999. y2999"),
            "{}",
            &text[text.len() - 40..]
        );
    }

    #[test]
    fn dangling_indices_print_as_numbers() {
        assert_eq!(Term::Var(2).to_string(), "#2");
        assert_eq!(Term::lam("x", Term::Var(3)).to_string(), "λx. #2");
        assert_eq!(
            Term::Var(usize::MAX).to_string(),
            format!("#{}", usize::MAX)
        );
    }

    #[test]
    fn deep_terms_need_no_deep_stack() {
        let depth = 300_000;
        let numeral = Term::church(depth);
        assert_eq!(numeral.size(), 2 * 300_000 + 3);
        assert_eq!(numeral, numeral.clone());
        assert_ne!(numeral, Term::church(depth - 1));
        assert!(numeral.free_names().is_empty());
        let text = numeral.to_string();
        assert!(text.starts_with("λf x. f (f (f "));
        assert!(text.trim_end_matches(')').ends_with("(f x"));
        // A chain nested on the function side, and a tower of binders.
        let chain = (0..depth).fold(Term::free("a"), |func, _| Term::app(func, Term::free("b")));
        assert_eq!(chain.size(), 2 * 300_000 + 1);
        assert_eq!(chain.free_names(), ["a", "b"]);
        let tower = (0..depth).fold(Term::Var(0), |body, _| Term::lam("", body));
        assert_eq!(tower.size(), 300_001);
        drop((numeral, chain, tower));
    }

    #[test]
    fn shared_subterms_survive_their_other_owners() {
        let shared = Term::church(1_000);
        let user = Term::app(shared.clone(), shared.clone());
        drop(shared);
        assert_eq!(user.size(), 2 * 2_003 + 1);
        let Term::App(func, arg) = &user else {
            unreachable!()
        };
        assert!(Arc::ptr_eq(func, arg) || func == arg);
        assert_eq!(func.as_church(), Some(1_000));
    }
}
