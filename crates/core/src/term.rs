//! λ-terms in de Bruijn form.
//!
//! Binder names are kept only as hints for printing. Equality is
//! α-equivalence: two terms are equal when they differ at most in those hints.

use std::collections::HashSet;
use std::fmt;

/// An untyped λ-term.
#[derive(Clone, Debug)]
pub enum Term {
    /// A bound variable, as a de Bruijn index (0 is the innermost binder).
    Var(usize),
    /// A free variable, identified by its name.
    Free(String),
    /// An abstraction. The name is a printing hint.
    Lam(String, Box<Term>),
    /// An application of a function to an argument.
    App(Box<Term>, Box<Term>),
}

impl Term {
    pub fn free(name: impl Into<String>) -> Term {
        Term::Free(name.into())
    }

    pub fn lam(name: impl Into<String>, body: Term) -> Term {
        Term::Lam(name.into(), Box::new(body))
    }

    pub fn app(func: Term, arg: Term) -> Term {
        Term::App(Box::new(func), Box::new(arg))
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

    /// The number of variables, abstractions and applications in the term.
    pub fn size(&self) -> usize {
        match self {
            Term::Var(_) | Term::Free(_) => 1,
            Term::Lam(_, body) => 1 + body.size(),
            Term::App(func, arg) => 1 + func.size() + arg.size(),
        }
    }

    fn collect_free_names<'a>(&'a self, names: &mut HashSet<&'a str>) {
        match self {
            Term::Var(_) => {}
            Term::Free(name) => {
                names.insert(name);
            }
            Term::Lam(_, body) => body.collect_free_names(names),
            Term::App(func, arg) => {
                func.collect_free_names(names);
                arg.collect_free_names(names);
            }
        }
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Term::Var(a), Term::Var(b)) => a == b,
            (Term::Free(a), Term::Free(b)) => a == b,
            (Term::Lam(_, a), Term::Lam(_, b)) => a == b,
            (Term::App(f, a), Term::App(g, b)) => f == g && a == b,
            _ => false,
        }
    }
}

impl Eq for Term {}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut reserved = HashSet::new();
        self.collect_free_names(&mut reserved);
        let mut printer = Printer {
            scope: Vec::new(),
            reserved,
        };
        printer.write(self, f, Position::Body)
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

struct Printer<'a> {
    /// Names of the enclosing binders, innermost last.
    scope: Vec<String>,
    /// Free variable names, which binders must not capture.
    reserved: HashSet<&'a str>,
}

impl Printer<'_> {
    fn write(
        &mut self,
        term: &Term,
        f: &mut fmt::Formatter<'_>,
        position: Position,
    ) -> fmt::Result {
        match term {
            Term::Var(index) => match self.scope.len().checked_sub(index + 1) {
                Some(slot) => f.write_str(&self.scope[slot]),
                None => write!(f, "#{}", index - self.scope.len()),
            },
            Term::Free(name) => f.write_str(name),
            Term::Lam(..) => {
                let parenthesized = position != Position::Body;
                if parenthesized {
                    f.write_str("(")?;
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
                    self.scope.push(name);
                    inner = body;
                }
                f.write_str(". ")?;
                self.write(inner, f, Position::Body)?;
                self.scope.truncate(depth);
                if parenthesized {
                    f.write_str(")")?;
                }
                Ok(())
            }
            Term::App(func, arg) => {
                let parenthesized = position == Position::Argument;
                if parenthesized {
                    f.write_str("(")?;
                }
                self.write(func, f, Position::Function)?;
                f.write_str(" ")?;
                self.write(arg, f, Position::Argument)?;
                if parenthesized {
                    f.write_str(")")?;
                }
                Ok(())
            }
        }
    }

    /// Picks a binder name close to `hint` that shadows nothing in scope.
    fn fresh(&self, hint: &str) -> String {
        let taken = |name: &str| {
            self.reserved.contains(name) || self.scope.iter().any(|bound| bound == name)
        };
        let hint = if hint.is_empty() { "x" } else { hint };
        if !taken(hint) {
            return hint.to_owned();
        }
        let stem = hint.trim_end_matches(|c: char| c.is_ascii_digit());
        let stem = if stem.is_empty() { "x" } else { stem };
        let mut suffix = 1u64;
        loop {
            let candidate = format!("{stem}{suffix}");
            if !taken(&candidate) {
                return candidate;
            }
            suffix += 1;
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
}
