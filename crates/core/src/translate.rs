//! Translation of λ-terms into Lambdascope nets.
//!
//! Abstractions and applications become nodes of the same name. A variable
//! occurrence becomes a wire to the variable port of its binder. On the way
//! it leaves the scope of every abstraction in between, and each such exit is
//! marked by a delimiter. A variable that occurs several times is shared by a
//! tree of fans, and one that never occurs is plugged with an eraser.

use std::fmt;

use crate::net::{Kind, Net, Port, slot};
use crate::term::Term;

/// The term has a de Bruijn index that points past its outermost binder.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnboundIndex(pub usize);

impl fmt::Display for UnboundIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "de Bruijn index {} has no binder", self.0)
    }
}

impl std::error::Error for UnboundIndex {}

/// Builds the net of `term`.
pub fn translate(term: &Term) -> Result<Net, UnboundIndex> {
    let mut builder = Builder {
        net: Net::new(),
        occurrences: Vec::new(),
    };
    let root = builder.net.root().principal();
    builder.build(term, root)?;
    Ok(builder.net)
}

struct Builder {
    net: Net,
    /// For each enclosing binder, innermost last, the ports that wait to be
    /// connected to its variable.
    occurrences: Vec<Vec<Port>>,
}

impl Builder {
    /// Builds `term` and attaches it to `parent`.
    fn build(&mut self, term: &Term, parent: Port) -> Result<(), UnboundIndex> {
        match term {
            Term::Var(index) => {
                let binder = self
                    .occurrences
                    .len()
                    .checked_sub(index + 1)
                    .ok_or(UnboundIndex(*index))?;
                let mut port = parent;
                for _ in 0..*index {
                    let delimiter = self.net.add(Kind::Delim { level: 0 });
                    self.net.link(delimiter.port(slot::INSIDE), port);
                    port = delimiter.principal();
                }
                self.occurrences[binder].push(port);
            }
            Term::Free(name) => {
                let name = self.net.intern(name);
                let free = self.net.add(Kind::Free { name });
                self.net.link(free.principal(), parent);
            }
            Term::Lam(name, body) => {
                let name = self.net.intern(name);
                let lam = self.net.add(Kind::Lam { name });
                self.net.link(lam.principal(), parent);
                self.occurrences.push(Vec::new());
                self.build(body, lam.port(slot::BODY))?;
                let occurrences = self.occurrences.pop().unwrap_or_default();
                self.share(lam.port(slot::VAR), &occurrences);
            }
            Term::App(func, arg) => {
                let app = self.net.add(Kind::App);
                self.net.link(app.port(slot::RESULT), parent);
                self.build(func, app.principal())?;
                self.build(arg, app.port(slot::ARG))?;
            }
        }
        Ok(())
    }

    /// Connects `source` to every port in `occurrences` through a balanced
    /// tree of fans.
    fn share(&mut self, source: Port, occurrences: &[Port]) {
        match occurrences {
            [] => {
                let eraser = self.net.add(Kind::Eraser);
                self.net.link(eraser.principal(), source);
            }
            [only] => self.net.link(source, *only),
            _ => {
                let fan = self.net.add(Kind::Fan { level: 0 });
                self.net.link(fan.principal(), source);
                let (first, second) = occurrences.split_at(occurrences.len() / 2);
                self.share(fan.port(slot::BRANCHES[0]), first);
                self.share(fan.port(slot::BRANCHES[1]), second);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    fn census(net: &Net) -> [usize; 5] {
        let mut counts = [0; 5];
        for (_, kind) in net.nodes() {
            let slot = match kind {
                Kind::Lam { .. } => 0,
                Kind::App => 1,
                Kind::Fan { .. } => 2,
                Kind::Delim { .. } => 3,
                Kind::Eraser => 4,
                Kind::Root | Kind::Free { .. } => continue,
            };
            counts[slot] += 1;
        }
        counts
    }

    fn net_of(source: &str) -> Net {
        let net = translate(&parse(source).unwrap()).unwrap();
        assert_eq!(net.check(), Ok(()), "{source}");
        net
    }

    #[test]
    fn identity_is_a_loop_on_one_node() {
        let net = net_of(r"\x. x");
        assert_eq!(census(&net), [1, 0, 0, 0, 0]);
        let lam = net.peer(net.root().principal()).node;
        assert_eq!(net.peer(lam.port(slot::BODY)), lam.port(slot::VAR));
    }

    #[test]
    fn unused_variables_are_erased() {
        assert_eq!(census(&net_of(r"\x. \y. y")), [2, 0, 0, 0, 1]);
    }

    #[test]
    fn occurrences_are_shared_by_fans() {
        assert_eq!(census(&net_of(r"\x. x x")), [1, 1, 1, 0, 0]);
        assert_eq!(census(&net_of(r"\x. x x x")), [1, 2, 2, 0, 0]);
    }

    #[test]
    fn crossing_a_binder_costs_a_delimiter() {
        // `x` leaves the scope of `y`, and of `y` and `z`.
        assert_eq!(census(&net_of(r"\x. \y. x")), [2, 0, 0, 1, 1]);
        assert_eq!(census(&net_of(r"\x. \y. \z. x")), [3, 0, 0, 2, 2]);
    }

    #[test]
    fn delimiters_face_the_binder() {
        let net = net_of(r"\x. \y. x");
        let outer = net.peer(net.root().principal()).node;
        let inner = net.peer(outer.port(slot::BODY)).node;
        let delimiter = net.peer(inner.port(slot::BODY));
        assert_eq!(delimiter.slot, slot::INSIDE);
        assert_eq!(net.peer(delimiter.node.principal()), outer.port(slot::VAR));
    }

    #[test]
    fn free_variables_get_their_own_nodes() {
        let net = net_of(r"\x. y y");
        assert_eq!(census(&net), [1, 1, 0, 0, 1]);
        assert_eq!(net.len(), 6);
    }

    #[test]
    fn dangling_indices_are_rejected() {
        assert_eq!(translate(&Term::Var(0)).unwrap_err(), UnboundIndex(0));
        let term = Term::lam("x", Term::Var(2));
        assert_eq!(translate(&term).unwrap_err(), UnboundIndex(2));
    }
}
