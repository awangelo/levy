//! The Lambdascope interaction rules.
//!
//! A rule rewrites two nodes whose principal ports face each other.
//!
//! - **Beta**: an application meets an abstraction. Both vanish. The body is
//!   handed to the parent of the application and the argument to the
//!   variable, each through a fresh delimiter of level 0 whose inside faces
//!   the body. The two delimiters mark the scope the abstraction used to
//!   bind.
//! - **Annihilate**: two fans or two delimiters of the same level meet. Both
//!   vanish and their wires are joined pairwise.
//! - **Commute**: any other pair involving a fan or a delimiter. The two nodes
//!   pass through each other, each being copied once per auxiliary port of
//!   the other. A fan or delimiter that enters a scope this way has its level
//!   raised: always when the scope is an abstraction, and when it is a
//!   delimiter only if the delimiter's level is not above its own.
//! - **Dissolve**: a delimiter reaches the root or a free variable. Nothing
//!   lies beyond, so the delimiter vanishes.
//!
//! A delimiter node stands for a stack of delimiters of one level, and a rule
//! treats it as it would treat those delimiters one by one: it raises levels
//! by the height of the stack, and two stacks of different heights annihilate
//! only as far as the shorter one goes. [`merge`] builds such stacks.
//!
//! Erasers never interact here. The machine reduces only what the result
//! needs, so garbage is left alone instead of being erased step by step.

use crate::net::{Kind, Net, NodeId, Port, slot};

/// The rule that applies to a pair of nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Rule {
    /// An application meets an abstraction.
    Beta,
    /// Two fans or two delimiters of one level cancel each other.
    Annihilate,
    /// Two nodes pass through each other, each copying the other.
    Commute,
    /// A delimiter vanishes at the root or at a free variable.
    Dissolve,
}

impl Rule {
    /// The name of the rule, in lower case.
    pub fn name(self) -> &'static str {
        match self {
            Rule::Beta => "beta",
            Rule::Annihilate => "annihilate",
            Rule::Commute => "commute",
            Rule::Dissolve => "dissolve",
        }
    }
}

/// The rule for two kinds of nodes meeting at their principal ports, if any.
pub fn rule_for(a: Kind, b: Kind) -> Option<Rule> {
    use Kind::{App, Delim, Fan, Free, Lam, Root};
    match (a, b) {
        (App, Lam { .. }) | (Lam { .. }, App) => Some(Rule::Beta),
        (Fan { level: i }, Fan { level: j }) | (Delim { level: i, .. }, Delim { level: j, .. }) => {
            Some(if i == j {
                Rule::Annihilate
            } else {
                Rule::Commute
            })
        }
        (Delim { .. }, Root | Free { .. }) | (Root | Free { .. }, Delim { .. }) => {
            Some(Rule::Dissolve)
        }
        (Fan { .. } | Delim { .. }, Lam { .. } | App | Fan { .. } | Delim { .. })
        | (Lam { .. } | App, Fan { .. } | Delim { .. })
        | (Fan { .. }, Free { .. })
        | (Free { .. }, Fan { .. }) => Some(Rule::Commute),
        _ => None,
    }
}

/// Rewrites the pair `a`, `b` by `rule`, which must be the one [`rule_for`]
/// gives for it. The principal ports of the two must face each other.
pub fn rewrite(net: &mut Net, rule: Rule, a: NodeId, b: NodeId) {
    debug_assert_eq!(net.peer(a.principal()), b.principal());
    debug_assert_eq!(rule_for(net.kind(a), net.kind(b)), Some(rule));
    match rule {
        Rule::Beta => {
            let (app, lam) = if net.kind(a) == Kind::App {
                (a, b)
            } else {
                (b, a)
            };
            beta(net, app, lam);
        }
        Rule::Annihilate => annihilate(net, a, b),
        Rule::Commute => commute(net, a, b),
        Rule::Dissolve => {
            let (delimiter, anchor) = if matches!(net.kind(a), Kind::Delim { .. }) {
                (a, b)
            } else {
                (b, a)
            };
            dissolve(net, delimiter, anchor);
        }
    }
}

fn beta(net: &mut Net, app: NodeId, lam: NodeId) {
    let scope = Kind::Delim { level: 0, count: 1 };
    let above = net.add(scope);
    net.transfer(app.port(slot::RESULT), above.principal());
    net.transfer(lam.port(slot::BODY), above.port(slot::INSIDE));
    // An argument that an eraser waits for gets its delimiter all the same,
    // though both are garbage from here on. The eraser may be one that a
    // collection put in, and a reduction must make the same nodes whenever
    // its garbage is collected.
    let below = net.add(scope);
    net.transfer(app.port(slot::ARG), below.principal());
    net.transfer(lam.port(slot::VAR), below.port(slot::INSIDE));
    net.remove(app);
    net.remove(lam);
}

fn annihilate(net: &mut Net, a: NodeId, b: NodeId) {
    if let (Kind::Delim { level, count }, Kind::Delim { count: other, .. }) =
        (net.kind(a), net.kind(b))
        && count != other
    {
        // The shorter stack cancels as much of the taller one, and what is
        // left of the taller one carries on.
        let (survivor, gone) = if count > other { (a, b) } else { (b, a) };
        net.set_kind(
            survivor,
            Kind::Delim {
                level,
                count: count.abs_diff(other),
            },
        );
        net.transfer(gone.port(slot::INSIDE), survivor.principal());
        net.remove(gone);
        return;
    }
    for slot in 1..net.kind(a).ports() {
        net.splice(a.port(slot), b.port(slot));
    }
    net.remove(a);
    net.remove(b);
}

fn commute(net: &mut Net, a: NodeId, b: NodeId) {
    let (kind_a, kind_b) = (net.kind(a), net.kind(b));
    // One copy of each node per auxiliary port of the other.
    let copies_of_a: Vec<NodeId> = (1..kind_b.ports())
        .map(|_| net.add(crossing(kind_a, kind_b)))
        .collect();
    let copies_of_b: Vec<NodeId> = (1..kind_a.ports())
        .map(|_| net.add(crossing(kind_b, kind_a)))
        .collect();
    for (copy, slot) in copies_of_a.iter().zip(1..) {
        net.transfer(b.port(slot), copy.principal());
    }
    for (copy, slot) in copies_of_b.iter().zip(1..) {
        net.transfer(a.port(slot), copy.principal());
    }
    for (copy_of_a, slot_of_b) in copies_of_a.iter().zip(1..) {
        for (copy_of_b, slot_of_a) in copies_of_b.iter().zip(1..) {
            net.link(copy_of_a.port(slot_of_a), copy_of_b.port(slot_of_b));
        }
    }
    net.remove(a);
    net.remove(b);
}

/// What a node of kind `me` becomes once it has passed through `other`.
fn crossing(me: Kind, other: Kind) -> Kind {
    let raised = |level: u32| match other {
        Kind::Lam { .. } => sum(level, 1),
        // Each delimiter of the stack is one more scope to be inside of.
        Kind::Delim {
            level: border,
            count,
        } if border <= level => sum(level, count),
        _ => level,
    };
    match me {
        Kind::Fan { level } => Kind::Fan {
            level: raised(level),
        },
        Kind::Delim { level, count } => Kind::Delim {
            level: raised(level),
            count,
        },
        unchanged => unchanged,
    }
}

/// Adds levels or heights. Either would take more interactions than a
/// machine can run to get anywhere near the limit, so this is not something
/// to recover from.
fn sum(a: u32, b: u32) -> u32 {
    a.checked_add(b)
        .expect("levels and heights stay far below 2^32")
}

fn dissolve(net: &mut Net, delimiter: NodeId, anchor: NodeId) {
    net.transfer(delimiter.port(slot::INSIDE), anchor.principal());
    net.remove(delimiter);
}

/// Merges two delimiters that are stacked: wired outside to inside, with the
/// same level. The one at `exit` stays and stands for both; the one at the
/// other end of the wire goes. Returns the level and the height of what was
/// merged in, or `None` if the wire does not join two stacked delimiters.
///
/// Delimiters stacked this way can only move one after the other, each
/// repeating what the one before did. As one node they move together, which
/// keeps long reductions from drowning in delimiters. This is no interaction:
/// the net stands for the same term with the same sharing.
pub fn merge(net: &mut Net, exit: Port) -> Option<(u32, u32)> {
    let entry = net.peer(exit);
    let (
        Kind::Delim { level, count },
        Kind::Delim {
            level: same,
            count: more,
        },
    ) = (net.kind(exit.node), net.kind(entry.node))
    else {
        return None;
    };
    // Stacked means the outside of one is wired to the inside of the other.
    if exit.node == entry.node || level != same || exit.is_principal() == entry.is_principal() {
        return None;
    }
    net.set_kind(
        exit.node,
        Kind::Delim {
            level,
            count: sum(count, more),
        },
    );
    let far_side = if entry.is_principal() {
        slot::INSIDE
    } else {
        slot::PRINCIPAL
    };
    net.transfer(entry.node.port(far_side), exit);
    net.remove(entry.node);
    Some((level, more))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net::Port;

    /// Rewrites the pair `a`, `b`, whose principal ports must face each
    /// other. Returns the rule that was applied, or `None` if the pair does
    /// not interact, in which case the net is unchanged.
    fn apply(net: &mut Net, a: NodeId, b: NodeId) -> Option<Rule> {
        let rule = rule_for(net.kind(a), net.kind(b))?;
        rewrite(net, rule, a, b);
        Some(rule)
    }

    /// A net with `kinds` as loose nodes, each auxiliary port plugged by its
    /// own free variable so that rewiring can be inspected.
    struct Bench {
        net: Net,
        plugs: Vec<Vec<Port>>,
        nodes: Vec<NodeId>,
    }

    impl Bench {
        fn new<const N: usize>(kinds: impl FnOnce(&mut Net) -> [Kind; N]) -> Bench {
            let mut net = Net::new();
            let anchor = net.add(Kind::Eraser);
            net.link(net.root().principal(), anchor.principal());
            let kinds = kinds(&mut net);
            let mut plugs = Vec::new();
            let mut nodes = Vec::new();
            for (index, kind) in kinds.into_iter().enumerate() {
                let node = net.add(kind);
                let mut ports = Vec::new();
                for slot in 1..kind.ports() {
                    let name = net.intern(&format!("p{index}{slot}"));
                    let plug = net.add(Kind::Free { name });
                    net.link(node.port(slot), plug.principal());
                    ports.push(plug.principal());
                }
                nodes.push(node);
                plugs.push(ports);
            }
            Bench { net, plugs, nodes }
        }

        /// Faces the first two nodes and rewrites them.
        fn fire(&mut self) -> Option<Rule> {
            let (a, b) = (self.nodes[0], self.nodes[1]);
            self.net.link(a.principal(), b.principal());
            let rule = apply(&mut self.net, a, b);
            assert_eq!(self.net.check(), Ok(()));
            rule
        }

        /// The port and kind found at the other end of a plug.
        fn beyond(&self, node: usize, aux: usize) -> (Port, Kind) {
            let port = self.net.peer(self.plugs[node][aux]);
            (port, self.net.kind(port.node))
        }
    }

    fn lam(net: &mut Net) -> Kind {
        Kind::Lam {
            name: net.intern("x"),
        }
    }

    fn free(net: &mut Net) -> Kind {
        Kind::Free {
            name: net.intern("y"),
        }
    }

    #[test]
    fn beta_wraps_the_body_in_a_scope() {
        let mut bench = Bench::new(|net| [Kind::App, lam(net)]);
        assert_eq!(bench.fire(), Some(Rule::Beta));
        // Result and argument see the outside of a delimiter.
        for aux in 0..2 {
            let (port, kind) = bench.beyond(0, aux);
            assert_eq!(
                (port.slot, kind),
                (slot::PRINCIPAL, Kind::Delim { level: 0, count: 1 })
            );
        }
        // Body and variable see the inside of one.
        for aux in 0..2 {
            let (port, kind) = bench.beyond(1, aux);
            assert_eq!(
                (port.slot, kind),
                (slot::INSIDE, Kind::Delim { level: 0, count: 1 })
            );
        }
        // Result pairs with body, argument with variable.
        assert_eq!(bench.beyond(0, 0).0.node, bench.beyond(1, 0).0.node);
        assert_eq!(bench.beyond(0, 1).0.node, bench.beyond(1, 1).0.node);
    }

    #[test]
    fn beta_on_an_unused_variable_hands_the_argument_to_the_eraser() {
        let mut bench = Bench::new(|net| [Kind::App, lam(net)]);
        let eraser = bench.net.add(Kind::Eraser);
        let variable = bench.nodes[1].port(slot::VAR);
        let plug = bench.net.peer(variable).node;
        bench.net.link(variable, eraser.principal());
        bench.net.remove(plug);
        assert_eq!(bench.fire(), Some(Rule::Beta));
        // Through a delimiter, as any variable would get it.
        let (port, kind) = bench.beyond(0, 1);
        assert_eq!(
            (port.slot, kind),
            (slot::PRINCIPAL, Kind::Delim { level: 0, count: 1 })
        );
        assert_eq!(
            bench.net.peer(port.node.port(slot::INSIDE)),
            eraser.principal()
        );
    }

    #[test]
    fn beta_on_the_identity_joins_the_two_delimiters() {
        let mut net = Net::new();
        let name = net.intern("x");
        let (app, lam) = (net.add(Kind::App), net.add(Kind::Lam { name }));
        let arg = net.add(Kind::Free { name });
        net.link(net.root().principal(), app.port(slot::RESULT));
        net.link(app.principal(), lam.principal());
        net.link(app.port(slot::ARG), arg.principal());
        net.link(lam.port(slot::BODY), lam.port(slot::VAR));
        assert_eq!(apply(&mut net, app, lam), Some(Rule::Beta));
        assert_eq!(net.check(), Ok(()));
        let above = net.peer(net.root().principal());
        let below = net.peer(arg.principal());
        assert_eq!((above.slot, below.slot), (slot::PRINCIPAL, slot::PRINCIPAL));
        assert_eq!(
            net.peer(above.node.port(slot::INSIDE)),
            below.node.port(slot::INSIDE)
        );
    }

    #[test]
    fn equal_levels_annihilate() {
        let fan = Kind::Fan { level: 3 };
        let mut bench = Bench::new(|_| [fan, fan]);
        assert_eq!(bench.fire(), Some(Rule::Annihilate));
        assert_eq!(bench.beyond(0, 0).0, bench.plugs[1][0]);
        assert_eq!(bench.beyond(0, 1).0, bench.plugs[1][1]);

        let delimiter = Kind::Delim { level: 1, count: 1 };
        let mut bench = Bench::new(|_| [delimiter, delimiter]);
        assert_eq!(bench.fire(), Some(Rule::Annihilate));
        assert_eq!(bench.beyond(0, 0).0, bench.plugs[1][0]);
    }

    #[test]
    fn fans_of_different_levels_duplicate_each_other() {
        let mut bench = Bench::new(|_| [Kind::Fan { level: 0 }, Kind::Fan { level: 1 }]);
        assert_eq!(bench.fire(), Some(Rule::Commute));
        for aux in 0..2 {
            assert_eq!(bench.beyond(0, aux).1, Kind::Fan { level: 1 });
            assert_eq!(bench.beyond(1, aux).1, Kind::Fan { level: 0 });
        }
        // Branch i of one copy leads to branch j of the opposite copy.
        let copy = bench.beyond(0, 0).0.node;
        let opposite = bench.beyond(1, 1).0.node;
        assert_eq!(bench.net.peer(copy.port(2)), opposite.port(1));
    }

    #[test]
    fn entering_an_abstraction_raises_the_level() {
        let mut bench = Bench::new(|net| [Kind::Fan { level: 2 }, lam(net)]);
        let name = bench.net.kind(bench.nodes[1]);
        assert_eq!(bench.fire(), Some(Rule::Commute));
        // The abstraction is duplicated, with fans of level 3 below.
        assert_eq!(bench.beyond(0, 0).1, name);
        assert_eq!(bench.beyond(0, 1).1, name);
        assert_eq!(bench.beyond(1, 0).1, Kind::Fan { level: 3 });
        assert_eq!(bench.beyond(1, 1).1, Kind::Fan { level: 3 });

        let mut bench = Bench::new(|net| [Kind::Delim { level: 0, count: 1 }, lam(net)]);
        assert_eq!(bench.fire(), Some(Rule::Commute));
        assert_eq!(bench.beyond(0, 0).1, name);
        assert_eq!(bench.beyond(1, 0).1, Kind::Delim { level: 1, count: 1 });
        assert_eq!(bench.beyond(1, 1).1, Kind::Delim { level: 1, count: 1 });
    }

    #[test]
    fn applications_leave_levels_alone() {
        let mut bench = Bench::new(|_| [Kind::Delim { level: 4, count: 1 }, Kind::App]);
        assert_eq!(bench.fire(), Some(Rule::Commute));
        assert_eq!(bench.beyond(0, 0).1, Kind::App);
        assert_eq!(bench.beyond(1, 0).1, Kind::Delim { level: 4, count: 1 });
        assert_eq!(bench.beyond(1, 1).1, Kind::Delim { level: 4, count: 1 });
    }

    #[test]
    fn a_delimiter_raises_levels_at_or_above_its_own() {
        for (delimiter, fan, raised) in [(0, 0, 1), (1, 1, 2), (0, 5, 6), (2, 1, 1)] {
            let mut bench = Bench::new(|_| {
                [
                    Kind::Delim {
                        level: delimiter,
                        count: 1,
                    },
                    Kind::Fan { level: fan },
                ]
            });
            assert_eq!(bench.fire(), Some(Rule::Commute));
            assert_eq!(bench.beyond(0, 0).1, Kind::Fan { level: raised });
            assert_eq!(
                bench.beyond(1, 0).1,
                Kind::Delim {
                    level: delimiter,
                    count: 1
                }
            );
        }
        // Between two delimiters, only the higher one is raised.
        let mut bench = Bench::new(|_| {
            [
                Kind::Delim { level: 1, count: 1 },
                Kind::Delim { level: 3, count: 1 },
            ]
        });
        assert_eq!(bench.fire(), Some(Rule::Commute));
        assert_eq!(bench.beyond(0, 0).1, Kind::Delim { level: 4, count: 1 });
        assert_eq!(bench.beyond(1, 0).1, Kind::Delim { level: 1, count: 1 });
    }

    #[test]
    fn a_stack_of_delimiters_raises_by_its_height() {
        let stack = Kind::Delim { level: 1, count: 3 };
        let mut bench = Bench::new(|_| [stack, Kind::Fan { level: 2 }]);
        assert_eq!(bench.fire(), Some(Rule::Commute));
        assert_eq!(bench.beyond(0, 0).1, Kind::Fan { level: 5 });
        assert_eq!(bench.beyond(1, 0).1, stack);

        // A fan below the stack's level is left alone, and an abstraction
        // raises the whole stack by one.
        let mut bench = Bench::new(|_| [stack, Kind::Fan { level: 0 }]);
        assert_eq!(bench.fire(), Some(Rule::Commute));
        assert_eq!(bench.beyond(0, 0).1, Kind::Fan { level: 0 });
        let mut bench = Bench::new(|net| [stack, lam(net)]);
        assert_eq!(bench.fire(), Some(Rule::Commute));
        assert_eq!(bench.beyond(1, 0).1, Kind::Delim { level: 2, count: 3 });

        // Between stacks, the higher one is raised by the height of the other.
        let mut bench = Bench::new(|_| [stack, Kind::Delim { level: 4, count: 2 }]);
        assert_eq!(bench.fire(), Some(Rule::Commute));
        assert_eq!(bench.beyond(0, 0).1, Kind::Delim { level: 7, count: 2 });
        assert_eq!(bench.beyond(1, 0).1, stack);
    }

    #[test]
    fn unequal_stacks_annihilate_in_part() {
        let mut bench = Bench::new(|_| {
            [
                Kind::Delim { level: 1, count: 5 },
                Kind::Delim { level: 1, count: 2 },
            ]
        });
        assert_eq!(bench.fire(), Some(Rule::Annihilate));
        // What is left of the taller stack now faces what the shorter one hid.
        let (port, kind) = bench.beyond(1, 0);
        assert_eq!(kind, Kind::Delim { level: 1, count: 3 });
        assert!(port.is_principal());
        assert_eq!(bench.beyond(0, 0).0.node, port.node);
    }

    /// A chain root, delimiter, delimiter, free variable, the delimiters
    /// facing as `outward` says: towards the root, or away from it.
    fn stacked(first: Kind, second: Kind, outward: bool) -> (Net, NodeId, NodeId, NodeId) {
        let mut net = Net::new();
        let (upper, lower) = (net.add(first), net.add(second));
        let kind = free(&mut net);
        let leaf = net.add(kind);
        let (top, bottom) = if outward {
            (slot::PRINCIPAL, slot::INSIDE)
        } else {
            (slot::INSIDE, slot::PRINCIPAL)
        };
        net.link(net.root().principal(), upper.port(top));
        net.link(upper.port(bottom), lower.port(top));
        net.link(lower.port(bottom), leaf.principal());
        (net, upper, lower, leaf)
    }

    #[test]
    fn stacked_delimiters_merge() {
        let (two, three) = (
            Kind::Delim { level: 1, count: 2 },
            Kind::Delim { level: 1, count: 3 },
        );
        for outward in [true, false] {
            let (mut net, upper, lower, leaf) = stacked(two, three, outward);
            let exit = net.peer(lower.port(if outward {
                slot::PRINCIPAL
            } else {
                slot::INSIDE
            }));
            assert_eq!(exit.node, upper);
            assert_eq!(merge(&mut net, exit), Some((1, 3)));
            assert_eq!(net.check(), Ok(()));
            assert_eq!(net.kind(upper), Kind::Delim { level: 1, count: 5 });
            assert!(!net.contains(lower));
            assert_eq!(net.peer(exit), leaf.principal());
            assert_eq!(net.peer(net.root().principal()).node, upper);
        }
    }

    #[test]
    fn only_stacked_delimiters_merge() {
        // Different levels.
        let (mut net, upper, _, _) = stacked(
            Kind::Delim { level: 0, count: 1 },
            Kind::Delim { level: 1, count: 1 },
            true,
        );
        let exit = upper.port(slot::INSIDE);
        assert_eq!(merge(&mut net, exit), None);
        // A delimiter next to something else.
        let exit = net.root().principal();
        assert_eq!(merge(&mut net, exit), None);
        // Face to face: that is an active pair, not a stack.
        let mut bench = Bench::new(|_| [Kind::Delim { level: 0, count: 1 }; 2]);
        let (a, b) = (bench.nodes[0], bench.nodes[1]);
        bench.net.link(a.principal(), b.principal());
        assert_eq!(merge(&mut bench.net, a.principal()), None);
        assert_eq!(bench.net.len(), 6);
    }

    #[test]
    fn delimiters_dissolve_at_the_root_and_at_free_variables() {
        let mut net = Net::new();
        let delimiter = net.add(Kind::Delim { level: 2, count: 1 });
        let kind = free(&mut net);
        let variable = net.add(kind);
        net.link(net.root().principal(), delimiter.principal());
        net.link(delimiter.port(slot::INSIDE), variable.principal());
        let root = net.root();
        assert_eq!(apply(&mut net, root, delimiter), Some(Rule::Dissolve));
        assert_eq!(net.peer(net.root().principal()), variable.principal());
        assert_eq!(net.check(), Ok(()));

        let mut bench = Bench::new(|net| [free(net), Kind::Delim { level: 0, count: 1 }]);
        let variable = bench.net.kind(bench.nodes[0]);
        assert_eq!(bench.fire(), Some(Rule::Dissolve));
        assert_eq!(bench.beyond(1, 0).1, variable);
    }

    #[test]
    fn fans_copy_free_variables() {
        let mut bench = Bench::new(|net| [Kind::Fan { level: 0 }, free(net)]);
        let variable = bench.net.kind(bench.nodes[1]);
        assert_eq!(bench.fire(), Some(Rule::Commute));
        assert_eq!(bench.beyond(0, 0).1, variable);
        assert_eq!(bench.beyond(0, 1).1, variable);
        assert_ne!(bench.beyond(0, 0).0, bench.beyond(0, 1).0);
    }

    #[test]
    fn pairs_without_a_rule_are_left_alone() {
        let mut bench = Bench::new(|net| [Kind::App, free(net)]);
        let before = bench.net.len();
        assert_eq!(bench.fire(), None);
        assert_eq!(bench.net.len(), before);
        assert_eq!(rule_for(Kind::Root, Kind::Fan { level: 0 }), None);
        assert_eq!(rule_for(Kind::Eraser, Kind::App), None);
    }
}
