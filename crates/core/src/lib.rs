//! Lévy-optimal reduction of the untyped λ-calculus.
//!
//! Terms are translated to Lambdascope interaction nets (van Oostrom, van de
//! Looij and Zwitserlood, 2004), reduced there with a leftmost-outermost
//! strategy, and read back as terms.
//!
//! ```
//! use levy_core::{Machine, parse};
//!
//! let term = parse(r"(\f x. f (f x)) (\f x. f (f x))")?;
//! let mut machine = Machine::new(&term)?;
//! // The fuel bounds the work, so a term without a normal form comes back
//! // as an error instead of running for ever.
//! let normal = machine.normalize(10_000)?;
//! assert_eq!(normal.as_church(), Some(4));
//! assert_eq!(machine.stats().beta, 5);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! Nothing in this crate recurses on the shape of a term or of a net, so the
//! depth of a term is limited by memory only, not by the stack.

#![warn(missing_docs)]

mod context;
pub mod dot;
pub mod gc;
pub mod machine;
pub mod net;
pub mod parse;
pub mod reference;
pub mod rules;
pub mod script;
pub mod term;
pub mod translate;

pub use machine::{Halt, Machine, Redex, Stats};
pub use parse::{ParseError, parse, parse_with};
pub use rules::Rule;
pub use script::{Definitions, Statement};
pub use term::Term;
pub use translate::UnboundIndex;

/// How often, in units of work, a reduction asks whether it was interrupted.
const INTERRUPT_CHECK: u64 = 1 << 10;
