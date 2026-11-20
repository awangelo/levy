//! Scripts: statements that define names or ask for a term to be evaluated.
//!
//! ```text
//! statement ::= name "=" term | term
//! ```
//!
//! A definition gives a name to a term. The name stands for that term in
//! every statement that follows, wherever no binder captures it. Definitions
//! are expanded when a term is parsed, so they cannot refer to themselves:
//! recursion needs a fixed-point combinator.

use std::collections::HashMap;
use std::fmt;

use crate::parse::{ParseError, is_name, parse_with, position};
use crate::term::Term;

/// One statement of a script.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement {
    /// `name = term`: the name stands for the term from here on.
    Define(String, Term),
    /// A term to reduce.
    Evaluate(Term),
}

/// Why a script cannot be run: one of its statements is not one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScriptError {
    /// The line of the script the problem is on, counted from 1.
    pub line: usize,
    /// The column of that line, counted from 1, in characters.
    pub column: usize,
    /// What was expected or what is wrong, without the place.
    pub message: String,
}

impl ScriptError {
    /// What `error` is in a script, `statement` being the statement it was
    /// found in and `line` the line of the script that statement starts on.
    pub fn new(line: usize, statement: &str, error: ParseError) -> ScriptError {
        let (down, column) = position(statement, error.offset);
        ScriptError {
            line: line + down - 1,
            column,
            message: error.message,
        }
    }
}

impl fmt::Display for ScriptError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ScriptError {
            line,
            column,
            message,
        } = self;
        write!(f, "line {line}, column {column}: {message}")
    }
}

impl std::error::Error for ScriptError {}

/// The names defined so far.
#[derive(Clone, Debug, Default)]
pub struct Definitions {
    /// In the order the names were first defined.
    entries: Vec<(String, Term)>,
    /// Where each name is in `entries`.
    index: HashMap<String, usize>,
}

impl Definitions {
    /// No definitions.
    pub fn new() -> Definitions {
        Definitions::default()
    }

    /// The term `name` stands for, if it is defined.
    pub fn get(&self, name: &str) -> Option<&Term> {
        self.index.get(name).map(|&at| &self.entries[at].1)
    }

    /// Defines `name`, replacing any earlier definition of it.
    ///
    /// The term must be closed, as the terms [`statement`] gives are: a de
    /// Bruijn index that points out of it would be captured where the name
    /// is used.
    ///
    /// [`statement`]: Definitions::statement
    pub fn define(&mut self, name: impl Into<String>, term: Term) {
        let name = name.into();
        match self.index.get(&name) {
            Some(&at) => self.entries[at].1 = term,
            None => {
                self.index.insert(name.clone(), self.entries.len());
                self.entries.push((name, term));
            }
        }
    }

    /// The definitions, in the order the names were first defined.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &Term)> {
        self.entries
            .iter()
            .map(|(name, term)| (name.as_str(), term))
    }

    /// The number of names defined.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether nothing is defined.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Parses a term, expanding the defined names.
    pub fn parse(&self, source: &str) -> Result<Term, ParseError> {
        parse_with(source, &|name| self.get(name).cloned())
    }

    /// Parses a statement, expanding the defined names. Returns `None` for a
    /// statement that holds nothing but blanks and comments.
    pub fn statement(&self, source: &str) -> Result<Option<Statement>, ParseError> {
        let code = blank_comments(source);
        if code.trim().is_empty() {
            return Ok(None);
        }
        let Some(sign) = code.find('=') else {
            return self.parse(&code).map(Statement::Evaluate).map(Some);
        };
        let name = code[..sign].trim();
        if !is_name(name) {
            return Err(ParseError {
                offset: code.len() - code.trim_start().len(),
                message: format!("expected a name before `=`, found `{name}`"),
            });
        }
        let body = sign + 1;
        let term = self.parse(&code[body..]).map_err(|error| ParseError {
            offset: error.offset + body,
            message: error.message,
        })?;
        Ok(Some(Statement::Define(name.to_owned(), term)))
    }

    /// Loads a script: defines what it defines, and returns the terms it
    /// asks to evaluate, in order. Stops at the first statement that does
    /// not parse, with the definitions before it made.
    pub fn load(&mut self, script: &str) -> Result<Vec<Term>, ScriptError> {
        let mut terms = Vec::new();
        for (line, source) in statements(script) {
            match self.statement(source) {
                Ok(None) => {}
                Ok(Some(Statement::Define(name, term))) => self.define(name, term),
                Ok(Some(Statement::Evaluate(term))) => terms.push(term),
                Err(error) => return Err(ScriptError::new(line, source, error)),
            }
        }
        Ok(terms)
    }
}

/// Replaces every comment by spaces, which keeps all offsets intact.
fn blank_comments(source: &str) -> String {
    let mut code = String::with_capacity(source.len());
    for line in source.split_inclusive('\n') {
        match line.find("--") {
            Some(start) => {
                code.push_str(&line[..start]);
                let comment = line[start..].trim_end_matches('\n');
                code.extend(std::iter::repeat_n(' ', comment.len()));
                code.push_str(&line[start + comment.len()..]);
            }
            None => code.push_str(line),
        }
    }
    code
}

/// Splits a script into statements, each with the number of the line it
/// starts on, counting from 1.
///
/// A statement starts on a line that begins in the first column and runs over
/// the indented lines, the empty lines and the lines holding only a comment
/// that follow.
pub fn statements(script: &str) -> Vec<(usize, &str)> {
    let mut found: Vec<(usize, std::ops::Range<usize>)> = Vec::new();
    let mut offset = 0;
    for (number, line) in script.split_inclusive('\n').enumerate() {
        let end = offset + line.len();
        let code = line.trim();
        let continues = line.starts_with([' ', '\t']) || code.is_empty() || code.starts_with("--");
        match found.last_mut() {
            Some((_, range)) if continues => range.end = end,
            _ => found.push((number + 1, offset..end)),
        }
        offset = end;
    }
    found
        .into_iter()
        .map(|(line, range)| (line, &script[range]))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    #[test]
    fn definitions_expand_in_later_statements() {
        let mut definitions = Definitions::new();
        let Ok(Some(Statement::Define(name, term))) = definitions.statement(r"id = \x. x") else {
            panic!("expected a definition");
        };
        assert_eq!(name, "id");
        definitions.define(name, term);
        assert_eq!(
            definitions.statement("id id"),
            Ok(Some(Statement::Evaluate(
                parse(r"(\x. x) (\x. x)").unwrap()
            )))
        );
    }

    #[test]
    fn loading_a_script_defines_and_collects_the_terms() {
        let mut definitions = Definitions::new();
        let script = "-- two, twice\ntwo = \\f x.\n  f (f x)\ntwo\nfour = two two\nfour a\n";
        let terms = definitions.load(script).unwrap();
        assert_eq!(terms.len(), 2);
        assert_eq!(terms[0], Term::church(2));
        assert_eq!(definitions.len(), 2);
        assert_eq!(definitions.load("-- nothing\n"), Ok(Vec::new()));
    }

    #[test]
    fn loading_stops_at_an_error_and_says_where_it_is() {
        let mut definitions = Definitions::new();
        let error = definitions
            .load("id = \\x. x\ntwo = \\f x.\n  f (f x))\nlater = id\n")
            .unwrap_err();
        assert_eq!((error.line, error.column), (3, 10));
        assert_eq!(error.to_string(), "line 3, column 10: unexpected `)`");
        // What came before the error is defined, what comes after is not.
        let names: Vec<&str> = definitions.iter().map(|(name, _)| name).collect();
        assert_eq!(names, ["id"]);
    }

    #[test]
    fn redefinition_replaces_and_keeps_the_order() {
        let mut definitions = Definitions::new();
        definitions.define("a", Term::church(1));
        definitions.define("b", Term::church(2));
        definitions.define("a", Term::church(3));
        let names: Vec<&str> = definitions.iter().map(|(name, _)| name).collect();
        assert_eq!(names, ["a", "b"]);
        assert_eq!(definitions.get("a"), Some(&Term::church(3)));
        assert_eq!(definitions.len(), 2);
    }

    #[test]
    fn comments_and_blanks_are_not_statements() {
        let definitions = Definitions::new();
        assert_eq!(definitions.statement("   "), Ok(None));
        assert_eq!(definitions.statement("-- x = y"), Ok(None));
        assert_eq!(
            definitions.statement("x -- = y"),
            Ok(Some(Statement::Evaluate(Term::free("x"))))
        );
    }

    #[test]
    fn errors_point_into_the_statement() {
        let definitions = Definitions::new();
        let error = definitions.statement("two = (x").unwrap_err();
        assert_eq!(error.offset, 8);
        let error = definitions.statement("-- note\ntwo = )").unwrap_err();
        assert_eq!(error.offset, 14);
        assert!(definitions.statement("a b = c").is_err());
        assert!(definitions.statement("= c").is_err());
        assert_eq!(definitions.statement("\n  1x = c").unwrap_err().offset, 3);
    }

    #[test]
    fn a_comment_does_not_end_a_statement() {
        let script = "two = \\f x.\n-- twice\n  f (f x)\n-- and now\nthree = 3\n";
        let found = statements(script);
        let lines: Vec<usize> = found.iter().map(|(line, _)| *line).collect();
        assert_eq!(lines, [1, 5]);
        let definitions = Definitions::new();
        assert_eq!(
            definitions.statement(found[0].1),
            Ok(Some(Statement::Define("two".to_owned(), Term::church(2))))
        );
        // A comment before the first statement stands alone.
        assert_eq!(statements("-- intro\nx\n").len(), 2);
    }

    #[test]
    fn long_chains_of_definitions_stay_small() {
        // Each name uses the one before twice. Expanded as trees these would
        // be 2^60 nodes, but the uses share one term.
        let mut definitions = Definitions::new();
        definitions.define("d0", Term::lam("x", Term::Var(0)));
        for n in 1..=60 {
            let source = format!("d{n} = d{} d{}", n - 1, n - 1);
            let Ok(Some(Statement::Define(name, term))) = definitions.statement(&source) else {
                panic!("expected a definition");
            };
            definitions.define(name, term);
        }
        assert_eq!(definitions.len(), 61);
    }

    #[test]
    fn statements_continue_on_indented_lines() {
        let script =
            "-- prelude\nid = \\x. x\n\ntwo = \\f x.\n  f (f x)\n\n  -- still two\ntwo id\n";
        let found = statements(script);
        let lines: Vec<usize> = found.iter().map(|(line, _)| *line).collect();
        assert_eq!(lines, [1, 2, 4, 8]);
        assert_eq!(found[1].1, "id = \\x. x\n\n");
        assert_eq!(found[2].1, "two = \\f x.\n  f (f x)\n\n  -- still two\n");
        assert_eq!(found[3].1, "two id\n");
        assert!(statements("").is_empty());
    }
}
