//! Parser for the surface syntax.
//!
//! ```text
//! term        ::= abstraction | application
//! abstraction ::= ("λ" | "\") name+ "." term
//! application ::= atom+ abstraction?
//! atom        ::= name | numeral | "(" term ")"
//! ```
//!
//! A numeral stands for the corresponding Church numeral. `--` starts a
//! comment that runs to the end of the line.

use std::collections::HashMap;
use std::fmt;

use crate::term::Term;

/// The largest numeral literal the parser expands.
pub const MAX_NUMERAL: u64 = 10_000;

/// Why a source text is not a term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    /// Byte offset into the source where the problem was found.
    pub offset: usize,
    /// What was expected or what is wrong, without the place.
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at byte {}", self.message, self.offset)
    }
}

impl std::error::Error for ParseError {}

/// Parses a term. Names that no binder captures become free variables.
pub fn parse(source: &str) -> Result<Term, ParseError> {
    parse_with(source, &|_| None)
}

/// Parses a term, replacing each name that no binder captures by the term
/// `definition` gives for it, if any.
///
/// The terms `definition` gives must be closed: a de Bruijn index that
/// points out of one would be captured by the binders around the name.
pub fn parse_with(
    source: &str,
    definition: &dyn Fn(&str) -> Option<Term>,
) -> Result<Term, ParseError> {
    let mut parser = Parser {
        tokens: lex(source)?,
        position: 0,
        scope: Vec::new(),
        bound: HashMap::new(),
        definition,
    };
    parser.term()
}

/// The line and the column of a byte offset into `source`, both counted
/// from 1, the column in characters.
pub fn position(source: &str, offset: usize) -> (usize, usize) {
    let before = &source[..offset.min(source.len())];
    let line_start = before.rfind('\n').map_or(0, |newline| newline + 1);
    let line = before.matches('\n').count() + 1;
    let column = before[line_start..].chars().count() + 1;
    (line, column)
}

/// Whether `text` can be used as a name.
pub fn is_name(text: &str) -> bool {
    let mut chars = text.chars();
    chars.next().is_some_and(is_name_start) && chars.all(is_name_part)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Lambda,
    Dot,
    Open,
    Close,
    Name(String),
    Numeral(u64),
    End,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Lambda => f.write_str("`λ`"),
            Token::Dot => f.write_str("`.`"),
            Token::Open => f.write_str("`(`"),
            Token::Close => f.write_str("`)`"),
            Token::Name(name) => write!(f, "name `{name}`"),
            Token::Numeral(value) => write!(f, "numeral `{value}`"),
            Token::End => f.write_str("end of input"),
        }
    }
}

fn is_name_start(c: char) -> bool {
    (c.is_alphabetic() && c != 'λ') || c == '_'
}

fn is_name_part(c: char) -> bool {
    is_name_start(c) || c.is_numeric() || c == '\''
}

fn lex(source: &str) -> Result<Vec<(usize, Token)>, ParseError> {
    let mut tokens = Vec::new();
    let mut chars = source.char_indices().peekable();
    while let Some(&(offset, c)) = chars.peek() {
        let token = match c {
            _ if c.is_whitespace() => {
                chars.next();
                continue;
            }
            '-' if source[offset..].starts_with("--") => {
                while chars.next_if(|&(_, c)| c != '\n').is_some() {}
                continue;
            }
            'λ' | '\\' => Token::Lambda,
            '.' => Token::Dot,
            '(' => Token::Open,
            ')' => Token::Close,
            _ if c.is_ascii_digit() => {
                let mut end = offset;
                while let Some((at, c)) = chars.next_if(|&(_, c)| c.is_ascii_digit()) {
                    end = at + c.len_utf8();
                }
                let value = source[offset..end]
                    .parse()
                    .ok()
                    .filter(|&value| value <= MAX_NUMERAL)
                    .ok_or_else(|| ParseError {
                        offset,
                        message: format!("numeral is larger than {MAX_NUMERAL}"),
                    })?;
                // `1x` is more likely a slip for `x1` than the numeral 1
                // applied to `x`.
                if let Some(&(at, c)) = chars.peek()
                    && is_name_part(c)
                {
                    return Err(ParseError {
                        offset: at,
                        message: format!("expected a space between the numeral and `{c}`"),
                    });
                }
                tokens.push((offset, Token::Numeral(value)));
                continue;
            }
            _ if is_name_start(c) => {
                let mut end = offset;
                while let Some((at, c)) = chars.next_if(|&(_, c)| is_name_part(c)) {
                    end = at + c.len_utf8();
                }
                tokens.push((offset, Token::Name(source[offset..end].to_owned())));
                continue;
            }
            _ => {
                return Err(ParseError {
                    offset,
                    message: format!("unexpected character `{c}`"),
                });
            }
        };
        chars.next();
        tokens.push((offset, token));
    }
    tokens.push((source.len(), Token::End));
    Ok(tokens)
}

/// What a group of juxtaposed terms is enclosed by.
enum Enclosure {
    /// Nothing: the group is the whole source.
    Source,
    Parentheses,
    /// The group is the body of an abstraction, which found this many names
    /// in scope before its own.
    Abstraction(usize),
}

/// A group of juxtaposed terms that is still being read.
struct Group {
    enclosure: Enclosure,
    /// The application of the terms read so far.
    term: Option<Term>,
}

impl Group {
    fn new(enclosure: Enclosure) -> Group {
        Group {
            enclosure,
            term: None,
        }
    }

    /// Adds one more term to the group.
    fn apply(&mut self, argument: Term) {
        self.term = Some(match self.term.take() {
            Some(func) => Term::app(func, argument),
            None => argument,
        });
    }
}

struct Parser<'a> {
    tokens: Vec<(usize, Token)>,
    position: usize,
    /// Names of the enclosing binders, innermost last.
    scope: Vec<String>,
    /// For each name, the places in `scope` of the binders that bind it,
    /// innermost last. A name is looked up here, not searched for in
    /// `scope`, which would take time in proportion to the depth.
    bound: HashMap<String, Vec<usize>>,
    definition: &'a dyn Fn(&str) -> Option<Term>,
}

impl Parser<'_> {
    fn peek(&self) -> &Token {
        &self.tokens[self.position].1
    }

    /// Moves on to the next token. The end of the input is never passed.
    fn advance(&mut self) {
        if *self.peek() != Token::End {
            self.position += 1;
        }
    }

    fn error(&self, message: String) -> ParseError {
        ParseError {
            offset: self.tokens[self.position].0,
            message,
        }
    }

    /// Parses a term that runs to the end of the source.
    ///
    /// Source can be nested deeper than any call stack, so the groups that
    /// are still open are kept in a list, not in recursive calls.
    fn term(&mut self) -> Result<Term, ParseError> {
        let mut outer: Vec<Group> = Vec::new();
        let mut group = Group::new(Enclosure::Source);
        loop {
            match self.peek().clone() {
                Token::Lambda => {
                    let depth = self.binders()?;
                    outer.push(std::mem::replace(
                        &mut group,
                        Group::new(Enclosure::Abstraction(depth)),
                    ));
                }
                Token::Open => {
                    self.advance();
                    outer.push(std::mem::replace(
                        &mut group,
                        Group::new(Enclosure::Parentheses),
                    ));
                }
                Token::Name(name) => {
                    self.advance();
                    group.apply(self.resolve(name));
                }
                Token::Numeral(value) => {
                    self.advance();
                    group.apply(Term::church(value));
                }
                token => {
                    // Nothing here goes on with the group, so it is complete.
                    // An abstraction reaches as far as it can: what ends its
                    // body ends the group around it as well.
                    loop {
                        let Some(term) = group.term.take() else {
                            return Err(self.error(format!("expected a term, found {token}")));
                        };
                        let closed = match group.enclosure {
                            Enclosure::Source if token == Token::End => return Ok(term),
                            Enclosure::Source => {
                                return Err(self.error(format!("unexpected {token}")));
                            }
                            Enclosure::Abstraction(depth) => self.close(depth, term),
                            Enclosure::Parentheses if token == Token::Close => {
                                self.advance();
                                term
                            }
                            Enclosure::Parentheses => {
                                return Err(self.error(format!("expected `)`, found {token}")));
                            }
                        };
                        let parenthesized = matches!(group.enclosure, Enclosure::Parentheses);
                        group = outer.pop().expect("only the source has no group around it");
                        group.apply(closed);
                        if parenthesized {
                            break;
                        }
                    }
                }
            }
        }
    }

    /// Reads `λ`, the binder names and the dot, and brings the names into
    /// scope. Returns how many names were in scope before.
    fn binders(&mut self) -> Result<usize, ParseError> {
        self.advance();
        let depth = self.scope.len();
        while let Token::Name(name) = self.peek() {
            let name = name.clone();
            self.bound
                .entry(name.clone())
                .or_default()
                .push(self.scope.len());
            self.scope.push(name);
            self.advance();
        }
        if self.scope.len() == depth {
            return Err(self.error(format!("expected a binder name, found {}", self.peek())));
        }
        if *self.peek() != Token::Dot {
            return Err(self.error(format!("expected `.`, found {}", self.peek())));
        }
        self.advance();
        Ok(depth)
    }

    /// Closes the binders brought into scope beyond the first `depth` around
    /// `body`, the innermost first.
    fn close(&mut self, depth: usize, body: Term) -> Term {
        let names = self.scope.split_off(depth);
        for name in &names {
            if let Some(places) = self.bound.get_mut(name) {
                places.pop();
            }
        }
        names
            .into_iter()
            .rev()
            .fold(body, |body, name| Term::lam(name, body))
    }

    fn resolve(&self, name: String) -> Term {
        if let Some(&place) = self.bound.get(&name).and_then(|places| places.last()) {
            Term::Var(self.scope.len() - 1 - place)
        } else if let Some(term) = (self.definition)(&name) {
            term
        } else {
            Term::Free(name)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_binders_and_applications() {
        let term = parse(r"\f x. f (f x)").unwrap();
        assert_eq!(term, Term::church(2));
        assert_eq!(parse("λf. λx. f (f x)").unwrap(), term);
    }

    #[test]
    fn application_associates_to_the_left() {
        let term = parse("a b c").unwrap();
        let expected = Term::app(Term::app(Term::free("a"), Term::free("b")), Term::free("c"));
        assert_eq!(term, expected);
    }

    #[test]
    fn trailing_abstraction_needs_no_parentheses() {
        assert_eq!(parse(r"f \x. x y").unwrap(), parse(r"f (\x. x y)").unwrap());
    }

    #[test]
    fn inner_binders_shadow_outer_ones() {
        let term = parse(r"\x. \x. x").unwrap();
        assert_eq!(term, Term::lam("x", Term::lam("x", Term::Var(0))));
        // Out of its abstraction, a name is free again.
        let term = parse(r"(\x. \x y. x) x").unwrap();
        let inner = Term::lam("x", Term::lam("y", Term::Var(1)));
        assert_eq!(term, Term::app(Term::lam("x", inner), Term::free("x")));
    }

    #[test]
    fn names_are_found_however_deep_their_binder() {
        // An outer binder used many times under many binders of another
        // name. Searching the scope at every use would take minutes.
        let depth = 100_000;
        let source = format!(r"\a. {}{}", r"\x. ".repeat(depth), "a ".repeat(depth));
        let uses = (1..depth).fold(Term::Var(depth), |func, _| {
            Term::app(func, Term::Var(depth))
        });
        let body = (0..depth).fold(uses, |body, _| Term::lam("x", body));
        assert_eq!(parse(&source).unwrap(), Term::lam("a", body));
    }

    #[test]
    fn numerals_and_comments() {
        assert_eq!(parse("3 -- three\n").unwrap(), Term::church(3));
        assert!(parse("99999999999").is_err());
    }

    #[test]
    fn definitions_replace_unbound_names_only() {
        let id = Term::lam("x", Term::Var(0));
        let lookup = |name: &str| (name == "id").then(|| id.clone());
        assert_eq!(
            parse_with("id y", &lookup).unwrap(),
            Term::app(id.clone(), Term::free("y"))
        );
        assert_eq!(
            parse_with(r"\id. id", &lookup).unwrap(),
            Term::lam("id", Term::Var(0))
        );
    }

    #[test]
    fn printed_terms_parse_back() {
        for source in [
            r"\x. x",
            r"\f x. f (f x)",
            r"(\x. x x) (\x. x x)",
            r"\x. \y. x (\z. z y) w",
            r"(\x. \x. x) a",
        ] {
            let term = parse(source).unwrap();
            assert_eq!(parse(&term.to_string()).unwrap(), term, "{source}");
        }
    }

    #[test]
    fn numerals_do_not_run_into_names() {
        let error = parse("1x").unwrap_err();
        assert_eq!(error.offset, 1);
        assert!(parse("2x y").is_err());
        assert!(parse("3'").is_err());
        assert_eq!(parse("2(x)").unwrap(), parse("2 x").unwrap());
        assert_eq!(parse("x1").unwrap(), Term::free("x1"));
    }

    #[test]
    fn deep_nesting_needs_no_deep_stack() {
        let depth = 200_000;
        let parentheses = format!("{}x{}", "(".repeat(depth), ")".repeat(depth));
        assert_eq!(parse(&parentheses).unwrap(), Term::free("x"));
        let binders = format!("{}x", r"\x. ".repeat(depth));
        assert_eq!(parse(&binders).unwrap().size(), depth + 1);
        let arguments = format!("{}x{}", "f (".repeat(depth), ")".repeat(depth));
        assert_eq!(parse(&arguments).unwrap().size(), 2 * depth + 1);
        // The printed form of a deep term reads back as the same term.
        let numeral = Term::church(100_000);
        assert_eq!(parse(&numeral.to_string()).unwrap(), numeral);
    }

    #[test]
    fn abstractions_reach_as_far_as_they_can() {
        assert_eq!(
            parse(r"(\x. x \y. y x) z").unwrap(),
            parse(r"(\x. (x (\y. (y x)))) z").unwrap()
        );
        assert_eq!(
            parse(r"\x. \y. x y").unwrap(),
            parse(r"\x. (\y. (x y))").unwrap()
        );
        for (source, offset) in [
            ("()", 1),
            (r"\x.", 3),
            (r"(\x. )", 5),
            (r"\x y", 4),
            ("x . y", 2),
        ] {
            assert_eq!(parse(source).unwrap_err().offset, offset, "{source}");
        }
    }

    #[test]
    fn finds_lines_and_columns() {
        assert_eq!(position("abc", 0), (1, 1));
        assert_eq!(position("abc", 2), (1, 3));
        assert_eq!(position("a\nλx. y", 6), (2, 4));
        assert_eq!(position("a\n", 2), (2, 1));
        assert_eq!(position("a", 99), (1, 2));
    }

    #[test]
    fn recognizes_names() {
        for name in ["x", "x1", "_tmp", "f'", "número"] {
            assert!(is_name(name), "{name}");
        }
        for text in ["", "1x", "a b", "λ", "x.y", "'"] {
            assert!(!is_name(text), "{text}");
        }
    }

    #[test]
    fn reports_errors_with_offsets() {
        assert_eq!(parse("(x").unwrap_err().offset, 2);
        assert_eq!(parse(r"\. x").unwrap_err().offset, 1);
        assert_eq!(parse("x )").unwrap_err().offset, 2);
        assert_eq!(parse("x $").unwrap_err().offset, 2);
        assert!(parse("").is_err());
    }
}
