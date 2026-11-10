//! `levy`: a REPL for Lévy-optimal λ-calculus reduction.

mod session;

use std::process::ExitCode;
use std::thread;

use rustyline::DefaultEditor;
use rustyline::error::ReadlineError;

use session::Session;

/// Stack of the thread that does the work.
///
/// Terms are trees handled by recursion, and a Church numeral nests as deep
/// as its value, so the default stack is far too small for honest arithmetic.
/// The memory is only reserved, not used, until the depth is reached.
const STACK_BYTES: usize = 1 << 30;

const USAGE: &str = "\
Usage: levy [OPTIONS] [FILE]...

Loads the given files, then reads statements from the prompt.

Options:
  -e, --eval TERM   evaluate TERM after loading the files, then exit
  -h, --help        show this text";

/// What the command line asks for.
#[derive(Debug, Default, PartialEq, Eq)]
struct Options {
    files: Vec<String>,
    eval: Vec<String>,
    help: bool,
}

fn options(arguments: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let mut options = Options::default();
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "-h" | "--help" => options.help = true,
            "-e" | "--eval" => {
                let term = arguments
                    .next()
                    .ok_or_else(|| format!("`{argument}` needs a term"))?;
                options.eval.push(term);
            }
            flag if flag.starts_with('-') => return Err(format!("unknown option `{flag}`")),
            _ => options.files.push(argument),
        }
    }
    Ok(options)
}

fn print(lines: &[String]) {
    for line in lines {
        println!("{line}");
    }
}

fn run(options: Options) -> rustyline::Result<()> {
    let mut session = Session::new();
    for file in &options.files {
        print(&session.execute(&format!(":load {file}")).lines);
    }
    if !options.eval.is_empty() {
        for term in &options.eval {
            print(&session.execute(term).lines);
        }
        return Ok(());
    }

    println!("levy: optimal λ-reduction. `:help` lists the commands.");
    let mut editor = DefaultEditor::new()?;
    loop {
        match editor.readline("λ> ") {
            Ok(line) => {
                if !line.trim().is_empty() {
                    editor.add_history_entry(line.as_str())?;
                }
                let reply = session.execute(&line);
                print(&reply.lines);
                if reply.quit {
                    return Ok(());
                }
            }
            Err(ReadlineError::Interrupted) => {}
            Err(ReadlineError::Eof) => return Ok(()),
            Err(error) => return Err(error),
        }
    }
}

fn main() -> ExitCode {
    let options = match options(std::env::args().skip(1)) {
        Ok(options) => options,
        Err(message) => {
            eprintln!("levy: {message}\n\n{USAGE}");
            return ExitCode::FAILURE;
        }
    };
    if options.help {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let worker = thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(move || run(options));
    let outcome = match worker {
        Ok(worker) => worker.join(),
        Err(error) => {
            eprintln!("levy: cannot start the worker thread: {error}");
            return ExitCode::FAILURE;
        }
    };
    match outcome {
        Ok(Ok(())) => ExitCode::SUCCESS,
        Ok(Err(error)) => {
            eprintln!("levy: {error}");
            ExitCode::FAILURE
        }
        Err(panic) => std::panic::resume_unwind(panic),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(arguments: &[&str]) -> Result<Options, String> {
        options(arguments.iter().map(|argument| (*argument).to_owned()))
    }

    #[test]
    fn reads_files_and_terms() {
        let options = parse(&["a.lam", "-e", "2 2", "b.lam"]).unwrap();
        assert_eq!(options.files, ["a.lam", "b.lam"]);
        assert_eq!(options.eval, ["2 2"]);
        assert!(!options.help);
    }

    #[test]
    fn rejects_bad_options() {
        assert!(parse(&["--eval"]).is_err());
        assert!(parse(&["--frobnicate"]).is_err());
        assert!(parse(&["--help"]).unwrap().help);
    }
}
