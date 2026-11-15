//! `levy`: a REPL for Lévy-optimal λ-calculus reduction.

mod session;

use std::io::{self, BufRead, IsTerminal, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use rustyline::DefaultEditor;
use rustyline::error::ReadlineError;

use session::{Outcome, Output, Session};

const USAGE: &str = "\
Usage: levy [OPTIONS] [FILE]...

Loads the given files, then reads statements from the prompt.

Options:
  -e, --eval TERM   evaluate TERM after loading the files, then exit
  -h, --help        show this text

With `-e`, or when standard input is not a terminal, nothing is asked: the
statements are run and the exit status tells whether all of them worked.";

/// The exit status of a run that Ctrl-C put an end to, as shells report it.
const INTERRUPTED: u8 = 130;

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

/// Results go to standard output and remarks to standard error.
#[derive(Default)]
struct Console {
    /// Whether standard output is gone, as when `levy ... | head` has read
    /// enough.
    closed: bool,
}

impl Output for Console {
    fn line(&mut self, text: &str) {
        if !self.closed && writeln!(io::stdout().lock(), "{text}").is_err() {
            self.closed = true;
        }
    }

    fn remark(&mut self, text: &str) {
        // Nothing can be done about a standard error that is gone.
        let _ = writeln!(io::stderr().lock(), "{text}");
    }

    fn is_closed(&self) -> bool {
        self.closed
    }
}

/// A session, where it writes, and how its inputs have fared.
struct Runner {
    session: Session,
    console: Console,
    /// Set by Ctrl-C while an evaluation runs.
    interrupt: Arc<AtomicBool>,
    failed: bool,
}

impl Runner {
    fn new() -> Runner {
        let interrupt = Arc::new(AtomicBool::new(false));
        let flag = Arc::clone(&interrupt);
        // If the handler cannot be set, Ctrl-C ends the process as usual.
        let _ = ctrlc::set_handler(move || flag.store(true, Ordering::Relaxed));
        Runner {
            session: Session::new(Arc::clone(&interrupt)),
            console: Console::default(),
            interrupt,
            failed: false,
        }
    }

    fn note(&mut self, outcome: Outcome) -> Outcome {
        self.failed |= outcome.failed;
        outcome
    }

    fn load(&mut self, path: &str) -> Outcome {
        let outcome = self.session.load(path, &mut self.console);
        self.note(outcome)
    }

    fn feed(&mut self, input: &str) -> Outcome {
        let outcome = self.session.execute(input, &mut self.console);
        self.note(outcome)
    }

    /// Whether a run that asks nothing should end here.
    fn is_over(&self, outcome: Outcome) -> bool {
        outcome.quit || self.console.closed || self.interrupt.load(Ordering::Relaxed)
    }

    /// The exit status of a run that asks nothing.
    fn status(&self) -> ExitCode {
        if self.interrupt.load(Ordering::Relaxed) {
            ExitCode::from(INTERRUPTED)
        } else if self.failed && !self.console.closed {
            ExitCode::FAILURE
        } else {
            ExitCode::SUCCESS
        }
    }
}

/// Where the lines typed at the prompt are kept between sessions.
fn history_file() -> Option<PathBuf> {
    let set = |name: &str| std::env::var_os(name).filter(|value| !value.is_empty());
    let state = set("XDG_STATE_HOME")
        .map(PathBuf::from)
        .or_else(|| Some(PathBuf::from(set("HOME")?).join(".local").join("state")))?;
    Some(state.join("levy").join("history"))
}

fn interact(runner: &mut Runner) -> rustyline::Result<()> {
    println!("levy: optimal λ-reduction. `:help` lists the commands.");
    let mut editor = DefaultEditor::new()?;
    let history = history_file();
    if let Some(path) = &history {
        // There is none on the first run.
        let _ = editor.load_history(path);
    }
    let outcome = loop {
        match editor.readline("λ> ") {
            Ok(line) => {
                if !line.trim().is_empty() {
                    editor.add_history_entry(line.as_str())?;
                }
                // Ctrl-C stops the evaluation it is pressed during, no other.
                runner.interrupt.store(false, Ordering::Relaxed);
                if runner.feed(&line).quit || runner.console.closed {
                    break Ok(());
                }
            }
            Err(ReadlineError::Interrupted) => {}
            Err(ReadlineError::Eof) => break Ok(()),
            Err(error) => break Err(error),
        }
    };
    if let Some(path) = &history {
        // Losing the history is not worth a complaint on the way out.
        if let Some(directory) = path.parent() {
            let _ = std::fs::create_dir_all(directory);
        }
        let _ = editor.save_history(path);
    }
    outcome
}

fn run(options: &Options) -> ExitCode {
    let mut runner = Runner::new();
    let asks = options.eval.is_empty() && io::stdin().is_terminal();
    for file in &options.files {
        let outcome = runner.load(file);
        if !asks && runner.is_over(outcome) {
            return runner.status();
        }
    }
    if !options.eval.is_empty() {
        for term in &options.eval {
            let outcome = runner.feed(term);
            if runner.is_over(outcome) {
                break;
            }
        }
        return runner.status();
    }
    if !asks {
        for line in io::stdin().lock().lines() {
            let line = match line {
                Ok(line) => line,
                Err(error) => {
                    eprintln!("levy: cannot read standard input: {error}");
                    return ExitCode::FAILURE;
                }
            };
            let outcome = runner.feed(&line);
            if runner.is_over(outcome) {
                break;
            }
        }
        return runner.status();
    }
    match interact(&mut runner) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("levy: {error}");
            ExitCode::FAILURE
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
    run(&options)
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
