# levy

An interpreter for the untyped λ-calculus that reduces terms optimally in
Lévy's sense: every family of redexes is contracted exactly once, however many
copies of it ordinary reduction would create. It comes with a REPL and a web
page that steps through the reduction one graph rewrite at a time.

```
λ> :compare 2 2 2 2 id id
λx. x
optimal:      27 β-steps, 1151 bookkeeping steps
normal order: 258294 β-steps in 27 families
```

(`id` is `\x. x`, from `examples/prelude.lam`.)

## Layout

| Path | What it is |
|---|---|
| `crates/core` | The engine: terms, parser, nets, rules, machine, readback, garbage collection. No dependencies. |
| `crates/repl` | The `levy` binary. |
| `crates/web` | WebAssembly bindings for the stepper. |
| `web/` | The page that draws the nets. |
| `examples/prelude.lam` | Church encodings to play with. |

## REPL

```
cargo run --release -p levy -- examples/prelude.lam
```

Enter a term to reduce it, or `name = term` to define a name.

```
λ> fact 4
λ> :compare fib 12      -- optimal versus normal order
λ> :trace (\f. f (f a)) (\x. (\y. y) x)
λ> :help
```

Syntax: `\x. body` or `λx. body`, application by juxtaposition, numbers up to
10000 for Church numerals, `--` for comments. Definitions are expanded when a
term is parsed, so recursion needs a fixed-point combinator, and a name used
before it is defined stays a free variable. The REPL says so when it happens.

Ctrl-C stops an evaluation and keeps the session. So does the fuel limit,
which bounds the work of one evaluation, and with it its time and memory:
`:fuel` shows it and `:fuel N` sets it. History is kept in
`$XDG_STATE_HOME/levy/history`, or `~/.local/state/levy/history`.

In a file, a statement runs on over the indented lines that follow it.
`:load` reports a bad statement with its line and column and goes on with
the next one.

With `-e TERM`, or when standard input is not a terminal, nothing is asked:
results go to standard output, errors to standard error, and the exit status
is nonzero if a statement failed.

```
levy examples/prelude.lam -e 'fact 5' -e ':compare fib 10'
```

## Web page

Building it needs the `wasm32-unknown-unknown` target and `wasm-pack`:

```
rustup target add wasm32-unknown-unknown
cargo install wasm-pack
scripts/build-web.sh
python3 -m http.server --directory web 8000
```

Then open <http://localhost:8000>. The page shows the net, the term it stands
for, the pair of nodes about to interact, and counters. Arrow keys step
forwards and backwards, space plays, `b` runs to the next β-step and `f` fits
the net in view. Ctrl+Enter in the script loads it. Finish and Next β can be
stopped by pressing them again. Scroll or pinch to zoom, drag to pan.

## How it works

The algorithm is Lambdascope (van Oostrom, van de Looij and Zwitserlood,
2004), the smallest known formulation of optimal reduction as an interaction
net.

1. **Translation** (`translate.rs`). Abstractions and applications become
   nodes. A variable occurrence is a wire to its binder that passes one
   *delimiter* per abstraction it leaves. A variable used several times is
   shared by *fans*.
2. **Rules** (`rules.rs`). Two nodes interact when their principal ports face
   each other. *Beta* removes an application and its abstraction and leaves
   two delimiters around the former body. Fans and delimiters of equal level
   *annihilate*; a delimiter that reaches the root or a free variable
   *dissolves*; any other pair with a fan or a delimiter in it *commutes*,
   each node copying the other, with levels adjusted like de Bruijn indices.
   One delimiter node stands for a whole stack of delimiters of the same
   level, so that they move together.
3. **Strategy** (`machine.rs`). The machine walks the net as one reads a term,
   head first, and rewrites only the active pairs on its way. That is
   leftmost-outermost order, so redexes nothing needs are never touched, and a
   diverging argument that is discarded costs nothing. The walk keeps its
   place between steps, so stepping costs no more than running, and it pays
   one unit of fuel per node it comes to, which is what bounds a reduction
   that does not end.
4. **Readback** (`context.rs`, `machine.rs`). The same walk without rewriting
   turns a net back into a term at any point. It carries a context that
   records which fan branch it came through and which scopes it has left.
5. **Garbage collection** (`gc.rs`). Whatever a reading from the root cannot
   reach is removed.

## How it is checked

`reference.rs` is a plain normal-order reducer over Lévy-labelled terms. It
gives the normal form and the number of redex families, which is the number of
β-steps an optimal reducer must take. The tests in
`crates/core/tests/differential.rs` compare the machine with it on every
closed term up to 10 nodes, on 63,000 random terms of 10 to 200 nodes, with
and without free variables, and on a corpus of classic examples written with
the prelude. They require equal normal forms and exactly one beta interaction
per family. They also check that

- no rule other than beta changes the term a net stands for, watching every
  kind of interaction at least twenty times;
- a reduction gives the same result and the same counts whether it runs in
  one go, one interaction at a time, in batches, in slices of fuel, or with
  garbage collected after every interaction;
- a term without a normal form stops at the fuel limit.

```
cargo test --release
```

The random terms come from a fixed seed. `LEVY_TEST_SEED=7 cargo test` tries
others.

## Limitations

- **Optimal in β-steps, not in time.** The bookkeeping that keeps sharing
  correct dominates: `fib 20` takes 283 β-steps and 635,474 bookkeeping
  interactions. Stacked delimiters are merged, which cuts that work by up to
  three (2.4 on `fib 20`, little where few delimiters pile up), but the other
  known remedies (safe fans, garbage collection of fans with a dead branch)
  are not implemented. On ordinary programs a conventional lazy evaluator is
  much faster; this one wins only when sharing under binders matters.
- **A step of the walk costs more the deeper the scopes nest.** The context
  the walk carries is a list with one entry per scope, and a fan or a
  delimiter of level `n` rebuilds `n` entries of it. `fact 8` takes 26 s for
  467,225 bookkeeping interactions where `fib 20` takes half a second for
  more. A context with cheap access in the middle would fix that.
- **Normal forms stay shared.** The net of a normal form can hold fans and
  delimiters that nothing will ever move. Reading it back gives the plain
  term, but the picture of it is larger than the term.
- **A large result needs fuel.** Reading a result costs one unit of fuel per
  node, and the REPL allows 100 million units, a few seconds, per
  evaluation. A result of 50 million nodes needs `:fuel` raised, and about
  75 bytes of memory per node.
- **Sequential.** Reducing active pairs in parallel would contract redexes
  that are not needed and lose optimality.
- **Family counts are fingerprints.** The reference reducer hashes Lévy labels
  instead of storing them, so the count it reports could in principle be off
  by a collision. The odds are negligible.
- **The page draws up to 700 nodes.** Larger nets can still be stepped, with
  the term and the counters as the only feedback.

## References

- J.-J. Lévy, *Réductions correctes et optimales dans le lambda-calcul*, 1978.
- J. Lamping, *An algorithm for optimal lambda calculus reduction*, POPL 1990.
- A. Asperti and S. Guerrini, *The Optimal Implementation of Functional
  Programming Languages*, Cambridge University Press, 1998.
- V. van Oostrom, K.-J. van de Looij and M. Zwitserlood, *Lambdascope: another
  optimal implementation of the lambda-calculus*, 2004.
