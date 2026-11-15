# levy

An untyped λ-calculus interpreter that reduces terms optimally in Lévy’s sense: it contracts each family of redexes once, no matter how many copies ordinary reduction would create. It includes a REPL and an interactive web page that shows each graph rewrite step.

```
λ> :compare 2 2 2 2 id id
λx. x
optimal:      27 β-steps, 1151 bookkeeping steps
normal order: 258294 β-steps in 27 families
```

(`id` is `\x. x`, from `examples/prelude.lam`)

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

### Syntax

| Form | Meaning |
|---|---|
| `\x. body` or `λx. body` | abstraction; `\x y. body` binds several names |
| `f a b` | application, associating to the left |
| `3` | the Church numeral for 3, up to 10000 |
| `-- text` | comment |

Definitions are expanded when a term is parsed, so a definition cannot refer to itself: recursion goes through a fixed-point combinator, like `fix` in the prelude. A name used before it is defined stays a free variable, and the REPL points it out.

### Commands

| Command | What it does |
|---|---|
| `:compare TERM` | reduce `TERM` both optimally and in normal order |
| `:trace TERM` | show the term after each β-step, up to 100 of them |
| `:dot TERM` | print the net of `TERM` in Graphviz format |
| `:load FILE` | run the statements of a file |
| `:defs` | list the definitions |
| `:fuel [N]` | show or set the limit on the work of one evaluation |
| `:help`, `:quit` | list the commands, leave |

### Stopping

An evaluation stops when you press Ctrl-C or when it runs out of fuel, and either way the session goes on. Fuel bounds the work, and with it the time and memory, of one evaluation: 100 million steps unless `:fuel` sets another limit.

### Files and scripts

In a file, a statement runs on over the indented lines that follow it. A bad statement is reported with its line and column, and loading goes on with the next one.

With `-e TERM`, or when standard input is not a terminal, nothing is asked: results go to standard output, errors to standard error, and the exit status is nonzero if a statement failed.

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

Then open <http://localhost:8000>. The page shows the net, the term it stands for, the pair of nodes about to interact, and counters. Arrow keys step forwards and backwards, space plays, `b` runs to the next β-step and `f` fits the net in view. Ctrl+Enter in the script loads it, and scripts can use every definition in `examples/prelude.lam`. Finish and Next β can be stopped by pressing them again. Scroll or pinch to zoom, drag to pan.

## How it works

levy follows Lambdascope (van Oostrom, van de Looij and Zwitserlood, 2004), the smallest known way to do optimal reduction with an interaction net. The idea is: turn the term into a graph that stores every shared piece once, rewrite that graph with a handful of local rules, and read a term back out of it whenever you want to look.

1. **Translation** (`translate.rs`). Every abstraction and every application becomes a node, and every variable becomes a wire back to the abstraction that binds it. Each time that wire leaves an abstraction on its way, it passes through a *delimiter*, a node that marks the edge of a scope. A variable used more than once gets *fans*, which split its wire so that all the uses share it.
2. **Rules** (`rules.rs`). Every node has one *principal* port, and two nodes interact only when their principal ports are wired to each other. There are four rules. *Beta* is the real computation: an application meets its abstraction, both disappear, and two delimiters are left around what used to be the body. Two fans, or two delimiters, of the same level *annihilate* each other. A delimiter that reaches the root or a free variable *dissolves*. Any other pair with a fan or a delimiter in it *commutes*: the two nodes pass through each other, each copied once for every auxiliary port of the other, with their levels adjusted much like de Bruijn indices. Delimiters of the same level that pile up are merged into one node, so a whole stack moves in a single step.
3. **Strategy** (`machine.rs`). The machine walks the net the way you would read the term, head first, and rewrites only the interacting pairs it runs into. That is leftmost-outermost order, so a redex nothing needs is never touched, and an argument that would loop forever costs nothing if it is thrown away. The walk remembers where it stopped, so stepping through a reduction costs no more than running it in one go. Every node it visits costs one unit of fuel, which is what stops a reduction that would never end.
4. **Readback** (`context.rs`, `machine.rs`). The same walk, with rewriting turned off, turns the net back into a term at any point. One node can stand for several places in the term, so the walk carries a *context* that remembers which fan branches it came through and which scopes it has left. It only ever goes back to an earlier context in the reverse of the order it reached them, so it keeps a single context, changes it in place, and logs how to undo each change. A step costs about the same however deeply the scopes nest.
5. **Garbage collection** (`gc.rs`). Anything a reading from the root can no longer reach is thrown away.

## How it is checked

levy is tested against a much simpler reducer that is easy to trust. `reference.rs` does plain normal-order reduction on terms that carry Lévy labels, which gives both the normal form and the number of redex families: exactly the number of β-steps an optimal reducer has to take.

`crates/core/tests/differential.rs` runs both of them on every closed term of up to 10 nodes, on 63,000 random terms of 10 to 200 nodes, with and without free variables, and on a set of classic examples written with the prelude. The normal forms have to match, and levy has to fire exactly one beta interaction per family. The tests also check that:

- no rule but beta changes the term a net stands for, with every kind of interaction watched at least twenty times;
- a reduction ends with the same result and the same counts whether it runs in one go, one interaction at a time, in batches, in slices of fuel, or with garbage collected after every interaction;
- a term with no normal form stops at the fuel limit.

```
cargo test --release
```

The random terms come from a fixed seed, so a failure can always be reproduced. To try other terms, set `LEVY_TEST_SEED`, as in `LEVY_TEST_SEED=7 cargo test --release`.

## Limitations

- **Optimal in β-steps, not in time.** Keeping the sharing correct takes a lot of bookkeeping, and the bookkeeping dominates: `fib 20` takes 283 β-steps but 635,474 bookkeeping interactions. Merging stacked delimiters cuts that work by up to a factor of three (2.4 on `fib 20`, much less where few delimiters pile up), but other known remedies, such as safe fans or collecting fans with a dead branch, are not implemented. On everyday programs a conventional lazy evaluator is much faster; levy wins when sharing under binders really matters.
- **Normal forms stay shared.** The net of a normal form can still hold fans and delimiters that will never move again. Reading it back gives the plain term, but the picture on the page is bigger than the term.
- **Big results need fuel.** Reading a result costs one unit of fuel per node, and the REPL allows 100 million of them per evaluation, a few seconds of work. A result of 50 million nodes needs a higher `:fuel`, and about 75 bytes of memory per node.
- **One pair at a time.** Reducing interacting pairs in parallel would contract redexes that are not needed, and optimality would be lost.
- **Family counts are fingerprints.** The reference reducer hashes Lévy labels instead of storing them, so in principle a collision could throw its count off. The odds are negligible.
- **The page draws up to 700 nodes.** Bigger nets can still be stepped through, with the term and the counters as the only feedback.

## References

- J.-J. Lévy, *Réductions correctes et optimales dans le lambda-calcul*, 1978.
- J. Lamping, *An algorithm for optimal lambda calculus reduction*, POPL 1990.
- A. Asperti and S. Guerrini, *The Optimal Implementation of Functional Programming Languages*, Cambridge University Press, 1998.
- V. van Oostrom, K.-J. van de Looij and M. Zwitserlood, *Lambdascope: another optimal implementation of the lambda-calculus*, 2004.
