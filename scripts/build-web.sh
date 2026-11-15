#!/bin/sh
# Builds the WebAssembly package the page in `web/` loads.
# Needs the wasm32-unknown-unknown target and wasm-pack.
set -eu
cd "$(dirname "$0")/.."
wasm-pack build crates/web --target web --release --no-typescript --out-dir ../../web/pkg
