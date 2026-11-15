#!/bin/sh
# Builds the WebAssembly package the page in `web/` loads.
# Needs the wasm32-unknown-unknown target and wasm-pack.
set -eu
cd "$(dirname "$0")/.."
wasm-pack build crates/web --target web --profile web --no-typescript --out-dir ../../web/pkg
echo "Built web/pkg. Serve the page with: python3 -m http.server --directory web 8000"
