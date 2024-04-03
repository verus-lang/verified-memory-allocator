#!/bin/bash

set -e

cd rust-jemalloc-wrapper
cargo build --release
cd ..

./build-verus-mimalloc.sh
