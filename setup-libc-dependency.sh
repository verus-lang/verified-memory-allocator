#!/bin/bash

set -e

BASEDIR=$(realpath $(dirname "$0"))
VERUS_DIR=$BASEDIR/../../verus

# build the rlib file for libc crate, which verus-mimalloc takes as a dependency

cd $BASEDIR
mkdir -p build

cd test_libc
cargo clean
cargo +1.73.0 build --release
cd ..
LIBC_RLIB_NAME=$(find ./test_libc/target/release/deps/ -name 'liblibc-*.rlib')
cp $LIBC_RLIB_NAME build/liblibc.rlib


