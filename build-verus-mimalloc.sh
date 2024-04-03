#!/bin/bash

set -e

BASEDIR=$(realpath $(dirname "$0"))

# build the rlib file for libc crate, which verus-mimalloc takes as a dependency

cd $BASEDIR
mkdir -p build

./setup-libc-dependency.sh

# compile overrides.cpp to a static library

cd verus-mimalloc

g++ -g -fPIC -std=c++17 -O2 -Wall -c overrides.cpp -o ../build/overrides.o

# TODO use no-alloc
# TODO turn on optimizations

verus \
    --extern libc=../build/liblibc.rlib \
    lib.rs \
    --compile --no-verify \
    -- \
    --cfg 'feature="override_system_allocator"' \
    -C debuginfo=2 \
    -C panic=abort \
    -Zproc-macro-backtrace \
    --crate-type cdylib \
    -C link-arg=$BASEDIR/build/overrides.o \
    -o $BASEDIR/build/libverus-mimalloc.so \
    -C opt-level=2 \
    -C overflow-checks=off

    #--print link-args

cd $BASEDIR/build/
