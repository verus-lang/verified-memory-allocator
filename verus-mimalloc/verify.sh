#!/usr/bin/env bash
cd $(dirname "$0")

if [ -z "$VERUS_PATH" ]; then
    VERUS_PATH="verus"
fi
$VERUS_PATH --triggers-mode=silent --no-auto-recommends-check --rlimit 70 --extern libc=../build/liblibc.rlib lib.rs "$@" -- -Zproc-macro-backtrace
