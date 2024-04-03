#!/usr/bin/env bash
cd $(dirname "$0")
verus --triggers-silent --no-auto-recommends-check --rlimit 70 --extern libc=../build/liblibc.rlib lib.rs "$@" -- -Zproc-macro-backtrace
