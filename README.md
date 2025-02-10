### What is this?

This is a verified memory allocator, written in Rust and verified with
[Verus](https://github.com/verus-lang/verus). Its design is based on 
[mimalloc](https://github.com/microsoft/mimalloc).

_Why verify a memory allocator?_
One aim of the project is to test Verus's ability to verify systems software.
Memory allocators, in particular, are interesting because they're fairly
low in the software stack. In Rust, a lot of the libraries we take for granted
(Box, Rc, Vec, etc.) rely on a memory allocator, so we can't use those.
As a result, the software's relationship to memory feels quite
a bit different than it does for higher-level application code,
making it an interesting case study.

_Why base your allocator on an existing one, rather than designing a new allocator?_
I don't know much about memory allocator design. Ultimately, this project is an exercise
in verification, not memory allocator design, so it made sense to use a design already
known to be good.

_Mimalloc is written in C, so that means you had to basically port it to Rust?_ That's right.

_Why do that?_ Rust has some nice properties that make it a good target for formal verification.
You can see [our paper](https://arxiv.org/abs/2303.05491) on the design of Verus.

_You said your allocator is "based on" mimalloc, what's that mean?_ I tried to stick
as close as possible to the same internal memory layout and high level code structure,
even when it was kind of annoying to do so. Of course, lots of types had to change in order
to make things work with Rust and Verus.
As a result, you'll actually find many of the function names match those in the mimalloc
source code, but this is less true for the type names.

### Verifying

Make sure [Verus](https://github.com/verus-lang/verus) is installed and `verus` is on your PATH.
Also, make sure that it is built with `--features singular`. (See the
[Singular setup instructions in the Verus guide](https://verus-lang.github.io/verus/guide/nonlinear_bitvec.html#setup)).

Run this:

```
./setup-libc-dependency.sh
```

Now you should be good for verifying:

```
./verus-mimalloc/verify.sh
```

This should take about a minute, but may depend on the amount of parallelism on your computer.
You will probably see a lot of information about which functions are taking a long time to verify,
but you can ignore this unless you see an actual error.
At the end you should see something like "743 verified, 0 errors" (or some other large number).

Last tested with Verus 27662d20bf2b2c085d6752cc22977df796e8e0e5

### Benchmarking

The `mimalloc-bench` directory contains the [mimalloc benchmark suite](https://github.com/daanx/mimalloc-bench) modified to support the allocators in this directory.

**You need to be on Linux.** The malloc overrides don't work for macOS, and it just silently uses the system malloc.
See `system_notes.md` for some more information on how the overrides work.

See https://github.com/microsoft/mimalloc/blob/master/src/alloc-override.c for some information on how mimalloc handles the system overrides. In principle, we could do something similar if we ever have a pressing need to get the benchmarking working on mac. I have no idea what happens on windows.

To set up the benchmarks:

```
# build our allocators
./build.sh

# set up benchmarks
cd mimalloc-bench
./build-bench-env.sh bench    # build benchmarks
./build-bench-env.sh mi       # build allocators to compare to (e.g., mimalloc)
```

To run benchmarks:

```
cd mimalloc-bench/out/bench
../../bench.sh vmi cfrac
```

"vmi" is verus-mimalloc, cfrac is the benchmark. Use "allt" for the benchmark name to run all benchmarks.

The bench.sh script takes the name of an allocator to run and a benchmark name, see
https://github.com/daanx/mimalloc-bench for more details.

To run both our allocator and mimalloc, and get a comparison table, run:

```
bash compare-benchmarks.sh
```

(At the moment, we compare pretty badly.)

### Allocator features

 * Supports `malloc` and `free`
 * Supports multi-threading
 * Supports allocations up to 128 KiB

Not supported:

 * realloc, aligned allocations
 * Thread cleanup (this means ThreadIDs can't be re-used, may leak memory if lots of threads are created and destroyed)

### Memory allocators in this directory

 * `verus-mimalloc` - Verus memory allocator based on [mimalloc](https://github.com/microsoft/mimalloc). (This is what you're here for.)
 * `rust-jemalloc-wrapper` - Rust wrapper around jemalloc. Mostly used as a control for testing the benchmark script.

