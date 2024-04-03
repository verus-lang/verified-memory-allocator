Some notes about the way the verified memory allocator interacts with the OS. For more details about the allocator itself, see the `verus-mimalloc/` directory.

### Glue code

The `build-verus-mimalloc.sh` script builds a `.so` file that can be linked to a binary to override the system allocator. This only works on *Linux* at the moment.

To accomplish the override, we need to override a bunch of symbols - `malloc`, `free`, and a bunch of others.  These symbols are all exported in `verus-mimalloc/lib.rs`.  These functions then dispatch to the verified code.  For example, the function called `malloc` calls into the top-level allocation function provided by the verified allocator, `heap_malloc`.

One snag is that the verified functions take a parameter that is a pointer to the thread-local "Heap" data structure. This means that: (i) When a new thread is initialized, we need to initialize the Heap for this thread, and (ii) When we call malloc, we need to obtain the pointer to the thread-local Heap. This is done with the help of `overrides.cpp`, which is linked into the crate by the build script.

### Internals

The memory allocator relies on two interfaces from the OS that we apply trusted specifications to.

 * **Allocating memory from the OS.** The `mmap` interface for allocating memory from the OS. This is specified in `os_mem.rs`. We use the libc crate and supply specifications in terms of Verus's `PointsToRaw` primitive and another ghost object that represents the OS permission state.

 * **Threading.** We don't actually need to spawn threads or anything, but we do need to account for the possibility that the client might, and we need a function to get the thread-unique ID. Actually, Verus's vstd already supports a way to get the current thread ID, but this internally relied on a memory allocator, so we couldn't use that. Thus, we implement our own thread ID function in `overrides.cpp`.
