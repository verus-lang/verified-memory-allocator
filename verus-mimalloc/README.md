# Verus memory allocator

This is a verified allocator based off the design of mimalloc.

For reference:

 * Mimalloc codebase is at: https://github.com/microsoft/mimalloc
 * Microsoft has a tech report with high level design decisions: https://www.microsoft.com/en-us/research/publication/mimalloc-free-list-sharding-in-action/

# Source code overview for Verus-mimalloc

The most most complex, interconnected top-level implementation files are:
`alloc_fast.rs`,
`alloc_generic.rs`,
`free.rs`,
`page.rs`,
`segment.rs`, and
`queues.rs`.
These files contain the `alloc` and `free` implementations and deal with
all the complex doubly-linked list structures that make up the segments,
e.g., allocating a new segment, allocating a new page, arranging the pages into blocks.

Other important implementation files:
 * `types.rs` - Definitions for segment headers, page headers, etc. Contains the primary "well-formedness predicate" for the thread-local state.
 * `linked_list.rs` - Implements the free list (including atomic free list and normal free lists)
 * `init.rs` - Initializing the heap for a thread
 * `commit_mask.rs` - Implements the bitmap used as the "commit mask"
 * `layout.rs` - pointer arithmetic for calculating page addresses, block addresses
 * `bin_sizes.rs` - handles the way we map block sizes to bins and vice versa

Files that are purely abstractions and proofs:
 * `page_organization.rs` - Abstract model of the segment slice structure (described below)
    and the doubly-linked lists, slice counts and offsets
 * `tokens.rs` - Models the way pages are shared across threads

**Overrides:** The `lib.rs` file is where we override all the symbols like `malloc` and so forth.
This requires the `override_system_allocator` feature and only works on Linux.
Note that the verified API takes a pointer to the thread local state, while `malloc` and friends
do not. To acquire the thread local pointer, we use the helper in `overrides.cpp` which is linked
in at the end.

Other trusted components:
 * `os_mem_util.rs` - where we axiomatize `mmap`
 * `thread.rs` - where we axiomatize thread utils like thread IDs. (Slightly modified
    from vstd's thread utilities)


# Notes on mimalloc implementation

Below is a more nitty-gritty summary of low-level details that are needed for
a reimplementation.

These notes are mostly based on my reading of the mimalloc codebase and inferring
how it works and how its data is laid out.

I'm specifically working off of commit dd7348066fe40e8bf372fa4e9538910a5e24a75f

### Overall architecture

The hierarchy of objects in this allocator goes:

   Heap > Page > Block

Each Page is associated to a particular 'block size'. So to allocate memory of size N,
the allocator first finds a page of the appropriate size, then allocates a block from
that page.

There is also a structure called a 'Segment'. Pages are allocated from the segments,
and segments are shared between the pages.

All of these (heap, segment, page, block) are assigned to a particular thread.
So we might have like:

 - Thread T has Heaps H1 and H2
 - Thread T has Segments S1, S2, and S3
 - H1 has pages {P1, P2, P3, P4} allocated out of T's segments
 - H2 has pages {P5, P6, P7, P8, P9} allocated out of T's segments
 - Each page has a bunch of blocks.

Now, even though this is all thread local, the 'free' might be called from any thread -
therefore, there could be concurrent access to any of these things, though there are
only a few fields that need to worry about atomic accesses.

(Note: at present, Verus-mimalloc only has one heap per thread)

### Segment layout

The Segment has: a SegmentHeader followed by a bunch of "slices".
Each Page might make up a "span" of slices.
Furthermore, the SegmentHeader has an array of PageHeaders (or just "Pages").
There is one PageHeader per slice.

 - Each "Page Area" is a span of slices, which corresponds to a span of PageHeaders.
   Within those PageHeaders, only the first one in the range is the "main" PageHeader
   for the span. All the other PageHeaders have their 'offset' marked.

 - Therefore, given a pointer to a block (i.e., into one of the slices)
   you can find the corresponding Page easily.
   First, you find the Slice you are in, then you use the 'offset' to go
   to the first slice.

```
 | SegmentHeader   |                        Slices                        |
 |-----|-----------|----|----|----|----|----|----|----|----|----|----|----|
 |     |PageHeaders|     Page     |          Page          |     Page     |
```

Example: In the diagram, there are 11 slices (after the slice that is unused because it
contains the SegmentHeader). In the 11 PageHeaders, their offsets will be:

```
   0, 1, 2, 0, 1, 2, 3, 4, 0, 1, 2
   |-----|  |-----------|  |-----|       (3 spans)
  
   ^        ^              ^
   |        |              |
    ----------------------------- main PageHeaders for each Page.
```

*Large alignment:* there's also a special case for blocks that need large alignment.
A segment can have one extra slice, which starts at the end of the main segment
(that is, `SEGMENT_SIZE` bytes after the start of the SegmentHeader).
In this case, the total number of slices in the segment is
one more than usual (that is, `SLICES_PER_SEGMENT + 1`).

### Organization of a thread's segments

A thread has a bunch of segments and each segment has a bunch of slices.
Slices are clumped into pages, though pages may or may not be in use.

 * If a page is "in use" then it has a "block size" assigned, and its blocks are arranged
   into free lists so they can be allocated out to the user.
 * If a page is "not in use" then it has no block size assigned and no linked list structure.

All the pages are kept in doubly-linked lists which link together the *first* PageHeader
of each page. Each first-PageHeader page is in exactly one of the following linked lists:

 * The "thread local data" (TLD) has a sequence of doubly-linked lists,
   each one representing a bin.
   These lists contain the pages which are currently "not in use".
   Pages are binned by the number of the slices in the page.
 * Each heap has a sequence of doubly-linked lists for pages that are "in use".
   These are binned by the block size.

Again: for a single thread, the sum total of the pages in these linked lists should
make up all the segments currently owned by that thread.

Now in terms of this layout, we can describe the meaning of the `PageHeader` fields
`prev`, `next`, `count` and `offset` more precisely:

 * `prev` and `next`: If it's the primary header, these are pointers within the linked list.
    Otherwise, unspecified.
 * `count`: If it's the primary header, it's the number of slices in this page.
    Otherwise, unspecified.
 * `offset`: Offset within the page, as described above. For an "in use" page,
    every slice has the offset (this is necessary to implement `free`).
    For a "not in use" page, only the first and last slices need an offset.
    This is needed for traversal of segments. The rest are unspecified.
 * `block_size`: For "in use" pages, the primary page should indicate the block size.
    For "not in use" pages, this value is 0. For non-primary pages, unspecified.

_Notes on ownership in Verus implementation._ Of these fields, the only one that might be accessed by concurrent threads is `offset`, which is constant for the period in which
a page is "in use".
Thus:

 * Ownership of all the other fields is always maintained by the thread to which the
   page belongs.
 * Ownership of the `offset` field is shared via the ghost token system when the page is
   in use, and maintained by the thread when not in use.

### Abandoned segments

When a thread terminates, all of its segments are _abandoned_.
Note that the segment might still have pages in use and the user might still be
holding onto memory that was allocated by that thread.
An abandoned thread is marked as thread 0 and goes into a global store for abandoned segments.
There might still be concurrent frees at this point.

When a segment is abandoned, all of its pages are removed from any doubly-linked list.

The "abandoned segment store" consists of two singly-linked lists, `abandoned` and
`abandoned_visited`.

TODO need to understand:
  * Do the prev and next pointers need to be set to NULL or anything, or are they unspecified at this point?
  * What's the logic for reclaiming or deallocating segments?
  * When does the `abandoned_visited` list move into the `abandoned` list?
  * How to verify popping from the list and the ABA problem? (See `segment.c`)


_Notes on ownership in Verus implementation._ Currently abandoned segments are unimplemented. Eventually, the way it will probably work is that when a thread is abandoned, the shared access to it (involving the "in use" pages) continues to be maintained by the token system. All of "thread local" ownership moves from the thread into the abandon page store.

### Heaps and page pointers

As explained above, the in-use PageHeaders are organized into a DOUBLY-linked list which is
owned by a Heap. (Each PageHeader has a `next` and `prev` field.)
Also, each PageHeader contains a pointer back to the Heap that owns it.

Therefore, the pointer structure between heaps and pages is very cyclic.
Furthermore, the exact layout of a segment is very important for a few reasons:

  1. `free` needs to be able to take a pointer to a block and determine
       what segment and page it is in (and our proof needs to be able to prove
       that said page is valid simply from the fact that its block was allocated).

  2. The segment is broken into chunks of size `COMMIT_SIZE`, the granularity
      at which memory is 'committed' from the OS.

# Proof notes

Our top-level tokensized system is going to maintain the heaps, segments, and pages,
keeping track of which thread owns what, all the doubly-linked lists, and so on.
(The singly-linked lists will primarily be handled in the implementation)

