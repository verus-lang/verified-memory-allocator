# build our allocators
./build-verus-mimalloc.sh

# set up benchmarks
cd mimalloc-bench
./build-bench-env.sh bench    # build benchmarks
./build-bench-env.sh mi       # build allocators to compare to (e.g., mimalloc) 
