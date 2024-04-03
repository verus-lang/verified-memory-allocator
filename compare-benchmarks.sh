set -e

cd mimalloc-bench/out/bench

../../bench.sh --procs=16 vmi allt | tee ../../../vmi-out.txt
../../bench.sh --procs=16 mi allt | tee ../../../mi-out.txt

cd ../../..

python3 compare-benchmarks.py
