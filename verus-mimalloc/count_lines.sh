DIR=/Users/tjhance/Dropbox/verus-systems-code/memory-allocators/verus-mimalloc
LCDIR=/Users/tjhance/Dropbox/verus/source/tools/line_count

rm -rf lib.d
./rrv --emit=dep-info --no-verify

cd $LCDIR
cargo run --release -- $DIR/lib.d -p 2> ~/o
cargo run --release -- $DIR/lib.d --json > $DIR/lc.json

cd $DIR
python3 process_lines.py < lc.json
