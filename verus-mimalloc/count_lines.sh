DIR=$(dirname "$0")

if [ ! -d "$LINE_COUNT_DIR" ]; then
  echo "set \$LINE_COUNT_DIR to the directory verus/source/tools/line_count"
  exit -1
fi

rm -rf lib.d
./rrv --emit=dep-info --no-verify

pushd $LINE_COUNT_DIR
cargo run --release -- $DIR/lib.d -p 2> ~/o
cargo run --release -- $DIR/lib.d --json > $DIR/lc.json
popd

pushd $DIR
python3 process_lines.py < lc.json
popd
