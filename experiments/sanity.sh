#!/usr/bin/env bash
set -euo pipefail
set -x

dir="$1"
timeout="5s"
mrdiff="../dist/build/mrdiff/mrdiff"

# limit to 8GiBs of memory per process
ulimit -v 8589934592

for d in ${dir}/*; do
  timeout "${timeout}" "${mrdiff}" diff "${d}/O.clj" "${d}/A.clj" || true
  timeout "${timeout}" "${mrdiff}" diff "${d}/O.clj" "${d}/B.clj" || true
done
