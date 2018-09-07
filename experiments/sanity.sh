#!/usr/bin/env bash
set -euo pipefail

dir="$1"
timeout="5s"
mergetool="../dist/build/mrdiff/mrdiff"

# limit to 8GiBs of memory per process
ulimit -v 8589934592

# TODO add timings

for d in ${dir}/*; do
  if ! timeout "${timeout}" "${mergetool}" merge "${d}/A.clj" "${d}/O.clj" "${d}/B.clj"
  then
    echo "FAIL ${mergetool}" merge "${d}/A.clj" "${d}/O.clj" "${d}/B.clj"
  else
    echo " SUCCESS ${mergetool}" merge "${d}/A.clj" "${d}/O.clj" "${d}/B.clj"
  fi
done
