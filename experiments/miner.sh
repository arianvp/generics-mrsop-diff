#!/usr/bin/env bash
set -uo pipefail

if [[ "$#" -ne "2" ]]; then
  echo "need lang [clj,lua] and I need a directory!"
elif [[ ! -d "$2" ]]; then
  echo "'$2' is not a directory!"
fi

lang="$1"
dir="$2"

# Same timeout as Garufi
# timeout="60s"
mergetool="../dist/build/mrdiff/mrdiff"


# limit to 8GiBs of memory per process
ulimit -v 10000000

# TODO add timings

trap "exit" INT

for d in ${dir}/*; do
  "${mergetool}" diff --stats duration "${d}"/{O,A}."${lang}"
  res_1=$?

  "${mergetool}" diff --stats duration "${d}"/{O,B}."${lang}"
  res_2=$?

if [[ $res_1 -gt 0  || $res_2 -gt 0 ]]
then
  mkdir -p  "${dir}_${res_1}_${res_2}"
  mv "$d" "${dir}_${res_1}_${res_2}"
fi

done
