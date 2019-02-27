#!/usr/bin/env bash
set -uo pipefail

if [[ "$#" -ne "2" ]]; then
  echo "need lang [clj,lua] and I need a directory!"
elif [[ ! -d "$2" ]]; then
  echo "'$2' is not a directory!"
fi

lang="$1"
dir="$2"
# data shows that things only run out of memory if
# they run longer than 20s
timeout="25s"
mergetool="../dist/build/mrdiff/mrdiff"


# limit to 8GiBs of memory per process
ulimit -v 10000000

# TODO add timings

trap "exit" INT

mkdir -p "${dir}_slow"
for d in ${dir}/*; do
  timeout "${timeout}" "${mergetool}" diff --stats duration "${d}"/{O,A}."${lang}"
  res_1=$?
  timeout "${timeout}" "${mergetool}" diff --stats duration "${d}"/{O,B}."${lang}"
  res_2=$?




  # if [[ $res_1 -gt 0  || $res_2 -gt 0 ]]
  # then
  #   echo "TOO SLOW. ISOLATING $d"
  #   mv "$d" "${dir}_slow"
  # fi
done
