#!/usr/bin/env bash
set -uo pipefail

if [[ "$#" -ne "1" ]]; then
  echo "I need a directory!"
elif [[ ! -d "$1" ]]; then
  echo "'$1' is not a directory!"
fi

dir="$1"
# data shows that things only run out of memory if
# they run longer than 20s
timeout="25s"
mergetool="../dist/build/mrdiff/mrdiff"

ver=$($mergetool --version)
echo "Running $mergetool at $ver"

# limit to 8GiBs of memory per process
ulimit -v 10000000

# TODO add timings

trap "exit" INT

mkdir -p "${dir}_slow"
for d in ${dir}/*; do
  # timeout "${timeout}" "${mergetool}" merge "${d}"/{A,O,B}.clj # 1>/dev/null 2>&1
  timeout "${timeout}" "${mergetool}" diff "${d}"/{O,A}.clj # 1>/dev/null 2>&1
  res_1=$?
  echo "${d} A $mergetool unknown($res_1)"

  timeout "${timeout}" "${mergetool}" diff "${d}"/{O,B}.clj # 1>/dev/null 2>&1
  res_2=$?
  echo "${d} B $mergetool unknown($res_2)"

  # if [[ $res_1 -gt 0  || $res_2 -gt 0 ]]
  # then
  #   echo "TOO SLOW. ISOLATING $d"
  #   mv "$d" "${dir}_slow"
  # fi
done
