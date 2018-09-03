#!/usr/bin/env bash

dir=$1

# Diffs that take longer than 30s are cancelled
timeout="30s"

mrdiff="./dist/build/mrdiff/mrdiff"

# limit to 8GiBs of memory per process
ulimit -v 8589934592

for d in $dir/* ; do
  a_or_b="A"
  atime="$(time ( timeout "${timeout}" "${mrdiff}" diff "${d}/O.clj" "${d}/${a_or_b}.clj") 2>&1 1>/dev/null )"
  ret=$?
  real=$(echo $atime | awk '{print $2}')
  user=$(echo $atime | awk '{print $4}')
  sys=$(echo $atime | awk '{print $6}')
  echo "$d $a_or_b $ret $real $user $sys"

  a_or_b="B"
  atime="$(time ( timeout "${timeout}" "${mrdiff}" diff "${d}/O.clj" "${d}/${a_or_b}.clj") 2>&1 1>/dev/null )"
  ret=$?
  real=$(echo $atime | awk '{print $2}')
  user=$(echo $atime | awk '{print $4}')
  sys=$(echo $atime | awk '{print $6}')
  echo "$d $a_or_b $ret $real $user $sys"
done

