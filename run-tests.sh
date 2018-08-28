#!/usr/bin/env bash

dir=$1
timeout="30s"
mrdiff="./dist/build/mrdiff/mrdiff"

# limit to 8GiBs of memory
ulimit -v 8589934592

# ls $dir/*/ | parallel --memfree 4G echo :::
# find $dir -type d | parallel --memfree 4G ./run-result.sh A 30s {}

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

