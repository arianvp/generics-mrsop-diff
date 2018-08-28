mrdiff="./dist/build/mrdiff/mrdiff"
a_or_b=$1
d=$3
atime="$(time ( timeout "${timeout}" "${mrdiff}" diff "${d}/O.clj" "${d}/${a_or_b}.clj") 2>&1 1>/dev/null )"
ret=$?
real=$(echo $atime | awk '{print $2}')
user=$(echo $atime | awk '{print $4}')
sys=$(echo $atime | awk '{print $6}')
echo "$d $a_or_b $ret $real $user $sys"
