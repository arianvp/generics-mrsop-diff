cd ../test/conflicts2

for D in ./*; do
  if [ -d "$D" ]; then
    if [ `ls $D -l | wc -l` -lt 4 ]; then
      rm -rf $D
      echo "$D"
    fi
  fi
done