#!/bin/bash
cd ../test/conflicts2

executable="/Users/giovannigarufi/Developement/thesis/th-vcs-clojure/.stack-work/dist/x86_64-osx/Cabal-1.24.2.0/build/th-vcs-clojure-exe/th-vcs-clojure-exe"

function wrap_diff3 () {
  diff3 $1 $2 $3 -m
  CODE=$?
  if [ $CODE -eq 1 ]; then
    return 0
  else
    return $CODE
  fi
}

for D in ./*; do
  echo "$D"
  if [ -d "$D" ]; then
    dirPath=$(realpath $D)
    cd "$D"
    if wrap_diff3 A.clj O.clj B.clj -m > M.clj && "${executable}" -p "${dirPath}" ; then
      echo "OK"
      cd ..
    else
      cd ..
      echo "deleting $D"
      rm -rf "$D"
    fi
  fi
done
