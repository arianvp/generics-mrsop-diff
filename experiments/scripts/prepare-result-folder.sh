cd ../test/repos

for D in ./*; do
  if [ -d "$D" ]; then
    repoName=${D:2}
    target="../results/${repoName}"
    mkdir -p $target
    touch "${target}/Disj.md"
    touch "${target}/Comp.md"
    touch "${target}/Struct-Comp.md"
    touch "${target}/Struct-Disj.md"
  fi
done