#!/usr/bin/env bash
GIT_WORK_TREE=""
GIT_DIR=""

repos="$1"
target="$2"
lang="$3"

function earlyexit {
  if ! [[ -z "$repo" ]]; then
    git -C $repo merge --abort
    git -C $repo reset -q --hard
    git -C $repo clean -fdxq
    git -C $repo checkout master
    exit 1
  fi
}

trap earlyexit SIGINT SIGTERM SIGQUIT

for repo in $repos/*/; do
  # make sure the git commits that follow are on the repo in question
  # export GIT_WORK_TREE="$repo"
  # export GIT_DIR="$repo/.git"
  echo "Mining $repo"
  old_branch=$(git -C $repo symbolic-ref --short HEAD)

  for commit in $(git -C $repo rev-list --merges HEAD); do
    parents=$(git -C $repo log -1 --format=%P $commit)
    fst=${parents%% *}
    rest=${parents#* }
    git -C $repo checkout -q $fst
    git -C $repo merge --no-commit $rest >/dev/null 2>&1
    if git -C $repo ls-files --unmerged | grep -q '^'; then
      echo "found conflict in $repo - $commit"
      unmerged=$(git -C $repo ls-files --unmerged | cut -d' ' -f2,3 | paste -d'\n' -s)
      git -C $repo ls-files --unmerged
      while read -r objID; do
        obj=${objID:0:40}
        role=${objID:41:1}
        extension=${objID: -3}
        if [ "$extension" == "$lang" ]; then
          if [ "$role" -eq "1" ]; then
            # We set the $obj the first time
            towrite="$target/$(basename $repo)-$commit-$obj"
            fname="O.$lang"
          fi
          if [ "$role" -eq "2" ]; then
            fname="A.$lang"
          fi
          if [ "$role" -eq "3" ]; then
            fname="B.$lang"
          fi
          echo "$twowrite"
          mkdir -p "$towrite"
          git -C $repo cat-file -p $obj > "$towrite/$fname"
        fi
      done <<< $unmerged
      git -C $repo merge --abort
    fi
    git -C $repo reset -q --hard
    git -C $repo clean -fdxq
  done
  git -C $repo checkout -q $old_branch
done

