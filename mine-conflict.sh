#!/usr/bin/env bash
set -eEfuo pipefail

GIT_WORK_TREE=""
GIT_DIR=""

repos="$1"
target="$2"

function earlyexit {
  if ! [[ -z "${GIT_WORK_TREE}" ]]; then
    git merge --abort
    git reset -q --hard
    git clean -fdxq
    git checkout master
    exit 1
  fi
}

trap earlyexit SIGINT SIGTERM

for repo in $repos/*; do
  # make sure the git commits that follow are on the repo in question
  export GIT_WORK_TREE="$repo"
  export GIT_DIR="$repo/.git"

  echo "Mining $GIT_WORK_TREE"
 
  old_branch=$(git symbolic-ref --short HEAD)

  for commit in $(git rev-list --merges HEAD); do
    parents=$(git log -1 --format=%P $commit)set -eEfuo pipefail
    fst=${parents%% *}
    rest=${parents#* }
    git checkout -q $fst
    git merge --no-commit $rest >/dev/null 2>&1
    if git-ls-files --unmerged | grep -q '^'; then
      echo "$found conflict in $GIT_WORK_TREE - $commit"
    fi
  done
done

