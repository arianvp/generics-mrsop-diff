#!/usr/bin/env bash

#############################################################################################################
# This script walks the commit history of the repositories under ../test/repos. For each repository it will #
# attempt to extract all the files which give rise to a conflict in a 3-way merge.                          #
#############################################################################################################

# Useful for testing
function earlyexit {
  # get rid of changes so the next checkout doesnt complain
  git merge --abort
  git reset -q --hard
  git clean -fdxq
  git checkout master
  exit 1
}

trap earlyexit SIGINT SIGTERM

cd ../test/repos

for D in ./*; do
  if [ -d "$D" ]; then
    cd "$D"
    echo "Mining $D"
    # We store the current status so we can restore cleanly once we are done
    old_branch=$(git symbolic-ref --short HEAD)

    # We list all commits which are identified as merges (>1 parent)
    for commit in `git rev-list --merges HEAD`
    do
      # find the parents of the merge commit
      parents=$(git log -1 --format=%P $commit)
      fst=${parents%% *}
      rest=${parents#* }
      # check out the first parent
      git checkout -q $fst
      # merge with the rest of them
      git merge --no-commit $rest  >/dev/null 2>&1
      # check for conflicting files
      if git ls-files --unmerged | grep -q '^'; then
        echo "Found conflict in $D - $commit"
        unmerged=$(git ls-files --unmerged | cut -d' ' -f2,3 | paste -d'\n' -s)
        # We parse the list of git objects representing the conflicting files. This representation is fixed
        # with a 40 character objId and an identifier which represents the role. We restrict to merges between 2 parents.
        while read -r objID; do
          obj=${objID:0:40}
          role=${objID:41:1}
          extension=${objID: -3}
          if [ "$extension" == "clj" ]; then
            # The role represents which version of the git object we are dealing with.
            # 1 -> Is the common parent for both branches (The origin)
            # 2 -> Version on branch A
            # 3 -> Version on branch B
            if [ "$role" -eq "1" ]; then
              # N.B. obj appear ordered by role. Role 1 will always be the first.
              targetDir="../../conflicts2/$D-$commit-$obj"
              mkdir -p "$targetDir"
              fname="O.clj"
            fi
            if [ "$role" -eq "2" ]; then
              fname="A.clj"
            fi
            if [ "$role" -eq "3" ]; then
              fname="B.clj"
            fi

            # Output the git object as a file according to our identification
            git cat-file -p $obj > "$targetDir/$fname"
          fi
        done <<< "$unmerged"
        # Abort the merge to restore initial state
        git merge --abort
      fi
      # get rid of changes so the next checkout doesnt complain
      git reset -q --hard
      git clean -fdxq
    done
    git checkout -q $old_branch
    cd ..
  fi
done


