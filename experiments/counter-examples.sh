

# This one triggers  a 
# mrdiff: should never happen
git diff --no-index conflicts-clj/aleph-b3a48043e7c80ad3ae3abeb7801fb4372a25fc61-c51646819e3934a008b7f54b0adb0d805ae39f46/O.clj conflicts-clj/aleph-b3a48043e7c80ad3ae3abeb7801fb4372a25fc61-c51646819e3934a008b7f54b0adb0d805ae39f46/B.clj


# Triggers a should never happen
../dist/build/mrdiff/mrdiff diff conflicts-clj/aleph-72d5703eeaf94eb83bad87b93809364c788c021d-5d64c9b4c972cb805e2f75043ee80ce42962084b/O.clj conflicts-clj/aleph-72d5703eeaf94eb83bad87b93809364c788c021d-5d64c9b4c972cb805e2f75043ee80ce42962084b/A.clj


# Triggers a HELP HELP
../dist/build/mrdiff/mrdiff diff conflicts-clj/aleph-5fa02b9437151891adf4ff692bd61dd96476352c-33e162798eefa97a0b37d6a32b5428595b8248ed/O.clj conflicts-clj/aleph-5fa02b9437151891adf4ff692bd61dd96476352c-33e162798eefa97a0b37d6a32b5428595b8248ed/B.clj
