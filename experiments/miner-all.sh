#!/bin/sh
./miner.sh clj conflicts-clj | tee clj.$(git rev-parse HEAD).csv
./miner.sh lua conflicts-lua | tee lua.$(git rev-parse HEAD).csv
