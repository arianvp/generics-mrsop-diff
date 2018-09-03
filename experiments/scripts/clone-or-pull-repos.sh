#!/usr/bin/env coffee

#############################################################################################################
# This script checks for a repos.json file in the same folder and attempts to clone all those               #
# repositories to the path ../test/repos. If the repo was already cloned it will attempt to pull instead    #
#############################################################################################################

require 'shelljs/global'
fs = require 'fs'
_ = require 'lodash'
async = require 'async'

if not which 'git'
  echo 'Sorry, this script requires git'
  exit 1

cd(__dirname)

repos = _.take(JSON.parse(fs.readFileSync('./repos.json')), 20)

cd("../test/repos")

async.eachSeries repos, (repo, cb) ->
  if not test('-d', repo.name)
    exec('git clone ' + repo.url)
  else
    cd(repo.name)
    exec('git reset -q --hard && git clean -fdxq && git checkout master')
    exec('git pull')
    cd('..')
  cb()
, (err) ->
  console.log('Done')

