#!/usr/bin/env coffee

#############################################################################################################
# This script queries Github for the 100 most popular (ranked by number of stars) Clojure repositories.     #
# It will then save these repositories to a file called repos.json ordering them by number of contributors  #
#############################################################################################################

request = require 'superagent'
_ = require 'lodash'
async = require 'async'
fs = require 'fs'

results = []
auth = {'Authorization': 'token ' + process.env['GITHUB_API_TOKEN']}

request
  .get("https://api.github.com/search/repositories?q=language:lua&s=stars")
  .query({per_page: 100})
  .set(auth)
  .end (err, res) ->
    if err then throw err
    # Set limit to 10 to be kind to github
    async.eachLimit(res.body.items, 10, (repo, cb) ->
      aggregatingResults([], request.get(repo.contributors_url).query({per_page: 100}).set(auth)
      , (err, res) ->
        if err then throw err
        results.push {name: repo.name, url: repo.html_url, contributors: res.length}
        cb()
      )
    , (err) ->
      if err then throw err
      fs.writeFileSync(__dirname + '/repos.json', JSON.stringify(_.reverse(_.sortBy(results, 'contributors')), null, 2))
    )


aggregatingResults = (acc, req, cb) ->
  req.end (err, res) ->
    if err then return cb(err, null)
    acc = acc.concat (res.body)
    if res.links?.next
      return aggregatingResults(acc, request.get(res.links.next).set(auth), cb)
    else
      return cb(err, acc)
