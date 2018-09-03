fs = require 'fs'
_ = require 'lodash'
file = JSON.parse fs.readFileSync('../Visualiser/patch.json', 'utf8')

checkNode = (node) ->
  node2str = JSON.stringify(_.omit(node, 'children'))
  if !_.isObject(node) then throw new Error("node " + node2str + " is not an object")
  if !node.text then throw new Error("node " + node2str + " has no text")
  for own key, value of node
    switch key
      when 'text', 'children', 'connectors', 'collapsed', 'pseudo', 'HTMLclass' then continue
      else throw new Error('node ' + node2str + ' has inconsistent props')
  # console.log('node ' + node2str + ' checks out ')
  _.map(node.children, checkNode)

isAlmu = (node) ->
  name = node.text.name
  return (name is "Alspn" || name is "Alins" || name is "Aldel")

isSpine = (node) ->
  name = node.text.name
  return (name is "Scp" || name is "Scns" || name is "Schg")

isAl = (node) ->
  name = node.text.name
  return (name is "Ains" || name is "Adel" || name is "Amod")

setStroke = (node, colour) ->
  col = colour
  if isAlmu(node)
    switch node.text.name
      when "Alspn" then col = 'black'
      when "Alins" then col = 'green'
      when "Aldel" then col = 'red'
  else if isAl(node)
    switch node.text.name
      when "Amod" then col = 'black'
      when "Ains" then col = 'green'
      when "Adel" then col = 'red'
  else if (node.text.name == "Here")
    col = 'black'
  node.connectors=
    style:
      stroke: col
      "stroke-width": '2'
  _.map(node.children, _.partial(setStroke, _, col))
  return node

isLeaf = (node) ->
  return (_.isUndefined(node.children) || _.isEmpty(node.children))

isSwap = (node) ->
  return (_.isString(node.text.src) && _.isString(node.text.dst))

isCons = (node) ->
  return node.text.name is "Cons"

collapseTree = (tree) ->
  collapseBranch = (node) ->
    childStatus = _.map(node.children, collapseBranch)
    check = (isFlattenable(node) && _.every(childStatus) && !isSwap(node))
    if (check && !isLeaf(node))
      node.collapsed = true
    if isCons(node)
      node.pseudo = true
      node.collapsed = false
    return check
  collapseBranch(tree)
  return tree

setHTMLClass = (node) ->
  if isIns(node) then node.HTMLclass = 'ins-node'
  if isDel(node) then node.HTMLclass = 'del-node'
  _.map(node.children, setHTMLClass)
  return node

isIns = (node) ->
  name = node.text.name
  return (name is 'Alins' || name is 'Ains')

isDel = (node) ->
  name = node.text.name
  return (name is 'Aldel' || name is 'Adel')

isFlattenable = (node) ->
  switch node.text.name
    when "Alins", "Aldel", "Ains", "Adel" then return false
    else return true

checkNode(file)
nfile = setStroke(file, 'black')
nfile = setHTMLClass(collapseTree(nfile))
fs.writeFileSync('../Visualiser/patch.json', JSON.stringify(nfile, null, 2))