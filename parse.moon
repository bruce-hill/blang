#!/usr/bin/env moon
-- Code for parsing

bp = require 'bp'
moon = require 'moon'
import log, viz, print_err from require 'util'

syntax_file = io.open "syntax.bp"
syntax = syntax_file\read "*a"
blang = bp.compile syntax
assert blang, "Failed to compile"

log "Loaded syntax"

each_tag = (tag)=>
    return unless type(@) == 'table'
    coroutine.yield @ if @__tag == tag
    for k,v in pairs(@)
        each_tag(v, tag) if type(v) == 'table'

process = (ast)=>
    for k,v in pairs(ast)
        continue if type(k) == 'string' and k\match("^__")
        if v[1]
            ast[k] = v[1]

add_parenting = (ast)->
    for k,node in pairs ast
        if type(node) == 'table' and not (type(k) == 'string' and k\match("^__"))
            node.__parent = ast
            add_parenting node

parse = (text, filename)->
    log "Parsing..."
    ast = blang\match text
    assert ast, "Completely failed to parse!"
    errors = 0
    for err in coroutine.wrap(->each_tag ast, "ParseError")
        print_err err
        errors += 1

    if errors > 0 then os.exit(1)

    add_parenting ast
    ast.__filename = filename
    return ast

return parse
