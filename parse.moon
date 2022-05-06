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

get_line_num = (source, pos)->
    if source\sub(pos,pos) == '\n'
        pos -= 1
    n = 0
    for line in source\sub(1,pos-1)\gmatch("[^\n]*")
        n += 1
    return n

each_tag = (tag)=>
    return unless type(@) == 'table'
    coroutine.yield @ if @__tag == tag
    for k,v in pairs(@)
        each_tag(v, tag) if type(v) == 'table'

parse = (text, filename)->
    ast = blang\match text
    assert ast, "Completely failed to parse!"
    errors = 0
    for err in coroutine.wrap(->each_tag ast, "ParseError")
        print_err err
        errors += 1

    if errors > 0 then os.exit(1)

    return ast

return parse
