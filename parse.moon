#!/usr/bin/env moon
-- Code for parsing

bp = require 'bp'
moon = require 'moon'
import log, viz from require 'util'

syntax_file = io.open "syntax.bp"
syntax = syntax_file\read "*a"
blang = bp.compile syntax
assert blang, "Failed to compile"

log "Loaded syntax"

get_line_num = (source, pos)->
    n = 0
    for _ in source\sub(1,pos-1)\gmatch("[^\n]*")
        n += 1
    return n

get_line = (source, num)->
    for line in source\gmatch("[^\n]*")
        return line if num == 1
        num -= 1
    return ""
        
print_err = (filename, source, ast)->
    linenum = get_line_num source, ast.start
    text = ast.message or "Parse error"
    print "\x1b[31;1;7m#{filename}:#{linenum} #{text}\x1b[m"
    for i=linenum,(get_line_num(source, ast.after))
        print "\x1b[2m#{("% 4d")\format i} | \x1b[0;31;1m#{get_line source, i}\x1b[m"

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
        print_err(filename or "-", text, err)
        errors += 1

    if errors > 0 then os.exit(1)

    log viz(ast)
    return ast

return parse
