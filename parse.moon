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
    if source\sub(pos,pos) == '\n'
        pos -= 1
    n = 0
    for line in source\sub(1,pos-1)\gmatch("[^\n]*")
        n += 1
    return n

-- get_line = (source, num)->
--     for line in source\gmatch("[^\n]*")
--         return line if num == 1
--         num -= 1
--     return ""
        
print_err = (filename, source, ast)->
    startline = get_line_num source, ast.start
    lastline = get_line_num source, ast.after-1
    text = ast.message or "Parse error"
    print "\x1b[31;1;7m#{filename}:#{startline} #{text}\x1b[m"

    pos = 1
    n = 1
    for line in source\gmatch("[^\n]*")
        if n == startline and n == lastline
            print "\x1b[2m#{("% 4d")\format n}| \x1b[m#{line\sub(1,ast.start-pos)}\x1b[0;31;1m#{line\sub(ast.start-pos+1, ast.after-pos)}\x1b[m#{line\sub(ast.after-pos+1,#line)}\x1b[m"
        elseif n == startline
            print "\x1b[2m#{("% 4d")\format n}| \x1b[m#{line\sub(1,ast.start-pos)}\x1b[0;31;1m#{line\sub(ast.start-pos+1,#line)}\x1b[m"
        elseif n == endline
            print "\x1b[2m#{("% 4d")\format n}| \x1b[0;31;1m#{line\sub(1,ast.after-pos)}\x1b[m#{line\sub(ast.after-pos+1,#line)}\x1b[m"
        elseif n > startline
            print "\x1b[2m#{("% 4d")\format n}| \x1b[0;31;1m#{line}\x1b[m"
            
        n += 1
        pos += #line + 1
        if n > lastline
            break
        
    -- for i=linenum,(get_line_num(source, ast.after))
    --     print "\x1b[2m#{("% 4d")\format i} | \x1b[0;31;1m#{get_line source, i}\x1b[m"

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

    return ast

return parse
