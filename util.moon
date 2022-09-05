#!/usr/bin/env moon
concat = table.concat

log = (...)->
    t = {...}
    io.stderr\write concat(t, " ").."\n"

viz = =>
    if type(@) != 'table'
        return "\x1b[34m#{@}\x1b[m"

    children = ["#{k}=#{viz(v)}" for k,v in pairs(@) when type(v) == 'table' and not (type(k) == 'string' and k\match("^__"))]
    body = #children > 0 and concat(children, " ") or viz(@[0])
    return "\x1b[33m#{@__tag or ""}:#{@__type or ""}(\x1b[m#{body}\x1b[33m)\x1b[m"

local cur_filename, cur_source
set_file = (filename, source)->
    cur_filename, cur_source = filename, source

get_line_num = (source, pos)->
    if source\sub(pos,pos) == '\n'
        pos -= 1
    n = 0
    for line in source\sub(1,pos-1)\gmatch("[^\n]*")
        n += 1
    return n

get_node_pos = (ast)->
    line = get_line_num cur_source, ast.start
    last = get_line_num cur_source, ast.after-1
    if last == line
        return "#{cur_filename}:#{line}"
    else
        return "#{cur_filename}:#{line}-#{last}"

print_err = (ast, msg, context=1)->
    while ast and not ast.start
        ast = ast.__parent
    assert ast, "Couldn't find AST source code information for printing error message: "..(msg or "")
    startline = get_line_num cur_source, ast.start
    lastline = get_line_num cur_source, ast.after-1
    text = msg or ast[0]
    print "\x1b[31;1;7m#{cur_filename}:#{startline} #{text}\x1b[m"

    pos = 1
    n = 1
    for line in cur_source\gmatch("[^\n]*")
        if n == startline - context or n == lastline + context
            print "\x1b[2m#{("% 4d")\format n}| \x1b[m#{line}"
        elseif n == startline and n == lastline
            print "\x1b[2m#{("% 4d")\format n}| \x1b[m#{line\sub(1,ast.start-pos)}\x1b[0;31;1m#{line\sub(ast.start-pos+1, ast.after-pos)}\x1b[m#{line\sub(ast.after-pos+1,#line)}\x1b[m"
        elseif n == startline
            print "\x1b[2m#{("% 4d")\format n}| \x1b[m#{line\sub(1,ast.start-pos)}\x1b[0;31;1m#{line\sub(ast.start-pos+1,#line)}\x1b[m"
        elseif n == endline
            print "\x1b[2m#{("% 4d")\format n}| \x1b[0;31;1m#{line\sub(1,ast.after-pos)}\x1b[m#{line\sub(ast.after-pos+1,#line)}\x1b[m"
        elseif n > startline
            print "\x1b[2m#{("% 4d")\format n}| \x1b[0;31;1m#{line}\x1b[m"
            
        n += 1
        pos += #line + 1
        if n > lastline + context
            break

node_assert = (assertion, node, msg)->
    if not assertion
        print_err node, msg
        error()
    return assertion

node_error = (node, msg)->
    print_err node, msg
    error()

each_tag = (...)=>
    return unless type(@) == 'table'

    tags = {...}
    for tag in *tags
        coroutine.yield @ if @__tag == tag

    for k,v in pairs(@)
        each_tag(v, ...) if type(v) == 'table' and not (type(k) == 'string' and k\match("^__"))

return (:log, :viz, :print_err, :set_file, :node_assert, :node_error, :get_node_pos, :each_tag)
