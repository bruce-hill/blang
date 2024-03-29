#!/usr/bin/env moon
concat = table.concat

log = (...)->
    t = {...}
    io.stderr\write concat(t, " ").."\n"

id = =>
    mt = getmetatable(@)
    setmetatable(@, nil)
    ret = tostring(@)
    setmetatable(@, mt)
    return ret

viz = =>
    if type(@) != 'table'
        return "\x1b[34m#{@}\x1b[m"

    children = ["#{k}=#{viz(v)}" for k,v in pairs(@) when type(v) == 'table' and not (type(k) == 'string' and k\match("^__"))]
    body = #children > 0 and concat(children, " ") or viz(@[0])
    typeinfo = @__type and "\x1b[2m:#{@__type}\x1b[m" or ""
    varinfo = (@__register or @__location) and "\x1b[2m#{@__register or @__location}\x1b[m" or ""
    return "\x1b[33m#{@__tag or ""}#{typeinfo}\x1b[33m(\x1b[m#{body}#{varinfo}\x1b[33m)\x1b[m"

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

context_err = (ast, msg, context=1)->
    while ast and not ast.start
        ast = ast.__parent
    assert ast, "Couldn't find AST source code information for printing error message: "..(msg or "")
    startline = get_line_num cur_source, ast.start
    lastline = get_line_num cur_source, ast.after-1
    text = msg or ast[0]
    lines = {"\x1b[31;1;7m#{cur_filename}:#{startline}: #{text}\x1b[m"}

    pos = 1
    n = 1
    for line in cur_source\gmatch("[^\n]*")
        if n == startline - context or n == lastline + context
            table.insert lines, "\x1b[2m#{("% 4d")\format n}| \x1b[m#{line}"
        elseif n == startline and n == lastline
            table.insert lines, "\x1b[2m#{("% 4d")\format n}| \x1b[m#{line\sub(1,ast.start-pos)}\x1b[0;31;1m#{line\sub(ast.start-pos+1, ast.after-pos)}\x1b[m#{line\sub(ast.after-pos+1,#line)}\x1b[m"
        elseif n == startline
            table.insert lines, "\x1b[2m#{("% 4d")\format n}| \x1b[m#{line\sub(1,ast.start-pos)}\x1b[0;31;1m#{line\sub(ast.start-pos+1,#line)}\x1b[m"
        elseif n == lastline
            table.insert lines, "\x1b[2m#{("% 4d")\format n}| \x1b[0;31;1m#{line\sub(1,ast.after-pos)}\x1b[m#{line\sub(ast.after-pos+1,#line)}\x1b[m"
        elseif n > startline and n < lastline
            table.insert lines, "\x1b[2m#{("% 4d")\format n}| \x1b[0;31;1m#{line}\x1b[m"
        elseif n >= startline - context and n <= lastline + context
            table.insert lines, "\x1b[2m#{("% 4d")\format n}| \x1b[m#{line}"
            
        n += 1
        pos += #line + 1
        if n > lastline + context
            break
    return table.concat(lines, "\n")

print_err = (...)->
    print(context_err(...))

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

return (:log, :viz, :print_err, :context_err, :set_file, :node_assert, :node_error, :get_node_pos, :each_tag, :id)
