#!/usr/bin/env moon
concat = table.concat

log = (...)->
    t = {...}
    io.stderr\write concat(t, " ").."\n"

viz = =>
    if type(@) != 'table'
        return "\x1b[34m#{@}\x1b[m"

    children = ["#{k}=#{viz(v)}" for k,v in pairs(@) when type(v) == 'table']
    body = #children > 0 and concat(children, " ") or viz(@[0])
    return "\x1b[33m#{@__tag or ""}(\x1b[m#{body}\x1b[33m)\x1b[m"

return (:log, :viz)
