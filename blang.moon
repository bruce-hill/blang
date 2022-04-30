#!/usr/bin/env moon
bp = require 'bp'
moon = require 'moon'
concat = table.concat

log = (...)->
    t = {...}
    io.stderr\write concat(t, " ").."\n"

syntax_file = io.open "syntax.bp"
syntax = syntax_file\read "*a"
blang = bp.compile syntax
assert blang, "Failed to compile"

log "Loaded syntax"

skip_tags = __tag:1, start:1, after:1, [0]:1

viz = =>
    if type(@) != 'table'
        return "\x1b[34m#{@}\x1b[m"

    children = ["#{k}=#{viz(v)}" for k,v in pairs(@) when not skip_tags[k]]
    body = #children > 0 and concat(children, " ") or viz(@[0])
    return "\x1b[33m#{@__tag or ""}(\x1b[m#{body}\x1b[33m)\x1b[m"

local compile_stmt, to_reg

strings = {}
functions = {}

fresh_reg = (types)->
    for i=1,999
        return "%x#{i}" unless types["%x#{i}"]

expr_compilers =
    Var: (types)=>
        if types[@[0]]
            return "%#{@[0]}", ""
        else
            return "$#{@[0]}", ""
    Int: (types)=>
        reg = fresh_reg types
        return reg, "#{reg} =l copy #{@[0]}\n"
    String: => strings[@[0]], ""
    Add: (types)=>
        t2 = setmetatable {}, {__index: types}
        lhs_reg, lhs_code = to_reg @lhs, t2
        t2[lhs_reg] = true
        rhs_reg, rhs_code = to_reg @rhs, t2
        t2[rhs_reg] = true
        ret_reg = fresh_reg t2
        return ret_reg, "#{lhs_code}#{rhs_code}#{ret_reg} =l add #{lhs_reg}, #{rhs_reg}\n"

    Fncall: (types)=>
        t2 = setmetatable {}, {__index: types}
        fn_reg = to_reg @fn, t2
        t2[fn_reg] = true
        arg_regs = {}
        code = ""
        for arg in *@args
            arg_reg, arg_code = to_reg arg, t2
            t2[arg_reg] = arg_reg
            code ..= arg_code
            table.insert arg_regs, arg_reg
        ret_reg = fresh_reg t2
        t2[ret_reg] = true
        code ..= "#{ret_reg} =l call #{fn_reg}(#{concat ["l #{r}" for r in *arg_regs], ", "})\n"
        return ret_reg, code
    
stmt_compilers =
    Block: (types)=>
        concat([compile_stmt(stmt, types) for stmt in *@], "")
    Declaration: (types)=>
        t2 = setmetatable {[@var[0]]: @type and @type[0] or true}, {__index: types}
        reg, code = to_reg @value, types
        code = "#{code}%#{@var[0]} =l copy #{reg}\n"
        if @scope
            code ..= compile_stmt @scope, t2
        return code
    FnDecl: (types)=>
        return ""
    Fncall: (types)=>
        _, code = to_reg @, types
        return code
    ["Return-statement"]: (types)=>
        reg, code = to_reg @[1], types
        return "#{code}ret #{reg}\n"
        
to_reg = (types)=>
    if not @__tag
        return to_reg @[1], types
    assert expr_compilers[@__tag], "Not implemented: #{@__tag}"
    expr_compilers[@__tag](@, types)

compile_stmt = (types)=>
    if not @__tag
        return compile_stmt @[1], types
    assert stmt_compilers[@__tag], "Not implemented: #{@__tag}"
    stmt_compilers[@__tag](@, types)

each_tag = (tag)=>
    return unless type(@) == 'table'

    if @__tag == tag
        coroutine.yield @

    for k,v in pairs(@)
        each_tag(v, tag) unless skip_tags[k]

for f in *arg
    log "Compiling #{f}"
    with io.open f
        text = \read "*a"
        --io.write "\x1b[2m#{text}\x1b[m\n"
        ast = blang\match text
        assert ast, "No match!"
        log viz(ast)

        s_i = 0
        string_code = ""
        for s in coroutine.wrap(-> each_tag(ast, "String"))
            s_i += 1
            strings[s[0]] = "$s#{s_i}"
            string_code ..= "data $s#{s_i} = { b #{s[0]}, b 0 }\n"

        fn_code = ""
        for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl"))
            functions[fndec.name[0]] = "$#{fndec.name[0]}"
            types = {}
            args = {}
            for arg in *fndec.args
                table.insert args, "%#{arg.arg[0]}"
                types[arg.arg[0]] = arg.type
            body = compile_stmt(fndec.body, types)\gsub("[^\n]+", "  %0")
            fn_code ..= "function l $#{fndec.name[0]}(#{concat ["l #{a}" for a in *args], ", "}) {\n@start\n#{body}}\n"

        body = compile_stmt(ast, {})\gsub("[^\n]+", "  %0")

        code = "# Source file: #{f}\n\n#{string_code}\n#{fn_code}\nexport function w $main() {\n@start\n#{body}\n  ret 0\n}\n"

        log "\x1b[32m#{code}\x1b[m"

        with io.open f..".ssa", "w"
            \write code
            \close!

        os.execute "qbe #{f}.ssa > #{f}.S && cc #{f}.S -o #{f}.o"

        log "Compiled #{f}!"

        \close!
