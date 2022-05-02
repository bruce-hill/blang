import add_parenting, get_type from require 'typecheck'
import log, viz from require 'util'
concat = table.concat

local compile_stmt, to_reg

strings = {}
functions = {}

fresh_reg = (vars, template="x")->
    for i=1,999
        r = "%#{template}#{i > 1 and i or ""}"
        continue if vars[r]
        vars[r] = true
        return r

label_counts = {}
fresh_label = (template="label")->
    label_counts[template] = (label_counts[template] or 0) + 1
    return "@#{template}#{label_counts[template]}"

get_abity = (t)->
    if type(t) == 'table'
        -- log "Getting type: #{viz t}"
        t = get_type(t)
    if t == "Float"
        return "d"
    else
        return "l"

binop = (op, flop)->
    (vars)=>
        assert @[1] and @[2], "Node doesn't have 2 captures: #{viz @}"
        assert get_type(@[1]) == get_type(@[2]), "Type mismatch"
        abity = get_abity(@[1])
        lhs_reg, lhs_code = to_reg @[1], vars
        vars[lhs_reg] = true
        rhs_reg, rhs_code = to_reg @[2], vars
        vars[rhs_reg] = true
        ret_reg = fresh_reg vars
        return ret_reg, "#{lhs_code}#{rhs_code}#{ret_reg} =#{abity} #{abity == "d" and flop or op} #{lhs_reg}, #{rhs_reg}\n"

expr_compilers =
    Var: (vars)=>
        if vars["%"..@[0]]
            return "%#{@[0]}", ""
        else
            return "$#{@[0]}", ""
    Int: (vars)=>
        reg = fresh_reg vars
        vars[reg] = "Int"
        return reg, "#{reg} =l copy #{@[0]}\n"
    Float: (vars)=>
        reg = fresh_reg vars
        vars[reg] = "Float"
        return reg, "#{reg} =d copy d_#{@[0]}\n"
    String: => strings[@[0]], ""
    Add: binop "add"
    Sub: binop "sub"
    Mul: binop "mul"
    Div: binop "div"
    Or: binop "or"
    Xor: binop "xor"
    And: binop "and"
    Mod: binop "rem"
    Less: binop("csltl", "cltd")
    LessEq: binop("cslel", "cled")
    Greater: binop("csgtl", "cgtd")
    GreaterEq: binop("csgel", "cged")
    Equal: binop "ceql"
    NotEqual: binop "cnel"
    Pow: (vars)=>
        base_reg, base_code = to_reg @base, vars
        -- if get_abity(vars, base_reg) != "d"
        --     base_reg2 = fresh_reg vars
        --     vars[base_reg2] = true
        --     base_code ..= "#{base_reg2} =d copy #{base_reg}\n"
        --     base_reg = base_reg2
            
        exponent_reg, exponent_code = to_reg @exponent, vars
        -- if get_abity(vars, exponent_reg) != "d"
        --     exponent_reg2 = fresh_reg vars
        --     vars[exponent_reg2] = true
        --     exponent_code ..= "#{exponent_reg2} =d copy #{exponent_reg}\n"
        --     exponent_reg = exponent_reg2

        ret_reg = fresh_reg vars
        return ret_reg, "#{base_code}#{exponent_code}#{ret_reg} =d call $pow(d #{base_reg}, d #{exponent_reg})\n"

    Fncall: (vars)=>
        fn_reg = to_reg @fn, vars
        vars[fn_reg] = true
        code = ""
        args = {}
        for arg in *@args
            arg_reg, arg_code = to_reg arg, vars
            vars[arg_reg] = true
            code ..= arg_code
            table.insert args, "#{get_abity arg} #{arg_reg}"
        ret_reg = fresh_reg vars
        unless skip_ret
            code ..= "#{ret_reg} =l "
        code ..= "call #{fn_reg}(#{concat args, ", "})\n"
        return ret_reg, code
    
stmt_compilers =
    Block: (vars)=>
        concat([compile_stmt(stmt, vars) for stmt in *@], "")
    Declaration: (vars)=>
        vars["%#{@var[0]}"] = true
        var_type = @type or get_type @value, vars
        reg, code = to_reg @value, vars
        code = "#{code}%#{@var[0]} =#{get_abity var_type, vars} copy #{reg}\n"
        return code
    Assignment: (vars)=>
        reg, code = to_reg @value, vars
        var_type = get_type(@var, vars)
        code = "#{code}%#{@var[0]} =#{get_abity var_type, vars} copy #{reg}\n"
        return code
    FnDecl: (vars)=> ""
    Fncall: (vars)=>
        r, code = to_reg @, vars
        -- Discard the return value register:
        vars[r] = nil
        code = code\gsub("[^\n]- (call [^\n]*\n)$", "%1")
        return code
    Return: (vars)=>
        reg, code = to_reg @[1], vars
        return "#{code}ret #{reg}\n"
    If: (vars)=>
        code = ""
        end_label = fresh_label "endif"
        false_label = fresh_label "else"
        for cond in *@
            r,cond_code = to_reg cond.condition, vars
            code ..= cond_code
            true_label = fresh_label "iftrue"
            code ..= "jnz #{r}, #{true_label}, #{false_label}\n#{true_label}\n"
            code ..= compile_stmt cond.body, vars
            unless code\match("%f[%w]ret%f[ \n][^\n]*\n$")
                code ..= "jmp #{end_label}\n"
            code ..= "#{false_label}\n"
            false_label = fresh_label "else"
        if @elseBody
            code ..= compile_stmt @elseBody, vars
            unless code\match("%f[%w]ret%f[ \n][^\n]*\n$")
                code ..= "jmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return code
    While: (vars)=>
        loop_label = fresh_label "while"
        body_label = fresh_label "body"
        end_label = fresh_label "endwhile"
        code = "#{loop_label}\n"
        reg,cond_code = to_reg @condition, vars
        code ..= cond_code
        code ..= "jnz #{reg}, #{body_label}, #{end_label}\n"
        code ..= "#{body_label}\n#{compile_stmt @body, vars}"
        unless code\match("%f[%w]ret%f[ \n][^\n]*\n$")
            code ..= "jmp #{loop_label}\n"
        code ..= "#{end_label}\n"
        return code
        
to_reg = (vars, ...)=>
    if not @__tag
        return to_reg @[1], vars
    assert expr_compilers[@__tag], "Not implemented: #{@__tag}"
    expr_compilers[@__tag](@, vars, ...)

compile_stmt = (vars)=>
    if not @__tag
        return compile_stmt @[1], vars
    assert stmt_compilers[@__tag], "Not implemented: #{@__tag}"
    stmt_compilers[@__tag](@, vars)

each_tag = (tag)=>
    return unless type(@) == 'table'

    if @__tag == tag
        coroutine.yield @

    for k,v in pairs(@)
        each_tag(v, tag) if type(v) == 'table'

compile_prog = (ast, filename)->
    add_parenting(ast)
    s_i = 0
    string_code = ""
    for s in coroutine.wrap(-> each_tag(ast, "String"))
        s_i += 1
        strings[s[0]] = "$str#{s_i}"
        string_code ..= "data $str#{s_i} = { b #{s[0]}, b 0 }\n"

    fn_dups = {}
    fn_code = ""
    for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl"))
        functions[fndec.name[0]] = "$#{fndec.name[0]}"
        args = ["#{get_abity arg} %#{arg.arg[0]}" for arg in *fndec.args]
        vars = {"%#{arg.arg[0]}",true for arg in *fndec.args}
        body_code = if fndec.body
            compile_stmt(fndec.body, vars)
        else
            ret_reg, tmp = to_reg fndec.expr, vars
            "#{tmp}ret #{ret_reg}\n"
        body_code = body_code\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))
        ret_type = fndec.return or get_type(fndec.body or fndec.expr)
        fn_code ..= "function #{ret_type == "Void" and "" or get_abity(ret_type).." "}"
        fn_name = "$"..fndec.name[0]
        fn_dups[fn_name] = (fn_dups[fn_name] or 0) + 1
        if fn_dups[fn_name] > 1
            fn_name = "#{fn_name}#{fn_dups[fn_name]}"
        fn_code ..= "$#{fndec.name[0]}(#{concat args, ", "}) {\n@start\n#{body_code}"
        if ret_type == "Void"
            fn_code ..= "  ret\n"
        elseif not fn_code\match("%f[%w]ret%f[ \n][^\n]*\n$")
            fn_code ..= "  ret 0\n"
        fn_code ..= "}\n"

    vars = {}
    body_code = compile_stmt(ast, vars)\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))

    code = "# Source file: #{filename}\n\n"
    code ..= "#{string_code}\n"
    code ..= "#{fn_code}\n"
    code ..= "export function w $main() {\n@start\n#{body_code}  ret 0\n}\n"
    return code

return {:compile_prog}
