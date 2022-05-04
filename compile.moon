Types = require 'typecheck'
import add_parenting, get_type from Types
import log, viz from require 'util'
concat = table.concat

local compile_stmt, to_reg, store_to

strings = {}
duplicate_regs = {}

fresh_reg = (vars, template="x")->
    for i=1,999
        r = if duplicate_regs[template]
            duplicate_regs[template] += 1
            "%#{template}.#{duplicate_regs[template]}"
        else
            duplicate_regs[template] = 1
            "%#{template}"
        continue if vars[r]
        vars[r] = true
        return r

label_counts = {}
fresh_label = (template="label")->
    label_counts[template] = (label_counts[template] or 0) + 1
    return "@#{template}.#{label_counts[template]}"

binop = (op, flop)->
    (vars)=>
        assert @[1] and @[2], "Node doesn't have 2 captures: #{viz @}"
        t = get_type(@[1])
        assert get_type(@[2]) == t, "Type mismatch: #{get_type(@[1])} vs #{get_type(@[2])}"
        lhs_reg, lhs_code = to_reg @[1], vars
        rhs_reg, rhs_code = to_reg @[2], vars
        ret_reg = fresh_reg vars
        if t.abi_type == "d" and flop
            op = flop
        return ret_reg, "#{lhs_code}#{rhs_code}#{ret_reg} =#{t.abi_type} #{op} #{lhs_reg}, #{rhs_reg}\n"

update = (op, flop)->
    (vars)=>
        assert @[1] and @[2], "Node doesn't have 2 captures: #{viz @}"
        --assert @[1].__tag == "Var", "Node should be a var"
        t = get_type @[1]
        assert get_type(@[2]) == t, "Type mismatch"
        reg, code = to_reg @[2], vars
        if @[1].__tag == "Var"
            dest,_ = to_reg @[1], vars
            if t.abi_type == "d" and flop
                op = flop
            code ..= "#{dest} =#{t.abi_type} #{op} #{dest}, #{reg}\n"
        else
            error "Not impl: update indexes"
        return code

expr_compilers =
    Var: (vars)=>
        if vars["%"..@[0]]
            return "%#{@[0]}", ""
        else
            return "$#{@[0]}", ""
    Int: (vars)=>
        return "#{@[0]}",""
    Float: (vars)=>
        return "d_#{@[0]}",""
    String: => strings[@[0]], ""
    Negative: (vars)=>
        reg,code = to_reg @[1], vars
        ret = fresh_reg vars, "neg"
        t = get_type @[1]
        assert t == Types.Int or t == Types.Float, "Invalid type to negate: #{t}"
        return reg, "#{code}#{ret} =#{t.abi_type} neg #{reg}\n"
    IndexedTerm: (vars)=>
        t = get_type @[1]
        assert t.__class == Types.ListType, "Not a list: #{viz @[1]} is: #{t}"
        item_type = t.item_type
        assert get_type(@[2]) == Types.Int, "Bad index"
        list_reg,list_code = to_reg @[1], vars
        index_reg,index_code = to_reg @[2], vars
        code = list_code..index_code
        p = fresh_reg vars, "p"
        code ..= "#{p} =l mul #{index_reg}, 8\n"
        code ..= "#{p} =l add #{p}, #{list_reg}\n"
        reg = fresh_reg vars, "item"
        code ..= "#{reg} =#{item_type.abi_type} load#{item_type.abi_type} #{p}\n"
        return reg,code
    List: (vars)=>
        reg = fresh_reg vars, "list"
        code = "#{reg} =l call $calloc(l #{1 + #@}, l 8)\n"
        -- code = "#{reg} =l alloc8 #{(1 + #@)*8}\n"
        code ..= "storel #{#@}, #{reg}\n"
        if #@ > 0
            p = fresh_reg vars, "p"
            for i,val in ipairs @
                val_reg,val_code = to_reg val, vars
                code ..= val_code
                code ..= "#{p} =l add #{reg}, #{8*i}\n"
                code ..= "storel #{val_reg}, #{p}\n"
        return reg, code
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
        -- TODO: auto-cast ints to doubles
        base_reg, base_code = to_reg @base, vars
        exponent_reg, exponent_code = to_reg @exponent, vars
        ret_reg = fresh_reg vars
        return ret_reg, "#{base_code}#{exponent_code}#{ret_reg} =d call $pow(d #{base_reg}, d #{exponent_reg})\n"

    FnCall: (vars, skip_ret=false)=>
        fn_reg = to_reg @fn, vars
        code = ""
        args = {}
        for arg in *@args
            arg_reg, arg_code = to_reg arg, vars
            code ..= arg_code
            table.insert args, "#{get_type(arg).abi_type} #{arg_reg}"

        if skip_ret
            return nil, "#{code}call #{fn_reg}(#{concat args, ", "})\n"

        ret_reg = fresh_reg vars
        code ..= "#{ret_reg} =#{get_type(@).abi_type} call #{fn_reg}(#{concat args, ", "})\n"
        return ret_reg, code

    Lambda: (vars)=>
        assert @__name, "Unreferenceable lambda: #{viz @}"
        return @__name,""

stmt_compilers =
    Block: (vars)=>
        concat([compile_stmt(stmt, vars) for stmt in *@], "")
    Declaration: (vars)=>
        varname = "%#{@var[0]}"
        assert not vars[varname], "Variable being shadowed: #{var}"
        vars[varname] = true
        if @type
            decl_type = Types.parse_type(@type[1])
            assert get_type(@value[1])\is_a(decl_type), "Type mismatch: #{get_type(@value[1])} is not a #{@type[1][0]}"
        return store_to @var[1], @value[1], vars
    Assignment: (vars)=>
        return store_to @[1], @[2], vars
    AddUpdate: update "add"
    SubUpdate: update "sub"
    MulUpdate: update "mul"
    DivUpdate: update "div"
    OrUpdate: update "or"
    XorUpdate: update "xor"
    AndUpdate: update "and"
    FnDecl: (vars)=> ""
    FnCall: (vars)=>
        _, code = to_reg @, vars, true
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
        body_label = fresh_label "whilebody"
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

store_to = (val, vars, ...)=>
    switch @__tag
        when "Var"
            if vars["%"..@[0]] == "CLOSURE"
                error("Not impl")
            elseif vars["%"..@[0]]
                reg,code = to_reg val, vars, ...
                return "#{code}%#{@[0]} =#{get_type(val).abi_type} copy #{reg}\n"
            else
                error "Undefined variable, or saving to global: #{@[0]}"
        when "IndexedTerm"
            t = get_type @[1]
            assert t.__class == Types.ListType, "Not a list: #{viz @[1]} is: #{t}"
            assert get_type(@[2]) == Types.Int, "Bad index"
            list_reg,list_code = to_reg @[1], vars
            index_reg,index_code = to_reg @[2], vars
            code = list_code..index_code
            dest = fresh_reg vars, "dest"
            code ..= "#{dest} =l mul #{index_reg}, 8\n"
            code ..= "#{dest} =l add #{dest}, #{list_reg}\n"
            val_reg,val_code = to_reg val, vars
            code ..= val_code
            code ..= "store#{t.item_type.abi_type} #{val_reg}, #{dest}\n"
            return code
        else
            error "Not implemented: store to #{@__tag}"
            

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

    declare_func = (fndec)->
        args = ["#{get_type(arg).abi_type} %#{arg.arg[0]}" for arg in *fndec.args]
        vars = {"%#{arg.arg[0]}",true for arg in *fndec.args}
        body_code = if fndec.body[1].__tag == "Block"
            compile_stmt(fndec.body[1], vars)
        else
            ret_reg, tmp = to_reg fndec.body[1], vars
            "#{tmp}ret #{ret_reg}\n"
        body_code = body_code\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))
        fn_type = get_type fndec
        ret_type = fn_type.return_type
        fn_name = fndec.name and "$"..fndec.name[0] or "$lambda"
        fn_dups[fn_name] = (fn_dups[fn_name] or 0) + 1
        if fn_dups[fn_name] > 1
            fn_name ..= ".#{fn_dups[fn_name]}"
        fn_code ..= "function #{ret_type == Types.Void and "" or ret_type.abi_type.." "}"
        fn_code ..= "#{fn_name}(#{concat args, ", "}) {\n@start\n#{body_code}"
        if ret_type == Types.Void
            fn_code ..= "  ret\n"
        elseif not fn_code\match("%f[%w]ret%f[ \n][^\n]*\n$")
            fn_code ..= "  ret 0\n"
        fn_code ..= "}\n"
        return fn_name

    for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl"))
        declare_func fndec
    for lambda in coroutine.wrap(-> each_tag(ast, "Lambda"))
        name = declare_func lambda
        lambda.__name = name

    vars = {["%__argc"]:true, ["%argc"]:true, ["%argv"]:true}
    body_code = compile_stmt(ast, vars)\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))

    code = "# Source file: #{filename}\n\n"
    code ..= "#{string_code}\n" if #string_code > 0
    code ..= "#{fn_code}\n" if #fn_code > 0
    code ..= "export function w $main(w %__argc, l %argv) {\n@start\n  %argc =l extsw %__argc\n#{body_code}  ret 0\n}\n"
    return code

return {:compile_prog}
