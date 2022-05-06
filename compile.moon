Types = require 'typecheck'
import add_parenting, get_type from Types
import log, viz, assert_node, print_err from require 'util'
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

infixop = (op, flop)->
    (vars)=>
        t = get_type @[1]
        if t.abi_type == "d" and flop
            op = flop
        lhs_reg, lhs_code = to_reg @[1], vars
        code = lhs_code
        ret_reg = fresh_reg vars
        for i=2,#@
            rhs = @[i]
            rhs_type = get_type rhs
            assert_node rhs_type == t, rhs, "Expected type: #{t} but got type #{rhs_type}"
            rhs_reg, rhs_code = to_reg rhs, vars
            code ..= rhs_code
            code ..= "#{ret_reg} =#{t.abi_type} #{op} #{lhs_reg}, #{rhs_reg}\n"
            lhs_reg = ret_reg
        return ret_reg, code

update = (op, flop)->
    (vars)=>
        lhs_type = get_type(@[1])
        rhs_type = get_type(@[2])
        assert_node lhs_type == rhs_type, @, "Type mismatch: #{lhs_type} vs #{rhs_type}"
        reg, code = to_reg @[2], vars
        if @[1].__tag == "Var"
            dest,_ = to_reg @[1], vars
            if lhs_type.abi_type == "d" and flop
                op = flop
            code ..= "#{dest} =#{lhs_type.abi_type} #{op} #{dest}, #{reg}\n"
        else
            print_err @, "Not impl: update indexes"
        return code

expr_compilers =
    Var: (vars)=>
        if vars["%"..@[0]]
            return "%#{@[0]}", ""
        else
            return "$#{@[0]}", ""
    Int: (vars)=>
        return "#{@[0]}",""
    Nil: (vars)=> "0",""
    Bool: (vars)=> (@[0] == "yes" and "1" or "0"),""
    Float: (vars)=>
        return "d_#{@[0]}",""
    String: => strings[@[0]], ""
    Negative: (vars)=>
        reg,code = to_reg @[1], vars
        ret = fresh_reg vars, "neg"
        t = get_type @[1]
        assert_node t == Types.Int or t == Types.Float, @, "Invalid type to negate: #{t}"
        return reg, "#{code}#{ret} =#{t.abi_type} neg #{reg}\n"
    IndexedTerm: (vars)=>
        t = get_type @[1]
        if t.__class == Types.ListType
            item_type = t.item_type
            index_type = get_type(@[2])
            assert_node index_type == Types.Int, @[2], "Index is #{index_type} instead of Int"
            list_reg,list_code = to_reg @[1], vars
            index_reg,index_code = to_reg @[2], vars
            code = list_code..index_code
            loc = fresh_reg vars, "item.loc"
            code ..= "#{loc} =l mul #{index_reg}, 8\n"
            code ..= "#{loc} =l add #{loc}, #{list_reg}\n"
            ret = fresh_reg vars, "item"
            code ..= "#{ret} =#{item_type.abi_type} load#{item_type.abi_type} #{loc}\n"
            return ret,code
        elseif t.__class == Types.StructType
            assert_node @[2].__tag == "Var", @[2], "Structs can only be indexed by member"
            member_name = @[2][0]
            assert_node t.members_by_name[member_name], @[2], "Not a valid struct member of #{t}"
            struct_reg,struct_code = to_reg @[1], vars
            i = t.members_by_name[member_name].index
            member_type = t.members_by_name[member_name].type
            code = struct_code
            loc = fresh_reg vars, "member.loc"
            code ..= "#{loc} =l add #{struct_reg}, #{8*(i-1)}\n"
            ret = fresh_reg vars, "member"
            code ..= "#{ret} =#{member_type.abi_type} load#{member_type.abi_type} #{loc}\n"
            return ret,code
        else
            print_err @[1], "Indexing is only valid on lists and structs, not #{t}"
            
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
    Add: infixop "add"
    Sub: infixop "sub"
    Mul: infixop "mul"
    Div: infixop "div"
    Xor: infixop "xor"
    Or: (vars)=>
        true_label = fresh_label "or.true"
        done_label = fresh_label "or.end"
        code = ""
        for val in *@
            assert_node get_type(val) == Types.Bool, val, "Expected Bool here, but got #{get_type val}"
            val_reg, val_code = to_reg val, vars
            false_label = fresh_label "or.false"
            code ..= "#{val_code}jnz #{val_reg}, #{true_label}, #{false_label}\n#{false_label}\n"
        ret_reg = fresh_reg vars, "any"
        code ..= "#{ret_reg} =#{Types.Bool.abi_type} copy 0\njmp #{done_label}\n#{true_label}\n#{ret_reg} =#{Types.Bool.abi_type} copy 1\n#{done_label}\n"
        return ret_reg, code
    And: (vars)=>
        false_label = fresh_label "and.false"
        done_label = fresh_label "and.end"
        code = ""
        for val in *@
            assert_node get_type(val) == Types.Bool, val, "Expected Bool here, but got #{get_type val}"
            val_reg, val_code = to_reg val, vars
            true_label = fresh_label "and.true"
            code ..= "#{val_code}jnz #{val_reg}, #{true_label}, #{false_label}\n#{true_label}\n"
        ret_reg = fresh_reg vars, "any"
        code ..= "#{ret_reg} =#{Types.Bool.abi_type} copy 1\njmp #{done_label}\n#{false_label}\n#{ret_reg} =#{Types.Bool.abi_type} copy 0\n#{done_label}\n"
        return ret_reg, code
    Mod: infixop "rem"
    Less: infixop("csltl", "cltd")
    LessEq: infixop("cslel", "cled")
    Greater: infixop("csgtl", "cgtd")
    GreaterEq: infixop("csgel", "cged")
    Equal: infixop "ceql"
    NotEqual: infixop "cnel"
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
        assert_node @__name, @, "Unreferenceable lambda"
        return @__name,""

    Struct: (vars)=>
        t = get_type @
        struct_size = 8*#t.members
        ret = fresh_reg vars, "#{t.name\lower!}"
        code = "#{ret} =l call $calloc(l 1, l #{struct_size})\n"
        p = fresh_reg vars, "#{t.name\lower!}.member.loc"
        named_members = {m.name[0],m.value[1] for m in *@ when m.name}
        unnamed_members = [m.value[1] for m in *@ when not m.name]
        for i,m in ipairs t.members
            val = if named_members[m.name]
                named_members[m.name]
            elseif #unnamed_members > 0
                tmp = unnamed_members[1]
                table.remove unnamed_members, 1
            else
                nil

            if val
                code ..= "#{p} =l add #{ret}, #{8*(i-1)}\n"
                val_reg,val_code = to_reg val, vars
                code ..= val_code
                m_t = get_type val
                code ..= "store#{m_t.abi_type} #{val_reg}, #{p}\n"
                
        return ret, code


stmt_compilers =
    Block: (vars)=>
        concat([compile_stmt(stmt, vars) for stmt in *@], "")
    Declaration: (vars)=>
        varname = "%#{@var[0]}"
        assert_node not vars[varname], @var, "Variable being shadowed: #{varname}"
        vars[varname] = true
        if @type
            decl_type = Types.parse_type @type[1]
            value_type = get_type @value[1]
            assert_node value_type\is_a(decl_type), @value[1], "Value is type #{value_type}, not declared type #{decl_type}"
        return store_to @var[1], @value[1], vars
    Assignment: (vars)=>
        var_type = get_type @[1]
        value_type = get_type @[2]
        assert_node value_type\is_a(var_type), @[2], "Value is type #{value_type}, but it's being assigned to something with type #{var_type}"
        return store_to @[1], @[2], vars
    AddUpdate: update "add"
    SubUpdate: update "sub"
    MulUpdate: update "mul"
    DivUpdate: update "div"
    OrUpdate: update "or"
    XorUpdate: update "xor"
    AndUpdate: update "and"
    FnDecl: (vars)=> ""
    TypeDeclaration: (vars)=> ""
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
    assert_node expr_compilers[@__tag], @, "Expression compiler implemented for #{@__tag}"
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
            if t.__class == Types.ListType
                assert_node get_type(@[2]) == Types.Int, @[2], "Index is: #{get_type @[2]} instead of Int"
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
            elseif t.__class == Types.StructType
                assert_node @[2].__tag == "Var", @[2], "Structs can only be indexed by member"
                member_name = @[2][0]
                assert_node t.members_by_name[member_name], @[2], "Not a valid struct member of #{t}"
                struct_reg,struct_code = to_reg @[1], vars
                i = t.members_by_name[member_name].index
                member_type = t.members_by_name[member_name].type
                code = struct_code
                dest = fresh_reg vars, "member.loc"
                code ..= "#{dest} =l add #{struct_reg}, #{8*(i-1)}\n"
                val_reg,val_code = to_reg val, vars
                code ..= val_code
                code ..= "store#{member_type.item_type.abi_type} #{val_reg}, #{dest}\n"
                return code
            else
                print_err @[1], "Indexing is only valid on a list or struct, but this is a #{t}"
        else
            error "Not implemented: store to #{@__tag}"

compile_stmt = (vars)=>
    if not @__tag
        return compile_stmt @[1], vars
    assert_node stmt_compilers[@__tag], @, "Not implemented: #{@__tag}"
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
