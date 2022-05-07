Types = require 'typecheck'
bp = require 'bp'
import add_parenting, get_type, parse_type from Types
import log, viz, assert_node, print_err from require 'util'
concat = table.concat

has_jump = bp.compile('^_("jmp"/"jnz"/"ret")\\b ..$ $$')

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

each_tag = (...)=>
    return unless type(@) == 'table'

    tags = {...}
    for tag in *tags
        coroutine.yield @ if @__tag == tag

    for k,v in pairs(@)
        each_tag(v, ...) if type(v) == 'table' and k != "__parent"

get_function_reg = (scope, name, arg_signature)->
    return nil unless scope
    switch scope.__tag
        when "Block"
            for i=#scope,1,-1
                stmt = scope[i]
                if stmt.__tag == "FnDecl" and stmt.name[0] == name and get_type(stmt)\arg_signature! == arg_signature
                    return stmt.__name, get_type(stmt)
                elseif stmt.__tag == "Declaration" and stmt.var[0] == name
                    t = if stmt.type
                        parse_type(stmt.type[1])
                    else
                        get_type stmt.value[1]
                    if t.__class == Types.FnType and t\arg_signature! == arg_signature
                        return "%#{stmt.var[0]}", t
        when "FnDecl","Lambda"
            for a in *scope.args
                if a.arg[0] == name
                    t = parse_type(a.type[1])
                    if t.__class == Types.FnType and t\arg_signature! == arg_signature
                        return "%"..a.arg[0], t
        when "For"
            iter_type = get_type(scope.iterable[1])
            if scope.var and scope.var[0] == name and iter_type.__class == Types.ListType and iter_type.item_type.__class == Types.FnType
                return "%"..scope.var[0], iter_type.item_type
    
    return get_function_reg(scope.__parent, name, arg_signature)

infixop = (op, flop, abi_type)->
    (vars)=>
        t = get_type @[1]
        if t.base_type == "d" and flop
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
            code ..= "#{ret_reg} =#{abi_type or t.abi_type} #{op} #{lhs_reg}, #{rhs_reg}\n"
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
            assert_node false, @, "Not impl: update indexes"
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
        t = get_type @[1]
        if t == Types.Int or t == Types.Float
            reg,code = to_reg @[1], vars
            ret = fresh_reg vars, "neg"
            return ret, "#{code}#{ret} =#{t.abi_type} neg #{reg}\n"
        elseif t == Types.Range
            orig,code = to_reg @[1], vars
            range = fresh_reg vars, "neg.range"
            code ..= "#{range} =l call $calloc(l 1, l #{3*8})\n"
            code ..= "call $range_backwards(l #{range}, l #{orig})\n"
            return range, code
        else
            assert_node false, @, "Invalid type to negate: #{t}"
    Len: (vars)=>
        t = get_type @[1]
        if t == Types.Range
            range,code = to_reg @[1], vars
            len = fresh_reg vars, "range.len"
            code ..= "#{len} =l call $range_len(l #{range})\n"
            return len, code
        elseif t.__class == Types.ListType
            list,code = to_reg @[1], vars
            len = fresh_reg vars, "list.len"
            return len, "#{code}#{len} =l loadl #{list}\n"
        else
            assert_node false, @, "Expected List or Range type, not #{t}"
    Not: (vars)=>
        assert_node get_type(@[1]) == Types.Bool, @[1], "Expected a Bool"
        b,code = to_reg @[1], vars
        ret = fresh_reg vars, "not"
        code ..= "#{ret} =l ceql #{b}, 0\n"
        return ret, code
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
            code ..= "#{ret} =#{item_type.abi_type} load#{item_type.base_type} #{loc}\n"
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
            code ..= "#{ret} =#{member_type.abi_type} load#{member_type.base_type} #{loc}\n"
            return ret,code
        elseif t.__class == Types.Range
            index_type = get_type(@[2])
            assert_node index_type == Types.Int, @[2], "Index is #{index_type} instead of Int"
            range_reg,code = to_reg @[1], vars
            index_reg,index_code = to_reg @[1], vars
            code ..= index_code
            ret = fresh_reg vars, "range.nth"
            code ..= "#{ret} =l call $range_nth(l #{range_reg}, l #{index_reg})\n"
            return ret, code
        else
            assert_node false, @[1], "Indexing is only valid on lists and structs, not #{t}"
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
    Range: (vars)=>
        range = fresh_reg vars, "range"
        code = "#{range} =l call $calloc(l 1, l #{3*8})\n"
        first_reg,first_code = to_reg @first[1], vars
        last_reg,last_code = to_reg @last[1], vars
        if @next
            next_reg,next_code = to_reg @next[1], vars
            code ..= "#{first_code}#{next_code}#{last_code}"
            code ..= "call $init_range3(l #{range}, l #{first_reg}, l #{next_reg}, l #{last_reg})\n"
        else
            code ..= "#{first_code}#{last_code}"
            code ..= "call $init_range2(l #{range}, l #{first_reg}, l #{last_reg})\n"
        return range, code
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
        code ..= "#{ret_reg} =#{Types.Bool.base_type} copy 0\njmp #{done_label}\n#{true_label}\n#{ret_reg} =#{Types.Bool.base_type} copy 1\n#{done_label}\n"
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
        code ..= "#{ret_reg} =#{Types.Bool.base_type} copy 1\njmp #{done_label}\n#{false_label}\n#{ret_reg} =#{Types.Bool.base_type} copy 0\n#{done_label}\n"
        return ret_reg, code
    Mod: infixop "rem"
    Less: infixop("csltl", "cltd", "l")
    LessEq: infixop("cslel", "cled", "l")
    Greater: infixop("csgtl", "cgtd", "l")
    GreaterEq: infixop("csgel", "cged", "l")
    Equal: infixop("ceql", "ceql", "l")
    NotEqual: infixop("cnel", "cnel", "l")
    TernaryOp: (vars)=>
        cond_reg,code = to_reg @condition[1], vars
        true_reg,true_code = to_reg @ifTrue[1], vars
        false_reg,false_code = to_reg @ifFalse[1], vars
        true_label = fresh_label "ternary.true"
        false_label = fresh_label "ternary.false"
        end_label = fresh_label "ternary.end"
        ret_reg = fresh_reg vars, "ternary.result"
        code ..= "jnz #{cond_reg}, #{true_label}, #{false_label}\n"
        code ..= "#{true_label}\n#{true_code}#{ret_reg} =#{get_type(@ifTrue[1]).base_type} copy #{true_reg}\njmp #{end_label}\n"
        code ..= "#{false_label}\n#{false_code}#{ret_reg} =#{get_type(@ifFalse[1]).base_type} copy #{false_reg}\njmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return ret_reg, code
    Pow: (vars)=>
        -- TODO: auto-cast ints to doubles
        base_reg, base_code = to_reg @base, vars
        exponent_reg, exponent_code = to_reg @exponent, vars
        ret_reg = fresh_reg vars
        return ret_reg, "#{base_code}#{exponent_code}#{ret_reg} =d call $pow(d #{base_reg}, d #{exponent_reg})\n"

    FnCall: (vars, skip_ret=false)=>
        code = ""
        local fn_type, fn_reg
        target_sig = "(#{concat [tostring(get_type(a)) for a in *@args], ","})"
        if @fn[1].__tag == "Var"
            fn_reg, fn_type = get_function_reg(@, @fn[0], target_sig)
            -- assert_node fn_reg, @fn, "Couldn't find register for function"
            if not fn_reg
                fn_reg = "$"..@fn[0]
        else
            fn_type = get_type @fn[1]
            fn_reg,fn_code = to_reg @fn, vars
            code ..= fn_code

        if fn_type
            assert_node fn_type and fn_type.__class == Types.FnType, @fn[1], "This is not a function, it's a #{fn_type}"

        args = {}
        for arg in *@args
            arg_reg, arg_code = to_reg arg, vars
            code ..= arg_code
            table.insert args, "#{get_type(arg).abi_type} #{arg_reg}"

        if skip_ret
            return nil, "#{code}call #{fn_reg}(#{concat args, ", "})\n"

        ret_reg = fresh_reg vars
        ret_type = fn_type and fn_type.return_type or get_type(@)
        code ..= "#{ret_reg} =#{ret_type.abi_type} call #{fn_reg}(#{concat args, ", "})\n"
        return ret_reg, code

    Lambda: (vars)=>
        assert_node @__name, @, "Unreferenceable lambda"
        return @__name,""

    Struct: (vars)=>
        t = get_type @
        struct_size = 8*#t.members
        ret = fresh_reg vars, "#{t.name\lower!}"
        code = "#{ret} =#{t.abi_type} call $calloc(l 1, l #{struct_size})\n"
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
                code ..= "store#{m_t.base_type} #{val_reg}, #{p}\n"
                
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
    Pass: (vars)=> ""
    TypeDeclaration: (vars)=> ""
    FnCall: (vars)=>
        _, code = to_reg @, vars, true
        code = code\gsub("[^\n]- (call [^\n]*\n)$", "%1")
        return code
    Return: (vars)=>
        if @[1]
            reg, code = to_reg @[1], vars
            return "#{code}ret #{reg}\n"
        else
            return "ret\n"
    Stop: (vars)=>
        assert @jump_label, "Jump label should have been populated by outer loop"
        return "jmp #{@jump_label}\n"
    Skip: (vars)=>
        assert @jump_label, "Jump label should have been populated by outer loop"
        return "jmp #{@jump_label}\n"
    If: (vars)=>
        code = ""
        end_label = fresh_label "if.end"
        false_label = fresh_label "if.else"
        for cond in *@
            r,cond_code = to_reg cond.condition, vars
            code ..= cond_code
            true_label = fresh_label "if.true"
            code ..= "jnz #{r}, #{true_label}, #{false_label}\n#{true_label}\n"
            code ..= compile_stmt cond.body, vars
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
            code ..= "#{false_label}\n"
            false_label = fresh_label "if.else"
        if @elseBody
            code ..= compile_stmt @elseBody, vars
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return code
    When: (vars)=>
        t = get_type @what[1]
        what_reg,code = to_reg @what[1], vars
        end_label = fresh_label "when.end"
        next_case = fresh_label "when.case"
        next_body = fresh_label "when.body"
        match_reg = fresh_reg vars, "when.matches"
        code ..= "jmp #{next_case}\n"
        for branch in *@branches
            for case in *branch.cases
                assert_node get_type(case)\is_a(t), case, "'when' value is not a #{t}"
                code ..= "#{next_case}\n"
                next_case = fresh_label "when.case"
                case_reg,case_code = to_reg case, vars
                code ..= "#{case_code}#{match_reg} =l ceql #{what_reg}, #{case_reg}\n"
                code ..= "jnz #{match_reg}, #{next_body}, #{next_case}\n"
            code ..= "#{next_body}\n"
            next_body = fresh_label "when.body"
            code ..= compile_stmt branch.body, vars
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
        if @elseBody
            code ..= "#{next_case}\n"
            code ..= compile_stmt @elseBody, vars
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return code
    While: (vars)=>
        -- Rough breakdown:
        -- jmp @while.condition
        -- jnz (condition), @while.body, @while.end
        -- @while.body
        -- // body code
        -- jmp @while.between
        -- // between code
        -- jnz (condition), @while.body, @while.end
        -- @while.end
        cond_label = fresh_label "while.condition"
        body_label = fresh_label "while.body"
        between_label = fresh_label "while.between"
        end_label = fresh_label "while.end"

        for skip in coroutine.wrap(-> each_tag(@, "Skip"))
            if not skip.target or skip.target[0] == "while"
                skip.jump_label = cond_label

        for stop in coroutine.wrap(-> each_tag(@, "Stop"))
            if not stop.target or stop.target[0] == "while"
                stop.jump_label = end_label

        cond_reg,cond_code = to_reg @condition[1], vars
        code = "jmp #{cond_label}\n#{cond_label}\n"
        code ..= cond_code
        code ..= "jnz #{cond_reg}, #{body_label}, #{end_label}\n"
        code ..= "#{body_label}\n#{compile_stmt @body[1], vars}"
        if @between
            code ..= cond_code
            unless has_jump\match(code)
                code ..= "jnz #{cond_reg}, #{between_label}, #{end_label}\n"
            code ..= "#{between_label}\n#{compile_stmt @between[1], vars}"
            unless has_jump\match(code)
                code ..= "jmp #{body_label}\n"
        else
            unless has_jump\match(code)
                code ..= "jmp #{cond_label}\n"
        code ..= "#{end_label}\n"
        return code
    For: (vars)=>
        -- Rough breakdown:
        -- len = #list; i = 1
        -- jmp @for.body
        -- @for.body
        -- item = list[i]
        -- // body code
        -- jmp @for.noskip
        -- i += 1
        -- jnz (i <= len), @for.end, @for.between
        -- @for.between
        -- // between code
        -- jmp @for.body
        -- @for.skip
        -- i += 1
        -- jnz (i <= len), @for.end, @for.body
        -- @for.end
        list_type = get_type @iterable[1]
        assert_node list_type.__class == Types.ListType or list_type == Types.Range, @iterable[1], "Expected a List or Range, not #{list_type}"

        body_label = fresh_label "for.body"
        between_label = fresh_label "for.between"
        noskip_label = fresh_label "for.noskip"
        skip_label = fresh_label "for.skip"
        end_label = fresh_label "for.end"

        for skip in coroutine.wrap(-> each_tag(@, "Skip"))
            if not skip.target or skip.target[0] == "for" or (@var and skip.target[0] == @var[0]) or (@index and skip.target[0] == @index[0])
                skip.jump_label = skip_label

        for stop in coroutine.wrap(-> each_tag(@, "Stop"))
            if not stop.target or stop.target[0] == "for" or (@var and stop.target[0] == @var[0]) or (@index and stop.target[0] == @index[0])
                stop.jump_label = end_label

        i = fresh_reg vars, "i"
        len = fresh_reg vars, "len"

        list_reg,code = to_reg @iterable[1], vars
        code ..= "#{i} =l copy 1\n"
        if list_type == Types.Range
            code ..= "#{len} =l call $range_len(l #{list_reg})\n"
        else
            code ..= "#{len} =l loadl #{list_reg}\n"
        finished = fresh_reg vars, "for.finished"
        code ..= "#{finished} =l csgtl #{i}, #{len}\n"
        code ..= "jnz #{finished}, #{end_label}, #{body_label}\n"
        code ..= "#{body_label}\n"
        if @index
            index_reg = "%#{@index[1]}"
            vars[index_reg] = true
            code ..= "#{index_reg} =l copy #{i}\n"
        if @var
            var_reg = "%#{@var[1]}"
            vars[var_reg] = true
            if list_type == Types.Range
                code ..= "#{var_reg} =l call $range_nth(l #{list_reg}, l #{i})\n"
            else
                item_addr = fresh_reg vars, "item.addr"
                code ..= "#{item_addr} =l mul #{i}, 8\n"
                code ..= "#{item_addr} =l add #{list_reg}, #{item_addr}\n"
                code ..= "#{var_reg} =#{list_type.item_type.abi_type} load#{list_type.item_type.base_type} #{item_addr}\n"
        code ..= "#{compile_stmt @body[1], vars}"
        unless has_jump\match(code)
            code ..= "jmp #{noskip_label}\n"
        code ..= "#{noskip_label}\n"
        code ..= "#{i} =l add #{i}, 1\n"
        code ..= "#{finished} =l csgtl #{i}, #{len}\n"
        if @between
            code ..= "jnz #{finished}, #{end_label}, #{between_label}\n"
            code ..= "#{between_label}\n#{compile_stmt @between[1], vars}"
            unless has_jump\match(code)
                code ..= "jmp #{body_label}\n"
        else
            code ..= "jnz #{finished}, #{end_label}, #{body_label}\n"
        code ..= "#{skip_label}\n"
        code ..= "#{i} =l add #{i}, 1\n"
        code ..= "#{finished} =l csgtl #{i}, #{len}\n"
        code ..= "jnz #{finished}, #{end_label}, #{body_label}\n"
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
                return "#{code}%#{@[0]} =#{get_type(val).base_type} copy #{reg}\n"
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
                code ..= "store#{t.item_type.base_type} #{val_reg}, #{dest}\n"
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
                code ..= "store#{member_type.item_type.base_type} #{val_reg}, #{dest}\n"
                return code
            else
                assert_node false, @[1], "Indexing is only valid on a list or struct, but this is a #{t}"
        else
            error "Not implemented: store to #{@__tag}"

compile_stmt = (vars)=>
    if not @__tag
        return compile_stmt @[1], vars
    assert_node stmt_compilers[@__tag], @, "Not implemented: #{@__tag}"
    stmt_compilers[@__tag](@, vars)

compile_prog = (ast, filename)->
    add_parenting(ast)
    s_i = 0

    type_code = "type :Range = { l, l, l }\n"
    for s in coroutine.wrap(-> each_tag(ast, "StructType"))
        t = parse_type s
        type_code ..= "type :#{t.name} = { #{concat [m.type.abi_type for m in *t.members], ", "} }"

    string_code = ""
    for s in coroutine.wrap(-> each_tag(ast, "String"))
        s_i += 1
        strings[s[0]] = "$str#{s_i}"
        string_code ..= "data $str#{s_i} = { b #{s[0]}, b 0 }\n"

    fn_dups = {}
    fn_code = ""

    vars = {["%__argc"]:true, ["%argc"]:true, ["%argv"]:true}

    declare_func = (fndec)->
        args = ["#{parse_type(arg.type[1]).abi_type} %#{arg.arg[0]}" for arg in *fndec.args]
        fn_vars = {"%#{arg.arg[0]}",true for arg in *fndec.args}
        body_code = if fndec.body[1].__tag == "Block"
            compile_stmt(fndec.body[1], fn_vars)
        else
            ret_reg, tmp = to_reg fndec.body[1], fn_vars
            "#{tmp}ret #{ret_reg}\n"
        body_code = body_code\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))
        fn_type = get_type fndec
        ret_type = fn_type.return_type
        fn_name = fndec.name and "$"..fndec.name[0] or "$lambda"
        fn_dups[fn_name] = (fn_dups[fn_name] or 0) + 1
        if fn_dups[fn_name] > 1
            fn_name ..= ".#{fn_dups[fn_name]}"
        fndec.__name = fn_name
        fn_code ..= "function #{ret_type == Types.Void and "" or ret_type.abi_type.." "}"
        fn_code ..= "#{fn_name}(#{concat args, ", "}) {\n@start\n#{body_code}"
        if ret_type == Types.Void
            fn_code ..= "  ret\n"
        elseif not has_jump\match(fn_code)
            fn_code ..= "  ret 0\n"
        fn_code ..= "}\n"
        return fn_name

    for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl"))
        declare_func fndec
    for lambda in coroutine.wrap(-> each_tag(ast, "Lambda"))
        declare_func lambda

    body_code = compile_stmt(ast, vars)\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))

    code = "# Source file: #{filename}\n\n"
    code ..= "#{type_code}\n" if #type_code > 0
    code ..= "#{string_code}\n" if #string_code > 0
    code ..= "#{fn_code}\n" if #fn_code > 0
    code ..= "export function w $main(w %__argc, l %argv) {\n@start\n  %argc =l extsw %__argc\n#{body_code}  ret 0\n}\n"
    return code

return {:compile_prog}
