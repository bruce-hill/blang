Types = require 'types'
bp = require 'bp'
import assign_all_types, get_type, parse_type, bind_var, bind_type from require('typecheck')
import log, viz, id, node_assert, node_error, context_err, each_tag from require 'util'
import Measure, register_unit_alias from require 'units'
ListMethods = require 'list_methods'
concat = table.concat

has_jump = bp.compile('^_("jmp"/"jnz"/"ret")\\b ..$ $$')

local stmt_compilers, expr_compilers

nonnil_eq = (t1, t2)-> (t1.nonnil or t1) == (t2.nonnil or t2)

infixop = (env, op)=>
    assert @lhs and @rhs, "Infix node doesn't have lhs/rhs: #{viz @}"
    t = get_type @lhs
    lhs_reg, lhs_code = env\to_reg @lhs
    code = lhs_code
    ret_reg = env\fresh_local "result"
    rhs = @rhs
    rhs_type = get_type rhs
    -- node_assert nonnil_eq(rhs_type, t), rhs, "Expected type: #{t} but got type #{rhs_type}"
    rhs_reg, rhs_code = env\to_reg rhs
    code ..= rhs_code
    if type(op) == 'string'
        code ..= "#{ret_reg} =#{t.base_type} #{op} #{lhs_reg}, #{rhs_reg}\n"
    else
        code ..= op(ret_reg, lhs_reg, rhs_reg)
    return ret_reg, code

comparison = (env, cmp)=>
    t1 = get_type @lhs
    t2 = get_type @rhs
    node_assert t1 == t2, @, "This comparison is between two different types: `#{t1}` and `#{t2}` which is not allowed"

    prev_val = nil
    lhs_reg,code = env\to_reg @lhs
    rhs_reg,rhs_code = env\to_reg @rhs
    code ..= rhs_code

    result = env\fresh_local "comparison"
    if t1\is_a(Types.String)
        tmp = env\fresh_local "comparison.i32"
        code ..= "#{tmp} =w call $strcmp(l #{lhs_reg}, l #{rhs_reg})\n"
        code ..= "#{result} =l extsw #{tmp}\n"
        code ..= "#{result} =l #{cmp} #{result}, 0\n"
    else
        code ..= "#{result} =l #{cmp} #{lhs_reg}, #{rhs_reg}\n"

    return result, code

repeat_loop = (env, make_body)=>
    -- Rough breakdown:
    -- jmp @repeat
    -- @repeat
    -- // body code
    -- jmp @repeat.between
    -- // between code
    -- jmp @repeat
    -- @repeat.end
    repeat_label,between_label,end_label = env\fresh_labels "repeat", "repeat.between", "repeat.end"

    for skip in coroutine.wrap(-> each_tag(@, "Skip"))
        if not skip.target or skip.target[0] == "repeat"
            skip.jump_label = repeat_label

    for stop in coroutine.wrap(-> each_tag(@, "Stop"))
        if not stop.target or stop.target[0] == "repeat"
            stop.jump_label = end_label

    code = "jmp #{repeat_label}\n"
    code ..= env\block repeat_label, ->
        code = ""
        code ..= env\compile_stmt @filter if @filter
        code ..= (make_body and make_body! or env\compile_stmt(@body))
        if @between
            unless has_jump\match(code)
                code ..= "jmp #{between_label}\n"
            code ..= env\block between_label, -> env\compile_stmt(@between)
        unless has_jump\match(code)
            code ..= "jmp #{repeat_label}\n"
        return code
    code ..= "#{end_label}\n"
    return code

while_loop = (env, make_body)=>
    -- Rough breakdown:
    -- jmp @while.condition
    -- jnz (condition), @while.body, @while.end
    -- @while.body
    -- // body code
    -- jmp @while.between
    -- // between code
    -- jnz (condition), @while.body, @while.end
    -- @while.end
    cond_label,body_label,between_label,end_label = env\fresh_labels "while.condition", "while.body", "while.between", "while.end"

    for skip in coroutine.wrap(-> each_tag(@, "Skip"))
        if not skip.target or skip.target[0] == "while"
            skip.jump_label = cond_label

    for stop in coroutine.wrap(-> each_tag(@, "Stop"))
        if not stop.target or stop.target[0] == "while"
            stop.jump_label = end_label

    cond_reg,cond_code = env\to_reg @condition
    code = "jmp #{cond_label}\n"
    code ..= env\block cond_label, ->
        cond_code.."jnz #{cond_reg}, #{body_label}, #{end_label}\n"

    code ..= env\block body_label, ->
        code = ""
        code ..= env\compile_stmt @filter if @filter
        code ..= (make_body and make_body! or env\compile_stmt(@body))
        if @between
            code ..= cond_code
            unless has_jump\match(code)
                code ..= "jnz #{cond_reg}, #{between_label}, #{end_label}\n"
            code ..= env\block between_label, -> env\compile_stmt(@between)
            unless has_jump\match(code)
                code ..= "jmp #{body_label}\n"
        else
            unless has_jump\match(code)
                code ..= "jmp #{cond_label}\n"
        return code

    code ..= "#{end_label}\n"
    return code

class Environment
    new: (@filename)=>
        @strings = {}
        @used_names = {}
        @dups = setmetatable({}, {__index:->0})
        @type_code = ""
        @string_code = ""
        @fn_code = ""
        @main_code = ""
        @tostring_funcs = {}

    inner_scope: (inner_vars=nil)=>
        return setmetatable({used_names:setmetatable(inner_vars or {}, __index:@used_vars)}, {
            __index: @
            __newindex: (inner,k,v)->
                @[k] = v
        })

    fresh_name: (base_name)=>
        base_name = base_name\gsub("[^a-zA-Z0-9_.]", "_")
        @dups[base_name] += 1
        name = "#{base_name}.#{@dups[base_name]}"
        assert not @used_names[name], "How is this used? #{name}"
        @used_names[name] = true
        return name

    fresh_local: (suggestion="x")=> "%"..@fresh_name(suggestion)
    fresh_locals: (...)=>
        locals = {...}
        for i,l in ipairs(locals) do locals[i] = "%"..@fresh_name(l)
        return table.unpack(locals)
    fresh_global: (suggestion="g")=> "$"..@fresh_name(suggestion)
    fresh_label: (suggestion="label")=> "@"..@fresh_name(suggestion)
    fresh_labels: (...)=>
        labels = {...}
        for i,l in ipairs(labels) do labels[i] = "@"..@fresh_name(l)
        return table.unpack(labels)

    block: (label, get_body)=> label.."\n"..get_body(label)

    get_string_reg: (str, suggestion="str")=>
        unless @strings[str]
            name = @fresh_global suggestion
            @strings[str] = name
            @string_code ..= "data #{name} = #{@string_as_data str}\n"
        return @strings[str]

    string_as_data: (str)=>
        chunks = tostring(str)\gsub('[^ !#-[^-~%]]', (c)->"\",b #{c\byte(1)},b\"")\gsub("\n", "\\n")
        return "{b\"#{chunks}\",b 0}\n"

    declare_function: (fndec)=>
        args = ["#{parse_type(arg.type).base_type} #{arg.name.__register}" for arg in *fndec.args]
        if fndec.selfVar
            t = get_type fndec.selfVar, true
            table.insert args, 1, "#{t.base_type} #{fndec.selfVar.__register}"
        fn_scope = @inner_scope {"%#{arg.name[0]}",true for arg in *fndec.args}

        fn_type = get_type fndec
        ret_type = fn_type.return_type
        check_returns = (ast)->
            return if type(ast) != 'table'
            return if ast.__tag == "FnDecl" or ast.__tag == "Lambda" or ast.__tag == "Macro"
            if ast.__tag == "Return"
                unless (ret_type == Types.NilType and not ast.value) or get_type(ast.value)\is_a(ret_type)
                    node_error ast, "Not a valid function return value. Expected type is #{ret_type}, not #{ast.value and get_type(ast.value) or Types.NilType}"
            for k,v in pairs ast
                check_returns(v) if type(v) == 'table' and not (type(k) == 'string' and k\match("^__"))

        check_returns fndec.body

        body_code = if fndec.__tag == "Lambda"
            ret_reg, tmp = fn_scope\to_reg fndec.body
            "#{tmp}ret #{ret_reg}\n"
        elseif fndec.body.__tag == "Block"
            fn_scope\compile_stmt fndec.body
        else
            ret_reg, tmp = fn_scope\to_reg fndec.body
            "#{tmp}ret #{ret_reg}\n"
        body_code = body_code\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))
        fn_name = fndec.__register or node_assert fndec.name.__register, fndec, "Function has no name"
        @fn_code ..= "\nfunction #{ret_type\is_a(Types.Abort) and "" or ret_type.base_type.." "}"
        @fn_code ..= "#{fn_name}(#{concat args, ", "}) {\n@start\n#{body_code}"
        if ret_type\is_a(Types.Abort) and not has_jump\match(@fn_code)
            @fn_code ..= "  ret\n"
        elseif not has_jump\match(@fn_code)
            @fn_code ..= "  ret 0\n"
        @fn_code ..= "}\n"

    get_tostring_fn: (t, scope)=>
        -- HACK: these primitive values' functions only take 1 arg, but it
        -- should be safe to pass them an extra callstack argument, which
        -- they'll just ignore.
        if t\works_like_a(Types.Int)
            return "$bl_tostring_int"
        elseif t\works_like_a(Types.Int32)
            return "$bl_tostring_int32"
        elseif t\works_like_a(Types.Int16)
            return "$bl_tostring_int16"
        elseif t\works_like_a(Types.Int8)
            return "$bl_tostring_int8"
        elseif t\works_like_a(Types.Percent)
            return "$bl_tostring_percent"
        elseif t\works_like_a(Types.Num)
            return "$bl_tostring_float"
        elseif t\works_like_a(Types.Num32)
            return "$bl_tostring_float32"
        elseif t\works_like_a(Types.Bool)
            return "$bl_tostring_bool"
        elseif t\works_like_a(Types.String) or t\is_a(Types.TypeValue)
            return "$bl_string"
        elseif t\works_like_a(Types.Range)
            return "$bl_tostring_range"

        if @tostring_funcs["#{t}"]
            return @tostring_funcs["#{t}"],false

        typename = t\id_str!
        fn_name = @fresh_global "tostring.#{typename}"
        @tostring_funcs["#{t}"] = fn_name

        reg = @fresh_local typename\lower()
        -- To avoid stack overflow on self-referencing structs, pass a callstack
        -- as a stack-allocated linked list and check before recursing
        callstack = "%callstack"
        code = "function l #{fn_name}(#{t.base_type} #{reg}, l #{callstack}) {\n@start\n"

        -- TODO: Check for recursive lists/tables? It probably doesn't matter,
        -- since the type system currently only allows recursive types for
        -- structs, not lists/tables, so cycles can only be achieved with structs.

        dest = @fresh_local "string"
        if t\works_like_a(Types.NilType)
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("nil", "nil")})\n"
        elseif t\works_like_a(Types.Abort)
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("Abort", "Abort")})\n"
        elseif t\works_like_a(Types.OptionalType)
            nil_label,nonnil_label,end_label = @fresh_labels "optional.nil", "optional.nonnil", "optional.end"
            code ..= @check_nil t, reg, nonnil_label, nil_label
            code ..= @block nil_label, ->
                code = "#{dest} =l call $bl_string(l #{@get_string_reg("nil", "nil")})\n"
                code ..= "jmp #{end_label}\n"
                return code
            code ..= @block nonnil_label, ->
                fn = @get_tostring_fn t.nonnil, scope
                code = "#{dest} =l call #{fn}(#{t.nonnil.base_type} #{reg}, l #{callstack})\n"
                code ..= "jmp #{end_label}\n"
                return code
            code ..= "#{end_label}\n"
        elseif t == Types.Value or t == Types.Value32 or t == Types.Value16 or t == Types.Value8
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("<#{t.name}>", t.name)})\n"
        elseif t\works_like_a(Types.EnumType)
            init_fields,fields_exist = @fresh_labels "make_fields", "fields_exist"
            tmp = @fresh_local "fieldname"
            code ..= "#{tmp} =l loadl $#{t\id_str!}.fields\n"
            code ..= "jnz #{tmp}, #{fields_exist}, #{init_fields}\n"
            code ..= @block init_fields, ->
                code = ""
                for field in *t.fields
                    -- str = @fresh_local "str"
                    -- code ..= "#{str} =l call $bl_string(l #{@get_string_reg "#{t.name}.#{field}", "#{t.name}.#{field}"})\n"
                    code ..= "#{tmp} =l add $#{t\id_str!}.fields, #{8*t.field_values[field]}\n"
                    code ..= "storel #{@get_string_reg "#{t.name}.#{field}", "#{t.name}.#{field}"}, #{tmp}\n"
                code ..= "jmp #{fields_exist}\n"
                return code

            code ..= "#{fields_exist}\n"
            code ..= "#{reg} =l mul #{reg}, 8\n"
            code ..= "#{tmp} =l add $#{t\id_str!}.fields, #{reg}\n"
            code ..= "#{dest} =l loadl #{tmp}\n"
        elseif t\works_like_a(Types.ListType)
            buf = @fresh_local "buf"
            code ..= "#{buf} =l call $CORD_from_char_star(l #{@get_string_reg "[", "lsq"})\n"
            item_reg = @fresh_local "item"
            code ..= @for_loop {
                type:t, iter_reg:reg, val_reg:item_reg,
                make_body: ->
                    item_str = @fresh_local "item.string"
                    fn = @get_tostring_fn t.item_type, scope
                    code = "#{item_str} =l call #{fn}(#{t.item_type.base_type} #{item_reg}, l #{callstack})\n"
                    code ..= "#{buf} =l call $CORD_cat(l #{buf}, l #{item_str})\n"
                    return code
                make_between: ->
                    return "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg ", ", "comma.space"})\n"
            }

            code ..= "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg "]", "rsq"})\n"
            code ..= "#{buf} =l call $CORD_to_const_char_star(l #{buf})\n"
            code ..= "#{dest} =l call $bl_string(l #{buf})\n"

        elseif t\works_like_a(Types.TableType)
            buf = @fresh_local "buf"
            code ..= "#{buf} =l call $CORD_from_char_star(l #{@get_string_reg "{", "lbracket"})\n"

            key_reg,value_reg = @fresh_locals "key","value"
            code ..= @for_loop {
                type: t, iter_reg:reg, :key_reg, :value_reg,
                make_body: ->
                    key_str = @fresh_local "key.string"
                    fn = @get_tostring_fn t.key_type, scope
                    code = "#{key_str} =l call #{fn}(#{t.key_type.base_type} #{key_reg}, l #{callstack})\n"
                    code ..= "#{buf} =l call $CORD_cat(l #{buf}, l #{key_str})\n"
                    code ..= "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg "=", "equals"})\n"
                    value_str = @fresh_local "value.string"
                    fn = @get_tostring_fn t.value_type, scope
                    code ..= "#{value_str} =l call #{fn}(#{t.value_type.base_type} #{value_reg}, l #{callstack})\n"
                    code ..= "#{buf} =l call $CORD_cat(l #{buf}, l #{value_str})\n"
                    return code
                make_between: ->
                    return "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg ", ", "comma"})\n"
            }

            code ..= "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg "}", "rbracket"})\n"
            code ..= "#{buf} =l call $CORD_to_const_char_star(l #{buf})\n"
            code ..= "#{dest} =l call $bl_string(l #{buf})\n"

        elseif t\works_like_a(Types.StructType)
            if t.name\match "^Tuple%.[0-9]+$"
                code ..= "#{dest} =l call $CORD_from_char_star(l #{@get_string_reg("{", "curly")})\n"
            else
                code ..= "#{dest} =l call $CORD_from_char_star(l #{@get_string_reg("#{t.name}{", "#{t\id_str!}.name")})\n"

            -- Check callstack for cyclical references
            cycle_next,cycle_check,cycle_found,cycle_notfound,conclusion = @fresh_labels(
                "cycle.check.next", "cycle.check", "cycle.found", "cycle.notfound", "tostring.conclusion")

            walker = @fresh_local "cycle.walker"
            code ..= "#{walker} =l copy #{callstack}\n"
            code ..= "jmp #{cycle_next}\n"
            code ..= @block cycle_next, ->
                return "jnz #{walker}, #{cycle_check}, #{cycle_notfound}\n"
            code ..= @block cycle_check, ->
                cycle_parent = @fresh_local "cycle.parent"
                local code
                code = "#{cycle_parent} =l add #{walker}, 8\n"
                code ..= "#{cycle_parent} =l loadl #{cycle_parent}\n"
                code ..= "#{walker} =l loadl #{walker}\n"
                wasfound = @fresh_local "cycle.wasfound"
                code ..= "#{wasfound} =l ceql #{cycle_parent}, #{reg}\n"
                code ..= "jnz #{wasfound}, #{cycle_found}, #{cycle_next}\n"
                return code

            code ..= @block cycle_found, ->
                local code
                code = "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg "...", "ellipsis"})\n"
                code ..= "jmp #{conclusion}\n"
                return code

            code ..= @block cycle_notfound, ->
                new_callstack = @fresh_local "new.callstack"
                local code
                code = "#{new_callstack} =l alloc8 #{2*8}\n"
                code ..= "storel #{callstack}, #{new_callstack}\n"
                p = @fresh_local "p"
                code ..= "#{p} =l add #{new_callstack}, 8\n"
                code ..= "storel #{reg}, #{p}\n"
                for i,mem in ipairs t.sorted_members
                    if i > 1
                        code ..= "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg ", ", "comma.space"})\n"

                    member_loc = @fresh_local "#{t\id_str!\lower!}.#{mem.name}.loc"
                    code ..= "#{member_loc} =l add #{reg}, #{mem.offset}\n"
                    member_reg = @fresh_local "#{t\id_str!\lower!}.#{mem.name}"
                    if mem.inline
                        code ..= "#{member_reg} =#{mem.type.base_type} copy #{member_loc}\n"
                    else
                        code ..= "#{member_reg} =#{mem.type.base_type} #{mem.type.load} #{member_loc}\n"

                    if mem.name
                        code ..= "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg("#{mem.name}=")})\n"

                    member_str = @fresh_local "#{t\id_str!\lower!}.#{mem.name}.string"
                    fn = @get_tostring_fn mem.type, scope
                    code ..= "#{member_str} =l call #{fn}(#{mem.type.base_type} #{member_reg}, l #{new_callstack})\n"

                    code ..= "#{dest} =l call $CORD_cat(l #{dest}, l #{member_str})\n"
                code ..= "jmp #{conclusion}\n"
                return code

            code ..= @block conclusion, ->
                local code
                code = "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg "}", "close.curly"})\n"
                code ..= "#{dest} =l call $CORD_to_const_char_star(l #{dest})\n"
                code ..= "#{dest} =l call $bl_string(l #{dest})\n"
                return code

        elseif t\works_like_a(Types.UnionType)
            init_fields,fields_exist = @fresh_labels "make_fields", "fields_exist"
            tmp = @fresh_local "fieldname"
            code ..= "#{tmp} =l loadl $#{t\id_str!}.member_names\n"
            code ..= "jnz #{tmp}, #{fields_exist}, #{init_fields}\n"
            code ..= @block init_fields, ->
                code = ""
                for name,info in pairs t.members
                    -- str = @fresh_local "str"
                    -- code ..= "#{str} =l call $bl_string(l #{@get_string_reg "#{t.name}.#{name}", "#{t.name}.#{name}"})\n"
                    code ..= "#{tmp} =l add $#{t\id_str!}.member_names, #{(info.index-1)*8}\n"
                    code ..= "storel #{@get_string_reg "#{t.name}.#{name}", "#{t.name}.#{name}"}, #{tmp}\n"
                code ..= "jmp #{fields_exist}\n"
                return code

            code ..= "#{fields_exist}\n"

            tag,offset,tmp,name,is_tag = @fresh_locals "tag","offset","tmp","name","is_tag"
            val_loc = @fresh_local "val.loc"
            code ..= "#{tag} =l loadl #{reg}\n"
            code ..= "#{offset} =l sub #{tag}, 1\n"
            code ..= "#{offset} =l mul #{offset}, 8\n"
            code ..= "#{name} =l add $#{t\id_str!}.member_names, #{offset}\n"
            code ..= "#{dest} =l loadl #{name}\n"
            code ..= "#{dest} =l call $CORD_cat(l #{@get_string_reg "@", "at"}, l #{dest})\n"
            code ..= "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg ':', "colon"})\n"
            code ..= "#{val_loc} =l add #{reg}, 8\n"
            next_check,done_label = @fresh_labels "check.member","done"
            for name,info in pairs t.members
                check,next_check = next_check, @fresh_label "check.member"
                found_member = @fresh_label "found.member"
                code ..= @block check, ->
                    code = "#{is_tag} =w ceql #{tag}, #{info.index}\n"
                    code ..= "jnz #{is_tag}, #{found_member}, #{next(t.members, name) and next_check or done_label}\n"
                    return code
                code ..= @block found_member, ->
                    val = @fresh_local "val"
                    code = "#{val} =#{info.type.base_type} #{info.type.load} #{val_loc}\n"
                    code ..= "#{tmp} =l call #{@get_tostring_fn info.type, scope}(#{info.type.base_type} #{val}, l #{callstack})\n"
                    code ..= "#{dest} =l call $CORD_cat(l #{dest}, l #{tmp})\n"
                    code ..= "jmp #{done_label}\n"
                    return code
            code ..= "#{done_label}\n"
            code ..= "#{dest} =l call $CORD_to_const_char_star(l #{dest})\n"
            code ..= "#{dest} =l call $bl_string(l #{dest})\n"

        elseif t\works_like_a(Types.FnType)
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("#{t}")})\n"
        elseif t\works_like_a(Types.MeasureType)
            code ..= "#{dest} =l call $bl_tostring_float(d #{reg})\n"
            code ..= "#{dest} =l call $bl_string_append_string(l #{dest}, l #{@get_string_reg("<"..t.units..">", "units")})\n"
        elseif t\works_like_a(Types.Pointer)
            code ..= "#{dest} =l call $bl_tostring_hex(l #{reg})\n"
        else
            error "Unsupported tostring type: #{t\verbose_type!}"

        code ..= "ret #{dest}\n"
        code ..= "}\n"
        code = code\gsub("[^\n]+", =>((@\match("^[@}]") or @\match("^function")) and @ or "  "..@))
        @fn_code ..= code

        return fn_name

    to_reg: (node, ...)=>
        assert expr_compilers[node.__tag], "Expression compiler not implemented for #{node.__tag}"
        return expr_compilers[node.__tag](node, @, ...)

    to_regs: (...)=>
        nodes = {...}
        regs = {}
        codes = {}
        for node in *nodes
            assert expr_compilers[node.__tag], "Expression compiler not implemented for #{node.__tag}"
            reg,node_code = expr_compilers[node.__tag](node, @)
            table.insert(codes, node_code)
            table.insert(regs, reg)
        table.insert(regs, table.concat(codes, ""))
        return table.unpack(regs)

    compile_stmt: (node)=>
        if not node.__tag
            error "WTF: #{viz node}"
            return @compile_stmt node[1]

        if not stmt_compilers[node.__tag] and expr_compilers[node.__tag]
            _,code = expr_compilers[node.__tag](node, @)
            return code

        node_assert stmt_compilers[node.__tag], node, "Not implemented: #{node.__tag}"
        return stmt_compilers[node.__tag](node, @)

    check_nil: (t, reg, nonnil_label, nil_label)=>
        if t == Types.NilType
            return "jmp #{nil_label}\n"
        elseif not t\is_a(Types.OptionalType)
            return "jmp #{nonnil_label}\n"
        elseif t.nil_value == 0
            return "jnz #{reg}, #{nonnil_label}, #{nil_label}\n"
        elseif t.nonnil.base_type == "d" or t.nonnil.base_type == "s"
            int_val,is_nan = @fresh_locals "int_val","is_nan"
            code = "#{int_val} =l cast #{reg}\n"
            code ..= "#{is_nan} =w ceql #{int_val}, #{t.nonnil.nil_value} # Check for nil\n"
            return code.."jnz #{is_nan}, #{nil_label}, #{nonnil_label}\n"
        else
            tmp = @fresh_local "is.nonnil"
            return "#{tmp} =w cne#{t.base_type} #{reg}, #{t.nil_value}\njnz #{tmp}, #{nonnil_label}, #{nil_label}\n"

    check_truthiness: (t, reg, truthy_label, falsey_label)=>
        if t\is_a(Types.Bool)
            return "jnz #{reg}, #{truthy_label}, #{falsey_label}\n"
        elseif t\is_a(Types.NilType)
            return "jmp #{falsey_label}\n"
        elseif t.base_type == "d"
            tmp = @fresh_local "is.nonnil"
            return "#{tmp} =l cod #{reg}, d_0.0 # Test for NaN\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
        elseif t.base_type == "s"
            tmp = @fresh_local "is.nonnil"
            return "#{tmp} =l cos #{reg}, d_0.0 # Test for NaN\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
        elseif t\is_a(Types.OptionalType)
            if t.nonnil\is_a(Types.Bool)
                tmp = @fresh_local "is.true"
                return "#{tmp} =l ceq#{t.base_type} #{reg}, 1\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
            else
                return @check_nil t, reg, truthy_label, falsey_label
        else
            return "jmp #{truthy_label}\n"

    for_loop: (args)=>
        iter_type = assert args.type
        iter_reg = args.iter_reg
        key_reg = args.key_reg
        value_reg = args.value_reg or args.val_reg
        scope = args.scope
        make_body = args.make_body
        make_between = args.make_between
        filter = args.filter

        -- Rough breakdown:
        -- i = 0 | k = NULL
        -- len = #list
        -- jmp @for.next
        -- @for.next
        -- i += 1 | k = bl_table_next(h, k)
        -- jnz (i > len), @for.end, @for.body
        -- @for.body
        -- index = i
        -- item = list[i] | bl_table_get(h, k)
        -- // body code
        -- i += 1 | k = bl_table_next(h, k)
        -- jnz (i <= len), @for.end, @for.between
        -- @for.between
        -- // between code
        -- jmp @for.body
        -- @for.end

        next_label,body_label,between_label,end_label = @fresh_labels "for.next","for.body","for.between","for.end"

        if scope
            for skip in coroutine.wrap(-> each_tag(scope, "Skip"))
                if not skip.target or skip.target[0] == "for" or (key_reg and skip.target.__register == key_reg) or (value_reg and skip.target.__register == value_reg)
                    skip.jump_label = next_label

            for stop in coroutine.wrap(-> each_tag(scope, "Stop"))
                if not stop.target or stop.target[0] == "for" or (key_reg and stop.target.__register == key_reg) or (value_reg and stop.target.__register == value_reg)
                    stop.jump_label = end_label

        i = @fresh_local(iter_type\works_like_a(Types.TableType) and "k" or "i")
        len = @fresh_local "len"
        is_done = @fresh_local "for.is_done"

        code = "# For loop:\n"
        if iter_type\works_like_a(Types.TableType)
            code ..= "#{i} =l copy #{iter_type.key_type.nil_value}\n"
        else
            code ..= "#{i} =l copy 0\n"
        local list_item
        if iter_type\is_a(Types.Range)
            code ..= "#{len} =l call $range_len(l #{iter_reg})\n"
        elseif iter_type\is_a(Types.ListType)
            code ..= "#{len} =l loadl #{iter_reg}\n"
            list_item = @fresh_local "list.item"
            code ..= "#{list_item} =l add #{iter_reg}, 8\n"
            code ..= "#{list_item} =l loadl #{list_item}\n"
        elseif iter_type\is_a(Types.TableType)
            len = nil -- Len is not used for tables
        else
            error "Expected an iterable type, not #{iter_type}"
        code ..= "jmp #{next_label}\n"
        code ..= @block next_label, ->
            code = ""
            if iter_type\is_a(Types.TableType)
                code ..= "#{i} =l call $bl_table_next(l #{iter_reg}, l #{i}, l #{iter_type.key_type.nil_value})\n"
                code ..= "#{is_done} =w ceql #{i}, #{iter_type.key_type.nil_value}\n"
                code ..= "jnz #{is_done}, #{end_label}, #{body_label}\n"
            else
                code ..= "#{i} =l add #{i}, 1\n"
                code ..= "#{is_done} =w csgtl #{i}, #{len}\n"
                code ..= "jnz #{is_done}, #{end_label}, #{body_label}\n"
            return code

        code ..= @block body_label, ->
            TableMethods = require 'table_methods'
            code = ""
            if iter_type\is_a(Types.TableType)
                if key_reg
                    if iter_type.key_type.base_type == "s" or iter_type.key_type.base_type == "d"
                        code ..= "#{key_reg} =#{iter_type.key_type.base_type} cast #{i}\n"
                    else
                        code ..= "#{key_reg} =#{iter_type.key_type.base_type} copy #{i}\n"

                if value_reg
                    value_bits = @fresh_local "value.bits"
                    code ..= "#{value_bits} =l call $bl_table_get(l #{iter_reg}, l #{i}, l #{iter_type.key_type.nil_value}, l #{iter_type.value_type.nil_value})\n"
                    if iter_type.value_type.base_type == "s" or iter_type.value_type.base_type == "d"
                        code ..= "#{value_reg} =#{iter_type.value_type.base_type} cast #{value_bits}\n"
                    else
                        code ..= "#{value_reg} =#{iter_type.value_type.base_type} copy #{value_bits}\n"
            else
                if key_reg
                    code ..= "#{key_reg} =l copy #{i}\n"

                assert value_reg
                if iter_type\is_a(Types.Range)
                    -- TODO: optimize to not use function call and just do var=start ... var += step
                    code ..= "#{value_reg} =l call $range_nth(l #{iter_reg}, l #{i})\n"
                else
                    code ..= "#{value_reg} =#{iter_type.item_type.base_type} #{iter_type.item_type.load} #{list_item}\n"
                    code ..= "#{list_item} =l add #{list_item}, #{iter_type.item_type.bytes}\n"

            if filter
                code ..= @compile_stmt filter

            if make_body
                code ..= make_body(key_reg, value_reg)

            -- If we reached this point, no skips
            unless has_jump\match(code)
                if iter_type\is_a(Types.TableType)
                    code ..= "#{i} =l call $bl_table_next(l #{iter_reg}, l #{i}, l #{iter_type.key_type.nil_value})\n"
                    code ..= "#{is_done} =w ceql #{i}, #{iter_type.key_type.nil_value}\n"
                    code ..= "jnz #{is_done}, #{end_label}, #{between_label}\n"
                else
                    code ..= "#{i} =l add #{i}, 1\n"
                    code ..= "#{is_done} =w csgtl #{i}, #{len}\n"
                    code ..= "jnz #{is_done}, #{end_label}, #{between_label}\n"

            return code

        code ..= @block between_label, ->
            code = ""
            if make_between
                code ..= make_between(key_reg, value_reg)

            unless has_jump\match(code)
                code ..= "jmp #{body_label}\n"
            return code

        code ..= "#{end_label}\n"
        return code


    set_nil: (t, reg)=>
        if t.base_type == "s" or t.base_type == "d"
            return "#{reg} =#{t.base_type} cast #{t.nil_value} # Set to nil\n"
        else
            return "#{reg} =#{t.base_type} copy #{t.nil_value} # Set to nil\n"

    apply_macros: (ast)=>
        substitute = (ast, replacements)->
            return ast unless type(ast) == 'table'

            if ast.__tag == "Var" and replacements[ast[0]]
                return replacements[ast[0]]

            return {k,(if type(k) == 'string' and k\match("^__") then v else substitute(v, replacements)) for k,v in pairs ast}

        macros = {}
        h = 0
        for m in coroutine.wrap(-> each_tag(ast, "Macro"))
            macro_vars = {}
            for dec in coroutine.wrap(-> each_tag(m.body, "Declaration"))
                macro_vars[dec.var[0]] = {[0]:"#{dec.var[0]}.hygienic.#{h}", __tag:"Var"}
                h += 1
            for dec in coroutine.wrap(-> each_tag(m.body, "FnDecl"))
                macro_vars[dec.name[0]] = {[0]:"#{dec.name[0]}.hygienic.#{h}", __tag:"Var"}
                h += 1
            -- TODO: struct, union, enum, etc.

            macros[m.name[0]] or= {}
            macros[m.name[0]][#m.args] = substitute(m, macro_vars)

        apply_macros = (ast)->
            return ast if type(ast) != 'table'
            if ast.__tag == "Macro"
                return {[0]:"pass", __tag:"Pass"}

            if ast.__tag == "FnCall"
                mac = macros[ast.fn[0]]
                mac = mac and mac[#ast]
                if mac
                    body = mac.body
                    while body.__tag == "Block" and #body == 1
                        body = body[1]
                    return apply_macros(substitute(body, {mac.args[i][0], apply_macros(ast[i]) for i=1,#ast}))

            return {k,apply_macros(v) for k,v in pairs(ast) when k != "__parent"}
                
        ast = apply_macros(ast)
        add_parenting = (ast)->
            for k,node in pairs ast
                if type(node) == 'table' and not (type(k) == 'string' and k\match("^__"))
                    node.__parent = ast
                    add_parenting node
        add_parenting(ast)
        log "Post macro: #{viz ast}"
        return ast

    compile_program: (ast, filename)=>
        ast = @apply_macros(ast)

        @type_code = "type :Range = {l,l,l}\n"

        bind_var ast, {
            [0]:"args",
            __tag: "Var",
            __type: Types.ListType(Types.String),
            __location: "$args",
        }
        bind_var ast, {
            [0]:"say",
            __tag: "Var",
            __type: Types.FnType({Types.String}, Types.NilType, {"text"}),
            __register: "$puts",
        }

        for name,t in pairs(Types)
            bind_type ast, {
                [0]: name,
                __tag: "TypeVar",
                __type: Types.TypeValue(t),
            }

        assign_all_types ast, @

        -- print "\n\n#{viz ast}"

        -- Type names:
        for typedecl in coroutine.wrap(-> each_tag(ast, "EnumDeclaration","StructDeclaration","UnionDeclaration","TypeDeclaration"))
            t = get_type(typedecl)
            type_name = "$#{t.type\id_str!}.name"
            @type_code ..= "data #{type_name} = #{@string_as_data tostring(t.type)}\n"
            typedecl.name.__register = type_name

        -- Enum field names
        for e in coroutine.wrap(-> each_tag(ast, "EnumDeclaration"))
            t = get_type(e)
            enum_t = t.type
            fieldnames = "$#{enum_t\id_str!}.fields"
            @type_code ..= "data #{fieldnames} = {#{("l 0,")\rep(enum_t.next_value)}}\n"

        -- Union field names
        for u in coroutine.wrap(-> each_tag(ast, "UnionDeclaration", "UnionType"))
            t = parse_type(u)
            assert t\is_a(Types.UnionType), "#{t}"
            fieldnames = "$#{t\id_str!}.member_names"
            @type_code ..= "data #{fieldnames} = {#{concat ["l 0" for _ in pairs t.members], ", "}}\n"

        is_file_scope = (scope)->
            while scope
                return true if scope == ast
                switch scope.__tag
                    when "FnDecl","Lambda","Macro","For","ConvertDecl"
                        return false
                scope = scope.__parent
            error("Unexpectedly reached a node not parented to top-level AST")

        file_scope_vars = {}
        -- Set up variable registers:
        for v in coroutine.wrap(-> each_tag(ast, "Var"))
            node_assert v.__declaration, v, "No declaration found"
            continue unless v == v.__declaration
            continue if v.__register or v.__location
            if v.__parent.__tag == "FnDecl" and v == v.__parent.name
                v.__register = @fresh_global v[0]
            elseif is_file_scope(v)
                v.__location = @fresh_global v[0]
                table.insert file_scope_vars, v
            else
                v.__register = @fresh_local v[0]

        for v in coroutine.wrap(-> each_tag(ast, "Var"))
            continue if v.__register or v.__location
            node_assert v.__declaration, v, "No declaration found"
            v.__register = v.__declaration.__register
            v.__location = v.__declaration.__location
            node_assert v.__register or v.__location, v, "Couldn't figure out what this variable refers to"

        -- Compile modules:
        for use in coroutine.wrap(-> each_tag(ast, "Use"))
            error "Not implemented"
            module_dirname,module_basename = use.name[0]\match("(.*/)([^/]*)$")
            if not module_dirname
                module_dirname,module_basename = "",modname
            found = false
            for search_path in (os.getenv("BLANG_MODULE_PATHS") or ".")\gmatch("[^:]+")
                unless search_path\match("^/")
                    dirname = filename\match("^.*/") or ""
                    search_path = dirname..search_path
                path = "#{search_path}/#{module_dirname}/#{module_basename}"
                libfile = io.open((path\gsub("([^/]+)$", "lib%1.so")))
                if libfile
                    libfile\close!
                    found = true
                    break
                bl_path = path\gsub("([^/]+)$", "%1.bl")
                bl_file = io.open(bl_path)
                if bl_file
                    bl_file\close!
                    assert os.execute("./blangc -c #{bl_path}"), "Failed to compile dependency module: #{bl_path}"
                    found = true
                    break

            assert found, "Failed to find module: #{use.name[0]}"

        naked_imports = {}
        -- Hook up naked imports
        for use in coroutine.wrap(-> each_tag(ast, "Use"))
            error "Not implemented"
            continue if use.as
            i = 1
            while use.__parent[i] != use
                i += 1
            scope = {table.unpack(use.__parent, i+1)}
            mod_type = get_type(use)
            use.__imports = {}
            for i,mem in ipairs((mod_type.nonnil or mod_type).sorted_members)
                loc = @fresh_global "#{use.name[0]}.#{mem.name}"
                t = use.orElse and mem.type or Types.OptionalType(mem.type)
                pseudo_var = setmetatable({[0]: mem.name, __tag:"Var", __type: t, __location: loc, __from_use:true}, getmetatable(use))
                use.__imports[i] = pseudo_var
                fn_type = mem.type\is_a(Types.FnType) and mem.type or nil
                hook_up_refs pseudo_var, scope, fn_type
                table.insert naked_imports, pseudo_var

        -- Conversion functions
        bind_conversion = (fn)=>
            switch @__tag
                when "As"
                    src_t, dest_t = @expr.__type, parse_type(@type)
                    if src_t and dest_t and fn.__type\matches({src_t}, dest_t)
                        @__converter = fn
                    bind_conversion @expr, fn
                when "Interp"
                    src_t, dest_t = @value.__type, @__parent.__parent.__type
                    if src_t and dest_t and fn.__type\matches({src_t}, dest_t)
                        @__converter = fn
                    bind_conversion @value, fn
                else
                    for k,child in pairs @
                        continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                        bind_conversion child, fn

        for conv in coroutine.wrap(-> each_tag(ast, "ConvertDecl"))
            conv.__register = @fresh_global "convert"
            bind_conversion conv.__parent, conv

        -- Compile functions:
        for lambda in coroutine.wrap(-> each_tag(ast, "Lambda"))
            lambda.__register = @fresh_global "lambda"
        for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl", "Lambda", "ConvertDecl"))
            @declare_function fndec

        exports = {}
        for exp in coroutine.wrap(-> each_tag(ast, "Export"))
            for var in *exp
                table.insert(exports, var)

        -- TODO: check for top-level returns and error if they exist
        body_code = @compile_stmt(ast)\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))

        code = "# Source file: #{filename}\n\n"
        code ..= "#{@type_code}\n" if #@type_code > 0
        code ..= "#{@string_code}\n" if #@string_code > 0
        code ..= "data $args = {l 0}\n"
        code ..= "data $exports = {#{concat [get_type(e).base_type.." 0" for e in *exports], ","}}\n"
        for var in *naked_imports
            code ..= "data #{var.__location} = {#{get_type(var).base_type} 0}\n"
        for var in *file_scope_vars
            code ..= "data #{var.__location} = {#{get_type(var).base_type} 0}\n"
        code ..= "#{@fn_code}\n" if #@fn_code > 0

        code ..= "export function l $load() {\n"
        code ..= "@start\n"
        code ..= body_code

        for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl"))
            if fndec.name[0] == "main" and #fndec.args == 0
                code ..= "  call #{fndec.name.__register}()\n"
                break

        for i,e in ipairs exports
            var_reg,var_code = @to_reg e
            code ..= var_code
            dest = @fresh_local "export.loc"
            code ..= "  #{dest} =l add $exports, #{(i-1)*8}\n"
            code ..= "  storel #{var_reg}, #{dest}\n"
        code ..= "  ret $exports\n"
        code ..= "}\n"

        code ..= "export function w $main(w %argc, l %argv) {\n"
        code ..= "@start\n"
        code ..= "  %argc2 =l extsw %argc\n"
        code ..= "  %args.size =l mul %argc2, 8\n"
        code ..= "  %args.items =l call $gc_alloc(l %args.size)\n"
        code ..= "  call $memcpy(l %args.items, l %argv, l %args.size)\n"
        code ..= "  %args =l call $gc_alloc(l 16)\n"
        code ..= "  storel %argc2, %args\n"
        code ..= "  storel %args, $args\n"
        code ..= "  %args =l add %args, 8\n"
        code ..= "  storel %args.items, %args\n"
        code ..= "  call $load()\n"
        code ..= "  ret 0\n"
        code ..= "}\n"
        source_chunks = ast[0]\gsub('[^ !#-[^-~]', (c)->"\",b #{c\byte(1)},b\"")\gsub("\n", "\\n")
        code ..= "\nexport data $source = {b\"#{source_chunks}\",b 0}\n"
        return code


expr_compilers =
    Var: (env)=>
        return @__register, "" if @__register
        t = get_type(@)
        if @__location
            tmp = env\fresh_local "#{@[0]}.value"
            return tmp, "#{tmp} =#{t.base_type} #{t.load} #{@__location}\n"
        elseif t\is_a(Types.TypeValue)
            return env\get_string_reg(t.type\verbose_type!, @[0]), ""
        node_error @, "This variable is not defined"
    Declaration: (env)=>
        code = env\compile_stmt @
        var_reg,var_code = env\to_reg @var
        return var_reg, code..var_code
    Int: (env)=>
        t = get_type(@)
        s = @[0]\gsub("_","")
        n = if s\match("^0x")
            tonumber(s\sub(3), 16)
        else
            tonumber(s)

        if t\is_a(Types.Num)
            return "d_#{n}",""
        elseif t\is_a(Types.Num32)
            return "s_#{n}",""

        min,max = -(2^(t.bytes*8-1)), 2^(t.bytes*8-1)-2
        if n == t.nil_value
            node_error @, "This value is reserved for represeting `nil` and can't be used as an integer. Consider using a larger integer type."
        elseif n > max
            node_error @, "This value is too large to fit into a #{t.bytes}-byte signed integer (max value: #{math.floor(max)})"
        elseif n < min
            node_error @, "This value is too small to fit into a #{t.bytes}-byte signed integer (min value: #{math.floor(min)})"
        return "#{n}",""
    Float: (env)=>
        s = @[0]\gsub("_","")
        t = get_type(@)
        prefix = t\is_a(Types.Num) and "d" or "s"
        return "#{prefix}_#{tonumber(s)}",""
    Measure: (env)=>
        n = tonumber((@amount[0]\gsub("_","")))
        m = Measure(n, @units[0]\gsub("[<>]",""))
        return "d_#{m.amount}",""
    Percent: (env)=>
        s = @[0]\gsub("_","")\gsub("%%","")
        return "d_#{tonumber(s)/100.0}",""
    Nil: (env)=>
        child = @
        parent = @__parent
        while parent
            if not parent.__tag
                parent = parent.__parent
                continue

            if parent.__tag == "Return"
                while parent and not (parent.__tag == "FnDecl" or parent.__tag == "Lambda")
                    parent,child = parent.__parent,parent
                continue

            if parent.__tag == "Equal" or parent.__tag == "NotEqual"
                other = (child == parent.lhs) and parent.rhs or parent.lhs
                t = get_type(other, true)
                if t\is_a(Types.OptionalType) and t != Types.NilType
                    t = t.nonnil
                -- if t.base_type == "s" or t.base_type == "d"
                --     nil_reg = env\fresh_local "nil"
                --     return nil_reg, "#{nil_reg} =#{t.base_type} cast #{t.nil_value}\n"
                -- else
                return "#{t.nil_value}",""

            t = if parent.__tag == "Declaration"
                get_type parent.value, true
            elseif parent.__tag == "Assignment"
                t = nil
                for i,rhs in ipairs parent.rhs
                    if rhs == child
                        t = get_type parent.lhs[i], true
                        break
                t
            elseif parent.__tag == "StructField"
                field = parent
                while parent.__tag != "Struct" and parent.__tag != "Union"
                    parent = parent.__parent
                struct_type = get_type parent, true
                if field.name
                    struct_type.members[field.name].type
                else
                    field_type = nil
                    for i,f in ipairs field.__parent
                        if f == field
                            field_type = node_assert(struct_type.members[i] or struct_type.sorted_members[i], @, "Not a #{struct_type} field").type
                            break
                    field_type
            elseif parent.__tag == "List"
                get_type(parent, true).item_type
            elseif parent.__tag == "TableEntry"
                entry = parent
                tab = parent.__parent
                while tab.__tag != "Table"
                    tab = tab.__parent
                table_type = get_type(tab, true)
                child == entry.key and table_type.key_type or table_type.value_type
            elseif parent.__tag == "FnDecl" or parent.__tag == "Lambda"
                break
            elseif parent.__tag == "Clause"
                parent,child = parent.__parent,parent
                continue
            else
                get_type(parent, true)

            if t != Types.NilType and t\is_a(Types.OptionalType)
                -- if t.base_type == "s" or t.base_type == "d"
                --     nil_reg = env\fresh_local "nil"
                --     return nil_reg, "#{nil_reg} =#{t.base_type} cast #{t.nil_value}\n"
                -- else
                return "#{t.nil_value}",""
            elseif parent.__tag == "Declaration"
                return "0",""

            parent,child = parent.__parent,parent
        return "0",""
    Bool: (env)=> (@[0] == "yes" and "1" or "0"),""
    Cast: (env)=>
        reg,code = env\to_reg @expr
        cast_type = parse_type @type
        actual_type = get_type(@expr)
        if not actual_type or (actual_type and cast_type.base_type == actual_type.base_type)
            return reg,code
        c = env\fresh_local "casted"
        abt = actual_type.base_type
        cbt = cast_type.base_type
        if actual_type\is_numeric! and cast_type\is_numeric!
            if (abt == "s" or abt == "d") and not (cbt == "s" or cbt == "d")
                return c, code.."#{c} =#{cbt} #{abt}tosi #{reg}\n"
            elseif (cbt == "s" or cbt == "d") and not (abt == "s" or abt == "d")
                return c, code.."#{c} =#{cbt} s#{abt}tof #{reg}\n"

        if abt == "l" and cbt == "w"
            code ..= "#{c} =w copy #{reg}\n"
        elseif abt == "w" and cbt == "l"
            code ..= "#{c} =l extsw #{reg}\n"
        elseif abt == "s" and cbt == "d"
            code ..= "#{c} =d exts #{reg}\n"
        elseif abt == "d" and cbt == "s"
            code ..= "#{c} =#{cast_type.base_type} truncd #{reg}\n"
        else
            code ..= "#{c} =#{cbt} cast #{reg}\n"
        return c,code

    As: (env)=>
        src_type, dest_type = @expr.__type, @__type
        fndec = node_assert @__converter, @, "Couldn't figure out how to convert #{src_type} into #{dest_type}"
        fn_reg = fndec.__register
        reg,code = env\to_reg @expr
        converted = env\fresh_local "converted"
        code ..= "#{converted} =#{dest_type.base_type} call #{fn_reg}(#{src_type.base_type} #{reg})\n"
        return converted,code

    TypeOf: (env)=>
        return env\get_string_reg("#{get_type(@expression)\verbose_type!}", "typename"), ""
    SizeOf: (env)=>
        t = get_type(@expression)
        return "#{t.bytes}", ""
    String: (env)=>
        str = env\fresh_local "str"
        if #@content == 0
            code = "#{str} =l call $bl_string(l #{env\get_string_reg(@content[0])})\n"
            return str, code

        chunks = {}
        i = @content.start
        for interp in *@content
            if interp.start > i
                chunk = @content[0]\sub(1+(i-@content.start), interp.start-@content.start)
                table.insert chunks, chunk unless chunk == ""
            table.insert chunks, interp
            i = interp.after

        if @content.after > i
            chunk = @content[0]\sub(1+(i-@content.start), @content.after-@content.start)
            table.insert chunks, chunk unless chunk == ""

        cord_reg = env\fresh_local "cord.buf"
        code = "#{cord_reg} =l copy 0\n"
        chunk_reg = env\fresh_local "string.chunk"
        for i,chunk in ipairs chunks
            if type(chunk) == 'string'
                code ..= "#{chunk_reg} =l copy #{env\get_string_reg chunk, "str.literal"}\n"
            else
                t = get_type(chunk, true)
                val_reg,val_code = env\to_reg chunk
                code ..= val_code
                if t == Types.String
                    code ..= "#{chunk_reg} =l copy #{val_reg}\n"
                elseif chunk.__converter
                    code ..= "#{chunk_reg} =l call #{chunk.__converter.__register}(#{t.base_type} #{val_reg})\n"
                else
                    fn = env\get_tostring_fn t, @
                    code ..= "#{chunk_reg} =l call #{fn}(#{t.base_type} #{val_reg}, l 0)\n"

            code ..= "#{cord_reg} =l call $CORD_cat(l #{cord_reg}, l #{chunk_reg})\n"
                
        code ..= "#{cord_reg} =l call $CORD_to_const_char_star(l #{cord_reg})\n"
        code ..= "#{str} =l call $bl_string(l #{cord_reg})\n"
        return str,code

    DSL: (env)=>
        str = env\fresh_local "str"
        if #@content == 0
            code = "#{str} =l call $bl_string(l #{env\get_string_reg(@content[0])})\n"
            return str, code

        code = "#{str} =l call $bl_string(l #{env\get_string_reg("", "emptystr")})\n"
        dsl_type = get_type(@)

        stringify = (val)->
            t = get_type(val)
            val_reg,val_code = env\to_reg val
            code ..= val_code
            safe = if t == dsl_type or val.__tag == "Escape" or val.__tag == "Newline"
                val_reg
            else
                converter = node_assert val.__converter, val, "Couldn't figure out how to convert #{val.value.__type} to #{dsl_type}"
                escaped = env\fresh_local "escaped"
                code ..= "#{escaped} =l call #{converter.__register}(#{t.base_type} #{val_reg})\n"
                escaped
            code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{safe})\n"

        i = @content.start
        for interp in *@content
            if interp.start > i
                chunk = @content[0]\sub(1+(i-@content.start), interp.start-@content.start)
                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{env\get_string_reg chunk})\n"

            stringify(interp)
            i = interp.after

        if @content.after > i
            chunk = @content[0]\sub(1+(i-@content.start), @content.after-@content.start)
            code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{env\get_string_reg chunk})\n"

        return str,code
    
    FieldName: (env)=>
        name = env\fresh_local @[0]
        code = "#{name} =l call $bl_string(l #{env\get_string_reg @[0], @[0]})\n"
        return name, code

    Interp: (env)=> env\to_reg @value

    Newline: (env)=> env\get_string_reg("\n", "newline"),""

    Escape: (env)=>
        esc = {a:'\a',b:'\b',t:'\t',n:'\n',r:'\r',v:'\v'}
        text = @[0]\sub(2)
        c = if esc[text]
            esc[text]\byte(1)
        elseif text\match('[0-8][0-8][0-8]')
            tonumber(text, 8)
        elseif text\match('x[0-9a-fA-F][0-9a-fA-F]')
            tonumber(text\sub(2), 16)
        else
            text\byte(1)
        return env\get_string_reg(("%c")\format(c), "char"),""

    Negative: (env)=>
        t = get_type @value
        if t\is_a(Types.Int) or t\is_a(Types.Num) or t\is_a(Types.MeasureType)
            reg,code = env\to_reg @value
            ret = env\fresh_local "neg"
            return ret, "#{code}#{ret} =#{t.base_type} neg #{reg}\n"
        elseif t\is_a(Types.Range)
            orig,code = env\to_reg @value
            range = env\fresh_local "neg.range"
            code ..= "#{range} =l call $range_backwards(l #{orig})\n"
            return range, code
        else
            node_error @, "Invalid type to negate: #{t}"
    Len: (env)=>
        t = get_type @value
        if t\is_a(Types.Range)
            range,code = env\to_reg @value
            len = env\fresh_local "range.len"
            code ..= "#{len} =l call $range_len(l #{range})\n"
            return len, code
        elseif t\is_a(Types.ListType)
            list,code = env\to_reg @value
            len = env\fresh_local "list.len"
            return len, "#{code}#{len} =l loadl #{list}\n"
        elseif t\is_a(Types.TableType)
            tab,code = env\to_reg @value
            len = env\fresh_local "table.len"
            return len, "#{code}#{len} =l call $hashmap_length(l #{tab})\n"
        elseif t\is_a(Types.String)
            str,code = env\to_reg @value
            len = env\fresh_local "str.len"
            return len, "#{code}#{len} =l call $strlen(l #{str})\n"
        else
            node_error @, "Expected List or Range type, not #{t}"

    Not: (env)=>
        t = get_type(@value)
        b,code = env\to_reg @value
        ret = env\fresh_local "not"
        code ..= "#{ret} =w cne#{t.base_type} #{b}, 1\n"
        return ret, code

    IndexedTerm: (env)=>
        t = get_type @value, true
        if t\is_a(Types.TypeValue) and t.type\is_a(Types.EnumType) and @index.__tag == "FieldName"
            value = node_assert t.type.field_values[@index[0]], @, "Couldn't find enum field: .#{@index[0]} on type #{t.type}"
            return "#{value}",""

        is_optional = t\is_a(Types.OptionalType) and t != Types.NilType
        t = t.nonnil if is_optional
        nil_guard = (check_reg, output_reg, output_type, get_nonnil_code)->
            unless is_optional
                return get_nonnil_code!

            ifnil,ifnonnil,done = env\fresh_labels "if.nil", "if.nonnil", "if.nil.done"
            code = env\check_nil get_type(@value), check_reg, ifnonnil, ifnil
            code ..= env\block ifnonnil, -> (get_nonnil_code!.."jmp #{done}\n")
            code ..= env\block ifnil, -> env\set_nil(output_type, output_reg)
            code ..= "#{done}\n"
            return code
            
        if t\is_a(Types.ListType)
            item_type = t.item_type
            index_type = get_type(@index)
            ListMethods = require 'list_methods'
            if index_type\is_a(Types.Int)
                return ListMethods.methods.get_or_fail(@, env)
            elseif index_type\is_a(Types.Range)
                index_reg, index_code = env\to_regs @index
                return ListMethods.methods.range(@, env)
            elseif @index.__tag == "FieldName"
                node_error @, "Field access on lists is not currently supported"
            else
                node_error @index, "Index is #{index_type} instead of Int or Range"
        elseif t\is_a(Types.TableType)
            TableMethods = require "table_methods"
            return TableMethods.methods.get_or_fail(@, env)
        elseif t\is_a(Types.StructType)
            if @__method
                chain = {}
                node = @__method
                while node.__parent
                    table.insert chain, table.find(node.__parent, node)
                    node = node.__parent
                node_assert @__method.__register, @__method, "No register found: #{table.concat chain, "."}\n\n#{viz node}"
                return @__method.__register,""

            member = if @index.__tag == "FieldName"
                member_name = @index[0]
                node_assert t.members[member_name], @index, "Not a valid struct member of #{t}"
                t.members[member_name]
            elseif @index.__tag == "Int"
                i = tonumber(@index[0])
                node_assert 1 <= i and i <= #t.members, @index, "#{t} only has members between 1 and #{#t.members}"
                t.members[i]
            else
                node_error @index, "Structs can only be indexed by a field name or Int literal"
            struct_reg,code = env\to_reg @value
            ret = env\fresh_local "member"
            code ..= nil_guard struct_reg, ret, member.type, ->
                loc = env\fresh_local "member.loc"
                if member.inline
                    return "#{ret} =l add #{struct_reg}, #{member.offset}\n"
                else
                    code = "#{loc} =l add #{struct_reg}, #{member.offset}\n"
                    return code.."#{ret} =#{member.type.base_type} #{member.type.load} #{loc}\n"
            return ret,code
        elseif t\is_a(Types.UnionType)
            node_assert @index.__tag == "FieldName", @, "Not a valid union field name"
            member_name = @index[0]
            member = node_assert t.members[member_name], @index, "Not a valid union member of #{t\verbose_type!}"
            union_reg, code = env\to_reg @value
            is_member,tag,ret = env\fresh_locals "is.member","tag","ret"
            code ..= "#{tag} =l loadl #{union_reg}\n"
            code ..= "#{is_member} =w ceql #{tag}, #{member.index}\n"
            if_tag,use_nil,done = env\fresh_labels "if.tag","use.nil","done"
            code ..= "jnz #{is_member}, #{if_tag}, #{use_nil}\n"
            code ..= env\block if_tag, ->
                value_loc = env\fresh_local "value.loc"
                code = "#{value_loc} =l add #{union_reg}, 8\n"
                code ..= "#{ret} =#{member.type.base_type} #{member.type.load} #{value_loc}\n"
                code ..= "jmp #{done}\n"
                return code
            code ..= env\block use_nil, ->
                env\set_nil(member.type, ret).."jmp #{done}\n"
            code ..= "#{done}\n"
            return ret,code
        elseif t\is_a(Types.Range)
            index_type = get_type(@index)
            -- TODO: Slice ranges
            node_assert index_type\is_a(Types.Int) or index_type == Types.OptionalType(Types.Int), @index, "Index is #{index_type} instead of Int"
            range_reg, index_reg, code = env\to_regs @value, @index
            ret = env\fresh_local "range.nth"
            code ..= nil_guard range_reg, ret, Types.Int, ->
                "#{ret} =l call $range_nth(l #{range_reg}, l #{index_reg})\n"
            return ret, code
        elseif t\is_a(Types.String)
            index_type = get_type(@index)
            str, index_reg, code = env\to_regs @value, @index
            if index_type\is_a(Types.Int) or index_type == Types.OptionalType(Types.Int) -- Get nth character as an Int
                char = env\fresh_local "char"
                code ..= nil_guard str, char, Types.Int, -> "#{char} =l call $bl_string_nth_char(l #{str}, l #{index_reg})\n"
                return char, code
            elseif index_type\is_a(Types.Range) -- Get a slice of the string
                slice = env\fresh_local "slice"
                code ..= nil_guard str, slice, t, -> "#{slice} =l call $bl_string_slice(l #{str}, l #{index_reg})\n"
                return slice, code
            else
                node_error @index, "Index is #{index_type} instead of Int or Range"
        else
            node_error @value, "Indexing is not valid on type #{t\verbose_type!}"
    List: (env)=>
        list,list_items,size,p = env\fresh_locals "list", "list.items", "list.size", "p"
        code = "#{list} =l call $gc_alloc(l 17)\n"
        if #@ == 0
            return list, code

        code ..= "#{size} =l copy 0\n"
        code ..= "#{list_items} =l copy 0\n"

        item_type = get_type(@).item_type

        add_item = (item)->
            item_reg, code = env\to_reg item
            code ..= "#{size} =l add #{size}, #{item_type.bytes}\n"
            code ..= "#{list_items} =l call $gc_realloc(l #{list_items}, l #{size})\n"
            code ..= "#{p} =l add #{list_items}, #{size}\n"
            code ..= "#{p} =l sub #{p}, #{item_type.bytes}\n"
            code ..= "#{item_type.store} #{item_reg}, #{p}\n"
            return code

        next_label = nil
        for i,val in ipairs @
            if next_label
                code ..= "jmp #{next_label}\n" unless has_jump\match(code)
                code ..= "#{next_label}\n"
                next_label = nil

            switch val.__tag
                when "If"
                    true_label = env\fresh_label "if.true"
                    cond, expr = assert(val[1].condition), assert(val[1].body[1])
                    cond_reg,cond_code = env\to_reg cond
                    code ..= cond_code
                    next_label = env\fresh_label "list.next"
                    code ..= env\check_truthiness get_type(cond), cond_reg, true_label, next_label
                    code ..= "#{true_label}\n"
                    code ..= add_item(expr)
                when "For"
                    iter_reg,iter_code = env\to_regs val.iterable
                    code ..= iter_code
                    key_reg, value_reg = if val.index and val.val
                        val.index.__register, val.val.__register
                    elseif val.val and val.iterable.__type\works_like_a(Types.TableType)
                        val.val.__register, nil
                    elseif val.val
                        nil, val.val.__register
                    else
                        nil, nil
                    code ..= env\for_loop {
                        type: val.iterable.__type, :iter_reg, :key_reg, :value_reg, scope:{val.body, val.filter},
                        make_body: (-> add_item(val.body[1])), filter: val.filter,
                    }
                when "While"
                    code ..= while_loop val, env, (-> add_item(val.body[1]))
                when "Repeat"
                    code ..= repeat_loop val, env, (-> add_item(val.body[1]))
                else
                    code ..= add_item(val)

        if next_label
            code ..= "jmp #{next_label}\n" unless has_jump\match(code)
            code ..= "#{next_label}\n"

        code ..= "#{size} =l div #{size}, #{item_type.bytes}\n"
        code ..= "storel #{size}, #{list}\n"
        items_loc = env\fresh_local "items.loc"
        code ..= "#{items_loc} =l add #{list}, 8\n"
        code ..= "storel #{list_items}, #{items_loc}\n"
        -- List slack is zero, no need to set

        return list, code
    Table: (env)=>
        t = get_type @
        node_assert not t.key_type\is_a(Types.OptionalType) and not t.value_type\is_a(Types.OptionalType), @,
            "Nil cannot be stored in a table, but this table is #{t}"

        tab = env\fresh_local "table"
        code = "#{tab} =l call $hashmap_new(l 0)\n"
        if #@ == 0
            return tab, code

        TableMethods = require "table_methods"
        add_entry = (entry)->
            _,code = TableMethods.methods.set({tab,entry.key,entry.value}, env)
            return code

        next_label = nil
        for i,val in ipairs @
            if next_label
                code ..= "jmp #{next_label}\n" unless has_jump\match(code)
                code ..= "#{next_label}\n"
                next_label = nil

            switch val.__tag
                when "If"
                    true_label = env\fresh_label "if.true"
                    cond, expr = assert(val[1].condition), assert(val[1].body[1])
                    cond_reg,cond_code = env\to_reg cond
                    code ..= cond_code
                    next_label = env\fresh_label "list.next"
                    code ..= env\check_truthiness get_type(cond), cond_reg, true_label, next_label
                    code ..= "#{true_label}\n"
                    code ..= add_entry expr
                when "For"
                    iter_reg,iter_code = env\to_regs val.iterable
                    code ..= iter_code
                    key_reg, value_reg = if val.index and val.val
                        val.index.__register, val.val.__register
                    elseif val.val and val.iterable.__type\works_like_a(Types.TableType)
                        val.val.__register, nil
                    elseif val.val
                        nil, val.val.__register
                    else
                        nil, nil
                    code ..= env\for_loop {
                        type: val.iterable.__type, :iter_reg, :key_reg, :value_reg, scope:{val.body, val.filter},
                        make_body: (-> add_entry(val.body[1])), filter: val.filter,
                    }

                when "While"
                    code ..= while_loop val, env, (-> add_entry(val.body[1]))
                when "Repeat"
                    code ..= repeat_loop val, env, (-> add_entry(val.body[1]))
                else
                    code ..= add_entry(val)

        if next_label
            code ..= "jmp #{next_label}\n" unless has_jump\match(code)
            code ..= "#{next_label}\n"
        return tab, code
    Range: (env)=>
        range = env\fresh_local "range"
        local code
        if @first and @next and @last
            first_reg,next_reg,last_reg,code = env\to_regs @first, @next, @last
            code ..= "#{range} =l call $range_new(l #{first_reg}, l #{next_reg}, l #{last_reg})\n"
        elseif @first and @next and not @last
            first_reg,next_reg,code = env\to_regs @first, @next
            code ..= "#{range} =l call $range_new_first_next(l #{first_reg}, l #{next_reg})\n"
        elseif @first and not @next and @last
            first_reg,last_reg,code = env\to_regs @first, @last
            code ..= "#{range} =l call $range_new_first_last(l #{first_reg}, l #{last_reg})\n"
        elseif @first and not @next and not @last
            first_reg,code = env\to_reg @first
            code ..= "#{range} =l call $range_new_first_last(l #{first_reg}, l 999999999999999999)\n"
        elseif not @first and not @next and @last
            last_reg,code = env\to_reg @last
            code ..= "#{range} =l call $range_new_first_last(l -999999999999999999, l #{last_reg})\n"
        elseif not @first and not @next and not @last
            code = "#{range} =l call $range_new_first_last(l -999999999999999999, l 999999999999999999)\n"
        else
            node_error @, "WTF"
        return range, code
    Or: (env)=>
        done_label = env\fresh_label "or.end"
        code = ""
        t = get_type(@)
        ret_reg = env\fresh_local "any.true"
        for i,val in ipairs @
            val_reg, val_code = env\to_reg val
            code ..= val_code
            false_label = env\fresh_label "or.falsey"
            code ..= "#{ret_reg} =#{t.base_type} copy #{val_reg}\n"
            if i < #@
                code ..= env\check_truthiness get_type(val), val_reg, done_label, false_label
                code ..= "#{false_label}\n"
        code ..= "#{done_label}\n"
        return ret_reg, code
    And: (env)=>
        done_label = env\fresh_label "and.end"
        code = ""
        t = get_type(@)
        ret_reg = env\fresh_local "all.true"
        for i,val in ipairs @
            val_reg, val_code = env\to_reg val
            code ..= val_code
            true_label = env\fresh_label "and.truthy"
            code ..= "#{ret_reg} =#{t.base_type} copy #{val_reg}\n"
            if i < #@
                code ..= env\check_truthiness get_type(val), val_reg, true_label, done_label
                code ..= "#{true_label}\n"
        code ..= "#{done_label}\n"
        return ret_reg, code
    Xor: (env)=>
        for val in *@
            node_assert get_type(val)\is_a(Types.Bool), val, "Expected Bool here, but got #{get_type val}"
        return infixop @, env, "xor"
    AddSub: (env)=>
        t_lhs,t_rhs = get_type(@lhs),get_type(@rhs)
        tl_nn, tr_nn = (t_lhs.nonnil or t_lhs), (t_rhs.nonnil or t_rhs)
        if @op[0] == "+"
            if tl_nn == tr_nn and (tl_nn\is_numeric! or tl_nn\is_a(Types.MeasureType))
                return infixop @, env, "add"
            elseif t_lhs == t_rhs and t_lhs\works_like_a(Types.String)
                return infixop @, env, (ret,lhs,rhs)->
                    "#{ret} =l call $bl_string_append_string(l #{lhs}, l #{rhs})\n"
            elseif t_lhs\works_like_a(Types.ListType) and t_rhs\is_a(t_lhs.item_type)
                return infixop @, env, (ret,lhs,rhs)->
                    list_reg,item_reg,item_type = lhs,rhs,t_rhs
                    new_len,len,new_items,items,new_size,size,tmp = env\fresh_locals "new.len","len","new.items","items","new.size","size","tmp"
                    code = "\n# Append\n"
                    code ..= "#{len} =l loadl #{list_reg}\n"
                    code ..= "#{size} =l mul #{len}, #{item_type.bytes}\n"
                    code ..= "#{new_len} =l add #{len}, 1\n"
                    code ..= "#{tmp} =l add #{list_reg}, 8\n"
                    code ..= "#{items} =l loadl #{tmp}\n"
                    code ..= "#{new_size} =l mul #{new_len}, #{item_type.bytes}\n"
                    code ..= "#{new_items} =l call $gc_alloc(l #{new_size})\n"
                    code ..= "#{tmp} =l call $mempcpy(l #{new_items}, l #{items}, l #{size})\n"
                    code ..= "#{item_type.store} #{item_reg}, #{tmp}\n"
                    code ..= "#{ret} =l call $gc_alloc(l 16)\n"
                    code ..= "storel #{new_len}, #{ret}\n"
                    code ..= "#{tmp} =l add #{ret}, 8\n"
                    code ..= "storel #{new_items}, #{tmp}\n"
                    code ..= "\n"
                    return code
            elseif t_rhs\works_like_a(Types.ListType) and t_lhs\is_a(t_rhs.item_type)
                return infixop @, env, (ret,lhs,rhs)->
                    list_reg,item_reg,item_type = rhs,lhs,t_lhs
                    new_len,len,new_items,items,new_size,size,tmp = env\fresh_locals "new.len","len","new.items","items","new.size","size","tmp"
                    code = "\n# Prepend\n"
                    code ..= "#{len} =l loadl #{list_reg}\n"
                    code ..= "#{size} =l mul #{len}, #{item_type.bytes}\n"
                    code ..= "#{new_len} =l add #{len}, 1\n"
                    code ..= "#{tmp} =l add #{list_reg}, 8\n"
                    code ..= "#{items} =l loadl #{tmp}\n"
                    code ..= "#{new_size} =l mul #{new_len}, #{item_type.bytes}\n"
                    code ..= "#{new_items} =l call $gc_alloc(l #{new_size})\n"
                    code ..= "#{item_type.store} #{item_reg}, #{new_items}\n"
                    code ..= "#{tmp} =l add #{new_items}, #{item_type.bytes}\n"
                    code ..= "call $memcpy(l #{tmp}, l #{items}, l #{size})\n"
                    code ..= "#{ret} =l call $gc_alloc(l 16)\n"
                    code ..= "storel #{new_len}, #{ret}\n"
                    code ..= "#{tmp} =l add #{ret}, 8\n"
                    code ..= "storel #{new_items}, #{tmp}\n"
                    code ..= "\n"
                    return code
            elseif t_lhs == t_rhs and t_lhs\works_like_a(Types.ListType)
                return infixop @, env, (ret,lhs,rhs)->
                    len1,len2,len3,items1,items2,items3,size,tmp = env\fresh_locals "len1","len2","len3","items1","items2","items3","size","tmp"
                    code = "#{len1} =l loadl #{lhs}\n"
                    code ..= "#{len2} =l loadl #{rhs}\n"
                    code ..= "#{lhs} =l add #{lhs}, 8\n"
                    code ..= "#{items1} =l loadl #{lhs}\n"
                    code ..= "#{rhs} =l add #{rhs}, 8\n"
                    code ..= "#{items2} =l loadl #{rhs}\n"
                    code ..= "#{len3} =l add #{len1}, #{len2}\n"
                    code ..= "#{size} =l mul #{len3}, #{t_lhs.item_type.bytes}\n"
                    code ..= "#{ret} =l call $gc_alloc(l 16)\n"
                    code ..= "storel #{len3}, #{ret}\n"
                    code ..= "#{items3} =l call $gc_alloc(l #{size})\n"
                    code ..= "#{tmp} =l add #{ret}, 8\n"
                    code ..= "storel #{items3}, #{tmp}\n"
                    code ..= "#{size} =l mul #{len1}, #{t_lhs.item_type.bytes}\n"
                    code ..= "#{items3} =l call $mempcpy(l #{items3}, l #{items1}, l #{size})\n"
                    code ..= "#{size} =l mul #{len2}, #{t_lhs.item_type.bytes}\n"
                    code ..= "call $memcpy(l #{items3}, l #{items2}, l #{size})\n"
                    return code
            else
                node_error @, "Addition is not supported for #{t_lhs} and #{t_rhs}"
        else -- "-"
            if tl_nn == tr_nn and (tl_nn\is_numeric! or tl_nn\is_a(Types.MeasureType))
                return infixop @, env, "sub"
            else
                node_error @, "Subtraction is not supported for #{t_lhs} and #{t_rhs}"
    MulDiv: (env)=>
        t_lhs,t_rhs = get_type(@lhs),get_type(@rhs)
        tl_nn, tr_nn = (t_lhs.nonnil or t_lhs), (t_rhs.nonnil or t_rhs)
        if @op[0] == "*"
            if tl_nn == tr_nn and tl_nn\is_numeric!
                return infixop @, env, "mul"
            elseif (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.Num)) or (tl_nn\is_a(Types.Num) and tr_nn\is_a(Types.MeasureType)) or (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.MeasureType))
                return infixop @, env, "mul"
            else
                node_error @, "Multiplication is not supported for #{t_lhs} and #{t_rhs}"
        else -- "/"
            if tl_nn == tr_nn and tl_nn\is_numeric!
                return infixop @, env, "div"
            elseif (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.Num)) or (tl_nn\is_a(Types.Num) and tr_nn\is_a(Types.MeasureType)) or (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.MeasureType))
                return infixop @, env, "div"
            else
                node_error @, "Division is not supported for #{t_lhs} and #{t_rhs}"

    AddUpdate: (env)=> "0", env\compile_stmt(@)
    SubUpdate: (env)=> "0", env\compile_stmt(@)
    MulUpdate: (env)=> "0", env\compile_stmt(@)
    OrUpdate: (env)=> "0", env\compile_stmt(@)
    AndUpdate: (env)=> "0", env\compile_stmt(@)
    XorUpdate: (env)=> "0", env\compile_stmt(@)
    ButWithUpdate: (env)=> "0", env\compile_stmt(@)

    Mod: (env)=>
        t = get_type(@)
        if (t.nonnil or t)\is_a(Types.Int) or (t.nonnil or t)\is_a(Types.Num)
            lhs_reg, rhs_reg, code = env\to_regs @lhs, @rhs
            ret = env\fresh_local "remainder"
            if t\is_a(Types.Int)
                code ..= "#{ret} =l call $sane_lmod(l #{lhs_reg}, l #{rhs_reg})\n"
            else
                code ..= "#{ret} =d call $sane_fmod(d #{lhs_reg}, d #{rhs_reg})\n"
            return ret, code
        else
            node_error @, "Modulus is not supported for #{get_type(@lhs)} and #{get_type(@rhs)}"
    Pow: (env)=>
        base_type = get_type @base
        exponent_type = get_type @exponent
        base_reg, exponent_reg, code = env\to_regs @base, @exponent
        ret_reg = env\fresh_local "result"
        if base_type == exponent_type and base_type\is_a(Types.Int)
            return ret_reg, code.."#{ret_reg} =l call $ipow(l #{base_reg}, l #{exponent_reg})\n"
        elseif base_type == exponent_type and base_type\is_a(Types.Num)
            return ret_reg, code.."#{ret_reg} =d call $pow(d #{base_reg}, d #{exponent_reg})\n"
        else
            node_error @, "Exponentiation is not supported for #{base_type} and #{exponent_type}"
    ButWith: (env)=>
        t = get_type @base
        if t\is_a(Types.ListType)
            error "Not impl"
        elseif t\is_a(Types.String)
            error "Not impl"
        elseif t\is_a(Types.StructType)
            lhs_reg,code = env\to_reg @base
            ret = env\fresh_local "#{t.name\lower!}.butwith"
            struct_size = 8*#t.sorted_members
            code ..= "#{ret} =l call $gc_alloc(l #{struct_size})\n"
            code ..= "call $memcpy(l #{ret}, l #{lhs_reg}, l #{struct_size})\n"
            p = env\fresh_local "#{t.name\lower!}.butwith.member.loc"
            for override in *@
                member = if override.index
                    t.members[tonumber(override.index[0])]
                elseif override.field
                    t.members[override.field[0]]
                else
                    node_error override, "I don't know what this is"

                override_type = get_type(override.value, true)
                node_assert override_type\is_a(member.type), override.value, "Not a #{member.type}"
                val_reg,val_code = env\to_reg override.value
                code ..= val_code
                code ..= "#{p} =l add #{ret}, #{member.offset}\n"
                code ..= "#{member.type.store} #{val_reg}, #{p}\n"

            -- code ..= "#{ret} =l call $intern_bytes(l #{ret}, l #{struct_size})\n"
            return ret, code
        else
            node_error @, "| operator is only supported for List and Struct types"
    In: (env)=>
        haystack_type = get_type(@haystack, true)
        needle_type = get_type(@needle, true)
        if haystack_type\is_a(Types.ListType) and needle_type\is_a(haystack_type.item_type)
            found = env\fresh_locals "found"
            done = env\fresh_label "in.done"
            haystack_reg,needle_reg,code = env\to_regs @haystack, @needle
            code ..= "#{found} =w copy 0\n"
            item_reg = env\fresh_local("item")
            code ..= env\for_loop {
                type: haystack_type, iter_reg: haystack_reg, value_reg:item_reg
                make_body: ->
                    base_type = haystack_type.item_type.base_type
                    code = if needle_type == Types.NilType and (base_type == 's' or base_type == 'd')
                        "#{found} =w cuo#{base_type} #{item_reg}, #{base_type}_0.0\n"
                    else
                        "#{found} =w ceq#{base_type} #{item_reg}, #{needle_reg}\n"
                    keep_going = env\fresh_label "keep_going"
                    code ..= "jnz #{found}, #{done}, #{keep_going}\n"
                    code ..= "#{keep_going}\n"
                    return code
            }
            code ..= "#{done}\n"
            return found, code
        elseif haystack_type\is_a(Types.TableType) and needle_type\is_a(haystack_type.key_type)
            needle_reg,haystack_reg,code = env\to_regs @needle, @haystack
            key_getter = env\fresh_local "key.getter"
            TableMethods = require 'table_methods'
            code ..= TableMethods.to_table_format env, haystack_type.key_type, needle_reg, key_getter
            found = env\fresh_local "found"
            code ..= "#{found} =l call $hashmap_get(l #{haystack_reg}, l #{key_getter})\n"
            code ..= "#{found} =l cnel #{found}, 0\n"
            return found, code
        elseif haystack_type == needle_type and haystack_type\is_a(Types.String)
            needle_reg,haystack_reg,code = env\to_regs @needle, @haystack
            found = env\fresh_local "found"
            code ..= "#{found} =l call $strstr(l #{haystack_reg}, l #{needle_reg})\n"
            code ..= "#{found} =l cnel #{found}, 0\n"
            return found, code
        else
            -- TODO: support `Int in Range`, `[Foo] in [Foo]`, `Range in Range` etc.
            node_error @, "Checking if #{needle_type} is in #{haystack_type} is not supported"
    Less: (env)=>
        t = get_type(@lhs)
        sign = (t.base_type == 's' or t.base_type == 'd') and "" or "s"
        return comparison @, env, "c#{sign}lt#{t.base_type}"
    LessEq: (env)=>
        t = get_type(@lhs)
        sign = (t.base_type == 's' or t.base_type == 'd') and "" or "s"
        return comparison @, env, "c#{sign}le#{t.base_type}"
    Greater: (env)=>
        t = get_type(@lhs)
        sign = (t.base_type == 's' or t.base_type == 'd') and "" or "s"
        return comparison @, env, "c#{sign}gt#{t.base_type}"
    GreaterEq: (env)=>
        t = get_type(@lhs)
        sign = (t.base_type == 's' or t.base_type == 'd') and "" or "s"
        return comparison @, env, "c#{sign}ge#{t.base_type}"
    Equal: (env)=>
        lhs_type, rhs_type = get_type(@lhs), get_type(@rhs)
        if lhs_type\is_a(rhs_type) or rhs_type\is_a(lhs_type)
            lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
            result = env\fresh_local "comparison"
            if rhs_type == Types.NilType and (lhs_type.base_type == 's' or lhs_type.base_type == 'd')
                code ..= "#{result} =w cuo#{lhs_type.base_type} #{lhs_reg}, #{lhs_type.base_type}_0.0\n"
            elseif lhs_type == Types.NilType and (rhs_type.base_type == 's' or rhs_type.base_type == 'd')
                code ..= "#{result} =w cuo#{rhs_type.base_type} #{rhs_reg}, #{rhs_type.base_type}_0.0\n"
            else
                code ..= "#{result} =w ceq#{lhs_type.base_type} #{lhs_reg}, #{rhs_reg}\n"
            return result,code
        return comparison @, env, "ceq#{lhs_type.base_type}"
    NotEqual: (env)=>
        lhs_type, rhs_type = get_type(@lhs), get_type(@rhs)
        if lhs_type\is_a(rhs_type) or rhs_type\is_a(lhs_type)
            lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
            result = env\fresh_local "comparison"
            if rhs_type == Types.NilType and (lhs_type.base_type == 's' or lhs_type.base_type == 'd')
                code ..= "#{result} =w co#{lhs_type.base_type} #{lhs_reg}, #{lhs_type.base_type}_0.0\n"
            elseif lhs_type == Types.NilType and (rhs_type.base_type == 's' or rhs_type.base_type == 'd')
                code ..= "#{result} =w co#{rhs_type.base_type} #{rhs_reg}, #{rhs_type.base_type}_0.0\n"
            else
                code ..= "#{result} =w cne#{lhs_type.base_type} #{lhs_reg}, #{rhs_reg}\n"
            return result,code
        return comparison @, env, "cnel"

    FnCall: (env, skip_ret=false)=>
        if @fn.__inline_method
            arg_types = {@fn.value.__type}
            for arg in *@
                if arg.__tag == "KeywordArg"
                    arg_types[arg.name[0]] = arg.value.__type
                else
                    table.insert arg_types, arg.__type
            matches, err = @fn.__type\matches(arg_types)
            node_assert matches, @, err
            return @fn.__inline_method(@, env, skip_ret)

        fn_type = get_type @fn
        fn_reg,code = env\to_reg @fn

        local arg_list
        if fn_type
            node_assert fn_type\is_a(Types.FnType), @fn, "This is not a function, it's a #{fn_type or "???"}"
            arg_types,arg_text = {},{}
            for arg in *@
                if arg.__tag == "KeywordArg"
                    arg_types[arg.name[0]] = get_type(arg.value)
                    table.insert arg_text, "#{arg.name[0]}=#{get_type(arg.value)\verbose_type!}"
                else
                    table.insert arg_types, get_type(arg)
                    table.insert arg_text, "#{get_type(arg)\verbose_type!}"
            if @fn.__method
                table.insert arg_types, 1, get_type(@fn.value)
                table.insert arg_text, 1, "#{get_type(@fn.value)}"

            node_assert fn_type\matches(arg_types), @,
                "This function is being called with #{@fn[0]}(#{concat arg_text, ", "}) but is defined as #{fn_type}"

            kw_args = {}
            pos_args = {}
            if @fn.__method
                arg_reg,arg_code = env\to_reg @fn.value
                code ..= arg_code
                table.insert pos_args, {reg: arg_reg, type: get_type(@fn.value), node: @fn.value}
            for arg in *@
                if arg.__tag == "KeywordArg"
                    arg_reg, arg_code = env\to_reg arg.value
                    code ..= arg_code
                    kw_args[arg.name[0]] = arg_reg
                else
                    arg_reg, arg_code = env\to_reg arg
                    code ..= arg_code
                    table.insert pos_args, {reg: arg_reg, type: get_type(arg), node:arg}

            if fn_type.arg_names
                arg_list = {}
                assert fn_type.arg_names, "No arg names: #{fn_type}"
                for i,name in ipairs fn_type.arg_names
                    arg_reg = kw_args[name] or (table.remove(pos_args, 1) or {}).reg
                    if not arg_reg
                        arg_reg = env\fresh_local name
                        code ..= env\set_nil fn_type.arg_types[i], arg_reg
                    table.insert arg_list, "#{fn_type.arg_types[i].base_type} #{arg_reg}"
            else
                node_assert not next(kw_args), @, "Keyword arguments supplied to a function that doesn't have names for its arguments"
                for _ in *fn_type.arg_types
                    table.remove(pos_args, 1)

            if #pos_args > 0
                node_assert fn_type.varargs, pos_args[1].node, "The arguments from here onwards are not defined in the function signature: #{fn_type}"
                table.insert(arg_list, #fn_type.arg_types+1, "...")
                for arg in *pos_args
                    table.insert arg_list, "#{arg.type.base_type} #{arg.reg}"

        if not arg_list
            arg_list = {}
            for arg in *@
                node_assert arg.__tag != "KeywordArg", arg, "Keyword arguments are not allowed here"
                arg_reg, arg_code = env\to_reg arg
                code ..= arg_code
                table.insert arg_list, "#{get_type(arg).base_type} #{arg_reg}"

        if skip_ret
            return nil, "#{code}call #{fn_reg}(#{concat arg_list, ", "})\n"

        ret_reg = env\fresh_local "return"
        ret_type = fn_type and fn_type.return_type or get_type(@)
        code ..= "#{ret_reg} =#{ret_type.base_type} call #{fn_reg}(#{concat arg_list, ", "}) # Ret type: #{ret_type} base: #{ret_type.base_type}\n"
        return ret_reg, code

    Lambda: (env)=>
        node_assert @__register, @, "Unreferenceable lambda"
        return @__register,""

    Struct: (env)=>
        t = get_type @, true
        ret = env\fresh_local "#{t.name\lower!}"
        code = "#{ret} =l call $gc_alloc(l #{t.memory_size})\n"
        i = 0
        unpopulated = {n,memb for n,memb in pairs t.members}
        for field in *@
            memb = if field.name
                t.members[field.name[0]]
            else
                i += 1
                t.members[i] or t.sorted_members[i]

            node_assert memb, field, "Not a valid struct member of #{t\verbose_type!}"
            m_t = get_type field.value
            node_assert m_t\is_a(memb.type), field, "Expected this value to have type #{memb.type\verbose_type!}, but got #{m_t\verbose_type!}"

            loc = env\fresh_local "#{t\id_str!\lower!}.#{memb.name}.loc"
            code ..= "#{loc} =l add #{ret}, #{memb.offset}\n"
            val_reg,val_code = env\to_reg field.value
            code ..= val_code
            if memb.inline
                code ..= "call $memcpy(l #{loc}, l #{val_reg}, l #{memb.type.memory_size})\n"
            else
                code ..= "#{m_t.store} #{val_reg}, #{loc}\n"
            unpopulated[memb.name] = nil

        for name,memb in pairs unpopulated
            continue unless memb.type\is_a(Types.OptionalType)
            unpopulated[name] = nil
            continue if memb.type.nil_value == 0
            loc = env\fresh_local "#{t\id_str!\lower!}.#{memb.name}.loc"
            code ..= "#{loc} =l add #{ret}, #{memb.offset}\n"
            code ..= "#{memb.type.store} #{memb.type.nil_value}, #{loc}\n"

        for name,memb in pairs unpopulated
            node_error @, "#{name} is a required field for #{t.name}, but was not specified"
            
        -- code ..= "#{ret} =l call $intern_bytes(l #{ret}, l #{struct_size})\n"
        return ret, code

    Union: (env)=>
        t = get_type @
        ret = env\fresh_local "#{t.name\lower!}"
        code = "#{ret} =l call $gc_alloc(l #{t.memory_size})\n"
        member = node_assert t.members[@member[0]], @, "Not a valid union member name: #{@member[0]} in #{t\verbose_type!}"
        code ..= "storel #{member.index}, #{ret}\n"
        val_reg,val_code = env\to_reg @value
        code ..= val_code
        val_loc = env\fresh_local "val.loc"
        code ..= "#{val_loc} =l add #{ret}, 8\n"
        code ..= "storel #{val_reg}, #{val_loc}\n"
        return ret, code

    If: (env)=>
        t = get_type(@)
        ret = t != Types.Abort and env\fresh_local("if.value") or nil
        code = ""
        end_label,false_label = env\fresh_labels "if.end", "if.else"
        for cond in *@
            r,cond_code = env\to_reg cond.condition
            code ..= cond_code
            true_label = env\fresh_label "if.true"
            code ..= env\check_truthiness get_type(cond.condition), r, true_label, false_label
            code ..= "#{true_label}\n"
            block_type = get_type(cond.body)
            if block_type == Types.Abort
                code ..= env\compile_stmt cond.body
            elseif block_type == Types.NilType
                code ..= env\compile_stmt cond.body
                unless has_jump\match(code)
                    code ..= env\set_nil t, ret
            else
                block_reg,block_code = env\to_reg cond.body
                code ..= block_code
                unless has_jump\match(code)
                    code ..= "#{ret} =#{block_type.base_type} copy #{block_reg}\n"
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
            code ..= "#{false_label}\n"
            false_label = env\fresh_label "if.else"

        if @elseBody
            else_type = get_type(@elseBody)
            if else_type == Types.Abort
                code ..= env\compile_stmt @elseBody
            elseif else_type == Types.NilType
                code ..= env\compile_stmt @elseBody
                code ..= env\set_nil(t, ret) unless t == Types.Abort or has_jump\match(code)
            else
                block_reg,block_code = env\to_reg @elseBody
                code ..= block_code
                unless has_jump\match(code)
                    code ..= "#{ret} =#{else_type.base_type} copy #{block_reg}\n"
                
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
        else
            code ..= env\set_nil(t, ret) unless t == Types.Abort or has_jump\match(code)

        code ..= "#{end_label}\n"
        return ret,code

    Do: (env)=>
        end_label,next_label = env\fresh_labels "do.end", "do.else"
        t = get_type(@)
        ret = t != Types.Abort and env\fresh_local("do.value") or nil
        code = "\n# Do block : #{t}\n"
        code ..= env\set_nil(t, ret) if t != Types.Abort and t\is_a(Types.OptionalType)
        for i,block in ipairs @
            for jmp in coroutine.wrap(-> each_tag(block, "Stop"))
                if not jmp.target or jmp.target[0] == "do"
                    jmp.jump_label = end_label
            for jmp in coroutine.wrap(-> each_tag(block, "Skip"))
                if not jmp.target or jmp.target[0] == "do"
                    jmp.jump_label = next_label

            block_type = get_type(block)
            if block_type == Types.Abort
                code ..= env\compile_stmt block
            elseif block_type == Types.NilType
                code ..= env\compile_stmt block
                code ..= env\set_nil t, ret
            else
                block_reg,block_code = env\to_reg block
                code ..= block_code
                code ..= "#{ret} =#{block_type.base_type} copy #{block_reg}\n"
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
            if i < #@
                code ..= "#{next_label}\n"
                next_label = env\fresh_label "do.else"
        code ..= "#{next_label}\n"
        code ..= "jmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return ret,code

    When: (env)=>
        t = get_type(@)
        what_type = get_type @what
        ret = t != Types.Abort and env\fresh_local("when.value") or nil
        what_reg,code = env\to_reg @what
        end_label,next_case,next_body = env\fresh_labels "when.end","when.case","when.body"
        match_reg = env\fresh_local "when.matches"
        code ..= "jmp #{next_case}\n"
        for branch in *@
            for case in *branch.cases
                node_assert get_type(case)\is_a(what_type), case, "'when' value is not a #{what_type}"
                code ..= "#{next_case}\n"
                next_case = env\fresh_label "when.case"
                case_reg,case_code = env\to_reg case
                code ..= "#{case_code}#{match_reg} =l ceql #{what_reg}, #{case_reg}\n"
                code ..= "jnz #{match_reg}, #{next_body}, #{next_case}\n"
            code ..= "#{next_body}\n"
            next_body = env\fresh_label "when.body"

            block_type = get_type(branch.body)
            if block_type == Types.Abort
                code ..= env\compile_stmt branch.body
            elseif block_type == Types.NilType
                code ..= env\compile_stmt branch.body
                code ..= env\set_nil t, ret
            else
                block_reg,block_code = env\to_reg branch.body
                code ..= block_code
                code ..= "#{ret} =#{block_type.base_type} copy #{block_reg}\n" unless t == Types.Abort

            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"

        if @elseBody
            code ..= "#{next_case}\n"

            else_type = get_type(@elseBody)
            if else_type == Types.Abort
                code ..= env\compile_stmt @elseBody
            elseif else_type == Types.NilType
                code ..= env\compile_stmt @elseBody
                code ..= env\set_nil(t, ret) unless t == Types.Abort
            else
                block_reg,block_code = env\to_reg @elseBody
                code ..= block_code
                code ..= "#{ret} =#{else_type.base_type} copy #{block_reg}\n"

            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
        else
            code ..= "#{next_case}\n"
            code ..= env\set_nil(t, ret)
            code ..= "jmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return ret,code

    Block: (env)=>
        code = ""
        for i=1,#@-1
            code ..= env\compile_stmt(@[i])
        last_reg,last_code = env\to_reg @[#@]
        code ..= last_code
        return last_reg,code

    Fail: (env)=> "0",env\compile_stmt(@).."#{env\fresh_label "unreachable"}\n"
    Return: (env)=> "0",env\compile_stmt(@).."#{env\fresh_label "unreachable"}\n"
    Skip: (env)=> "0",env\compile_stmt(@).."#{env\fresh_label "unreachable"}\n"
    Stop: (env)=> "0",env\compile_stmt(@).."#{env\fresh_label "unreachable"}\n"

    Use: (env)=>
        name = @name[0]
        mod = env\fresh_local name
        code = "#{mod} =l call $bl_use(l #{env\get_string_reg env.filename, "current_file"}, l #{env\get_string_reg name, name})\n"
        if @orElse
            success_label,fail_label = env\fresh_labels "use.success","use.fail"
            code ..= env\check_nil Types.OptionalType(get_type(@)), mod, success_label, fail_label
            code ..= env\block fail_label, -> env\compile_stmt(@orElse)
            code ..= "jmp #{success_label}\n" unless has_jump\match(code)
            code ..= "#{success_label}\n"
        return mod, code

stmt_compilers =
    Block: (env)=>
        concat([env\compile_stmt(stmt) for stmt in *@], "")
    Use: (env)=>
        assert @__imports
        name = @name[0]
        mod = env\fresh_local name
        code = "#{mod} =l call $bl_use(l #{env\get_string_reg env.filename, "current_file"}, l #{env\get_string_reg name, name})\n"
        success_label,fail_label,done_label = env\fresh_labels "use.success","use.fail","use.done"
        if @orElse
            code ..= env\check_nil Types.OptionalType(get_type(@)), mod, success_label, fail_label
            code ..= env\block fail_label, -> env\compile_stmt(@orElse)
            code ..= "jmp #{done_label}\n" unless has_jump\match(code)
            code ..= "#{success_label}\n"

        for i,mem in ipairs @__imports
            loc = env\fresh_local "#{name}.#{mem[0]}.loc"
            code ..= "#{loc} =l add #{mod}, #{8*(i-1)}\n"
            tmp = env\fresh_local "#{name}.#{mem[0]}"
            code ..= "#{tmp} =#{mem.__type.base_type} #{mem.__type.load} #{loc}\n"
            code ..= "storel #{tmp}, #{mem.__location}\n"

        if @orElse
            code ..= "jmp #{done_label}\n" unless has_jump\match(code)
            code ..= "#{done_label}\n"
        return code
    Declaration: (env)=>
        value_type = get_type @value, true
        val_reg,code = env\to_reg @value
        if @var.__register
            code ..= "#{@var.__register} =#{value_type.base_type} copy #{val_reg}\n"
        elseif @var.__location
            code ..= "#{value_type.store} #{val_reg}, #{@var.__location}\n"
        else
            node_error @var, "Undefined variable"
        return code
    Assignment: (env)=>
        node_assert #@lhs == #@rhs, @rhs, "Incorrect number of values on right hand side of assignment. Expected #{#@lhs}, but got #{#@rhs}"
        code = ""
        lhs_stores = {}

        for i,lhs in ipairs @lhs
            rhs = @rhs[i]

            lhs_type,rhs_type = get_type(lhs), get_type(rhs)
            if lhs.__tag == "Var"
                node_assert rhs_type\is_a(lhs_type), rhs, "Assignment value is type #{rhs_type}, but it's being assigned to something with type #{lhs_type}"
                node_assert lhs.__register or lhs.__location, lhs, "Undefined variable"
                if lhs.__register
                    table.insert lhs_stores, (rhs_reg)->
                        "#{lhs.__register} =#{lhs_type.base_type} copy #{rhs_reg}\n"
                elseif lhs.__location
                    table.insert lhs_stores, (rhs_reg)->
                        "#{lhs_type.store} #{rhs_reg}, #{lhs.__location}\n"
                continue
            
            node_assert lhs.__tag == "IndexedTerm", lhs, "Expected a Var or an indexed value"
            t = get_type(lhs.value)
            is_optional = t\is_a(Types.OptionalType)
            t = t.nonnil if is_optional
            if t\is_a(Types.ListType)
                index_type = get_type(lhs.index)
                list_reg,index_reg,new_code = env\to_regs lhs.value, lhs.index
                code ..= new_code
                if index_type\is_a(Types.Int) or index_type == Types.OptionalType(Types.Int)
                    table.insert lhs_stores, (rhs_reg)->
                        nonnil_label, end_label = env\fresh_labels "if.nonnil", "if.nonnil.done"
                        local code
                        code = env\check_nil get_type(lhs.value), list_reg, nonnil_label, end_label
                        code ..= env\block nonnil_label, ->
                            not_too_low,not_too_high = env\fresh_labels "not.too.low", "not.too.high"
                            len, bounds_check = env\fresh_locals "len", "bounds.check"
                            local code
                            code = ""
                            unless index_reg\match("^%d+$")
                                code ..= "#{bounds_check} =w csgel #{index_reg}, 1\n"
                                code ..= "jnz #{bounds_check}, #{not_too_low}, #{end_label}\n"
                                code ..= "#{not_too_low}\n"

                            code ..= "#{len} =l loadl #{list_reg}\n"
                            code ..= "#{bounds_check} =w cslel #{index_reg}, #{len}\n"
                            code ..= "jnz #{bounds_check}, #{not_too_high}, #{end_label}\n"

                            code ..= env\block not_too_high, ->
                                local code
                                p = env\fresh_local "p"
                                code = "#{p} =l add #{list_reg}, 8\n"
                                code ..= "#{p} =l loadl #{p}\n"
                                offset = env\fresh_local "offset"
                                code ..= "#{offset} =l sub #{index_reg}, 1\n"
                                code ..= "#{offset} =l mul #{offset}, #{t.item_type.bytes}\n"
                                code ..= "#{p} =l add #{p}, #{offset}\n"
                                if rhs_type.base_type == "d"
                                    rhs_casted = env\fresh_local "list.item.float"
                                    code ..= "#{rhs_casted} =d cast #{rhs_reg}\n"
                                    rhs_reg = rhs_casted
                                code ..= "#{t.item_type.store} #{rhs_reg}, #{p}\n"
                                return code.."jmp #{end_label}\n"

                            return code
                        code ..= "#{end_label}\n"
                        return code
                elseif index_type\is_a(Types.Range)
                    node_error lhs.index, "Assigning to list slices is not supported."
                else
                    node_error lhs.index, "Index is #{index_type} instead of Int or Range"
            elseif t\is_a(Types.TableType)
                key_type = get_type(lhs.index)
                tab_reg,key_reg,new_code = env\to_regs lhs.value, lhs.index
                code ..= new_code

                TableMethods = require 'table_methods'
                table.insert lhs_stores, (rhs_reg)->
                    _,code2 = TableMethods.methods.set {tab_reg, key_reg, rhs_reg}, env, true, t
                    return code2
            elseif t\is_a(Types.StructType)
                memb = if lhs.index.__tag == "FieldName"
                    member_name = lhs.index[0]
                    node_assert t.members[member_name], lhs.index, "Not a valid struct member of #{t}"
                    t.members[member_name]
                elseif lhs.index.__tag == "Int"
                    i = tonumber(lhs.index[0])
                    node_assert t.members, lhs.index, "#{t} only has members between 1 and #{#t.members}"
                    t.members[i]
                else
                    node_error lhs.index, "Structs can only be indexed by a field name or Int literal"
                struct_reg,new_code = env\to_regs lhs.value
                code ..= new_code

                table.insert lhs_stores, (rhs_reg)->
                    nonnil_label, end_label = env\fresh_labels "if.nonnil", "if.nonnil.done"
                    local code
                    code = env\check_nil get_type(lhs.value), struct_reg, nonnil_label, end_label
                    code ..= env\block nonnil_label, ->
                        loc = env\fresh_local "member.loc"
                        code = "#{loc} =l add #{struct_reg}, #{memb.offset}\n"
                        if memb.inline
                            code ..= "call $memcpy(l #{loc}, l #{rhs_reg}, l #{assert memb.type.memory_size})\n"
                        else
                            code ..= "#{rhs_type.store} #{rhs_reg}, #{loc}\n"
                        code ..= "jmp #{end_label}\n"
                        return code
                    code ..= "#{end_label}\n"
                    return code
            else
                node_error lhs.value, "Only Lists and Structs are mutable, not #{t}"

        assignments = ""
        for i=1,#@rhs
            rhs_reg,rhs_code = env\to_reg @rhs[i]
            code ..= rhs_code
            if #@rhs > 1
                rhs_copy = env\fresh_local "rhs.#{i}.copy"
                code ..= "#{rhs_copy} =#{get_type(@rhs[i]).base_type} copy #{rhs_reg}\n"
                assignments ..= lhs_stores[i](rhs_copy)
            else
                assignments ..= lhs_stores[i](rhs_reg)

        code ..= assignments
        return code
    AddUpdate: (env)=>
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
        store_code = @lhs.__location and "#{lhs_type.store} #{lhs_reg}, #{@lhs.__location}\n" or ""
        if nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            return code.."#{lhs_reg} =#{lhs_type.base_type} add #{lhs_reg}, #{rhs_reg}\n"..store_code
        elseif lhs_type == rhs_type and lhs_type\works_like_a(Types.String)
            return code.."#{lhs_reg} =l call $bl_string_append_string(l #{lhs_reg}, l #{rhs_reg})\n"..store_code
        elseif lhs_type\works_like_a(Types.ListType) and rhs_type\is_a(lhs_type.item_type)
            node_error @, "Cannot use += with Lists, use list.append(other) or list = list+other instead"
        elseif lhs_type == rhs_type and lhs_type\works_like_a(Types.ListType)
            node_error @, "Cannot use += with Lists, use list.append_all(other) or list = list+other instead"
        else
            node_error @, "Addition is not supported for #{lhs_type} and #{rhs_type}"
    SubUpdate: (env)=>
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
        store_code = @lhs.__location and "#{lhs_type.store} #{lhs_reg}, #{@lhs.__location}\n" or ""
        if nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            return code.."#{lhs_reg} =#{lhs_type.base_type} sub #{lhs_reg}, #{rhs_reg}\n"..store_code
        else
            node_error @, "Subtraction is not supported for #{lhs_type} and #{rhs_type}"
    MulUpdate: (env)=>
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
        store_code = @lhs.__location and "#{lhs_type.store} #{lhs_reg}, #{@lhs.__location}\n" or ""
        if nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            return code.."#{lhs_reg} =#{lhs_type.base_type} mul #{lhs_reg}, #{rhs_reg}\n"..store_code
        else
            node_error @, "Multiplication is not supported for #{lhs_type} and #{rhs_type}"
    DivUpdate: (env)=>
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
        store_code = @lhs.__location and "#{lhs_type.store} #{lhs_reg}, #{@lhs.__location}\n" or ""
        if nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            return code.."#{lhs_reg} =#{lhs_type.base_type} div #{lhs_reg}, #{rhs_reg}\n"..store_code
        else
            node_error @, "Division is not supported for #{lhs_type} and #{rhs_type}"
    OrUpdate: (env)=>
        t_lhs, t_rhs = get_type(@lhs), get_type(@rhs)
        true_label,false_label = env\fresh_labels "or.lhs.true", "or.lhs.false"
        lhs_reg,code = env\to_reg @lhs
        code ..= env\check_truthiness t_lhs, lhs_reg, true_label, false_label
        code ..= env\block false_label, ->
            rhs_reg,code = env\to_reg @rhs
            code ..= "#{lhs_reg} =#{t_lhs.base_type} copy #{rhs_reg}\n"
            code ..= "#{t_lhs.store} #{lhs_reg}, #{@lhs.__location}\n" if @lhs.__location
            code ..= "jmp #{true_label}\n"
            return code
        code ..= "#{true_label}\n"
        return code
    AndUpdate: (env)=>
        t_lhs, t_rhs = get_type(@lhs), get_type(@rhs)
        true_label,false_label = env\fresh_labels "and.lhs.true", "and.lhs.false"
        lhs_reg,code = env\to_reg @lhs
        code ..= env\check_truthiness t_lhs, lhs_reg, true_label, false_label
        code ..= env\block true_label, ->
            rhs_reg,code = env\to_reg @rhs
            code ..= "#{lhs_reg} =#{t_lhs.base_type} copy #{rhs_reg}\n"
            code ..= "#{t_lhs.store} #{lhs_reg}, #{@lhs.__location}\n" if @lhs.__location
            code ..= "jmp #{false_label}\n"
            return code
        code ..= "#{false_label}\n"
        return code
    XorUpdate: (env)=>
        t_lhs, t_rhs = get_type(@lhs), get_type(@rhs)
        lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
        store_code = @lhs.__location and "#{t_lhs.store} #{lhs_reg}, #{@lhs.__location}\n" or ""
        lhs_true,lhs_false,use_rhs,use_false,xor_done = env\fresh_labels "xor.lhs.true","xor.lhs.false","xor.use.rhs","xor.false","xor.done"

        code ..= env\check_truthiness t_lhs, lhs_reg, lhs_true, lhs_false
        code ..= env\block lhs_true, ->
            env\check_truthiness t_rhs, rhs_reg, use_false, xor_done
        code ..= env\block lhs_false, ->
            env\check_truthiness t_rhs, rhs_reg, use_rhs, xor_done
        code ..= env\block use_rhs, ->
            "#{lhs_reg} =#{t_lhs.base_type} copy #{rhs_reg}\n"..store_code
        code ..= env\block use_false, ->
            if t_lhs\is_a(Types.Optional)
                code ..= env\set_nil t_lhs, lhs_reg
            else
                code ..= "#{lhs_reg} =l copy 0"..store_code
            code ..= "jmp #{xor_true}\n"

        code ..= "#{xor_done}\n"
        return code
    ButWithUpdate: (env)=>
        t = get_type @base
        if t\is_a(Types.StructType)
            base_reg,code = env\to_reg @base
            ret = env\fresh_local "#{t.name\lower!}.butwith"
            code ..= "#{ret} =l call $gc_alloc(l #{t.memory_size})\n"
            code ..= "call $memcpy(l #{ret}, l #{base_reg}, l #{t.memory_size})\n"
            p = env\fresh_local "#{t.name\lower!}.butwith.member.loc"
            for override in *@
                memb = if override.index
                    t.members[tonumber(override.index[0])]
                elseif override.field
                    t.members[override.field[0]]
                else
                    node_error override, "I don't know what this is"

                node_assert memb, override, "Not a valid member of #{t}"
                node_assert get_type(override.value)\is_a(memb.type), override.value, "Not a #{memb}"
                val_reg,val_code = env\to_reg override.value
                code ..= val_code
                code ..= "#{p} =l add #{ret}, #{memb.offset}\n"
                code ..= "#{memb.type.store} #{val_reg}, #{p}\n"

            code ..= "#{t.store} #{base_reg}, #{@base.__location}\n" if @base.__location
            return code
        else
            node_error @, "| operator is only supported for Struct types"

    MethodCallUpdate: (env)=>
        dest = @[1]
        node_assert dest and dest.__tag == "Var", dest, "Method call updates expect a variable"
        update_sig = "(#{concat [tostring(get_type(a)) for a in *@], ","})=>#{get_type(dest)}"
        fn_type = get_type @fn
        fn_reg,code = env\to_reg @fn

        if fn_type
            node_assert fn_type\is_a(Types.FnType), @fn, "This is not a function, it's a #{fn_type or "???"}"
            node_assert "#{fn_type}" == update_sig, @, "For this to work, #{@fn[0]} should be #{update_sig}, not #{fn_type}"

        args = {}
        for arg in *@
            arg_reg, arg_code = env\to_reg arg
            code ..= arg_code
            table.insert args, "#{get_type(arg).base_type} #{arg_reg}"

        ret_type = fn_type and fn_type.return_type or get_type(dest)

        if dest.__register
            code ..= "#{dest.__register} =#{ret_type.base_type} call #{fn_reg}(#{concat args, ", "})\n"
        elseif dest.__location
            ret = env\fresh_local "return"
            code ..= "#{ret} =#{ret_type.base_type} call #{fn_reg}(#{concat args, ", "})\n"
            code ..= "#{ret_type.store} #{ret}, #{dest.__location}\n"
        return code

    FnDecl: (env)=> ""
    ConvertDecl: (env)=> ""
    Extern: (env)=> ""
    Macro: (env)=> ""
    Pass: (env)=> ""
    Fail: (env)=>
        if @message
            t = get_type(@message)
            node_assert t\is_a(Types.OptionalType(Types.String)), @message,
                "Failure messages must be a String or nil, not #{get_type @message}"
            msg,code = env\to_reg @message
            fail_label,empty_label = env\fresh_labels "failure", "empty.message"
            code ..= "jnz #{msg}, #{fail_label}, #{empty_label}\n"
            code ..= "#{empty_label}\n"
            code ..= "#{msg} =l copy #{env\get_string_reg("Unexpected failure!", "default.failure")}\n"
            code ..= "jmp #{fail_label}\n#{fail_label}\n"
            code ..= "call $dprintf(l 2, l #{env\get_string_reg(context_err(@, "%s", 2).."\n", "failure.message")}, l #{msg})\n"
            code ..= "call $_exit(l 1)\n"
            return code
        else
            code = "call $dprintf(l 2, l #{env\get_string_reg(context_err(@, "A failure occurred!", 2).."\n", "failure.message")})\n"
            code ..= "call $_exit(l 1)\n"
            return code
    TypeDeclaration: (env)=> ""
    StructDeclaration: (env)=> ""
    EnumDeclaration: (env)=> ""
    UnionDeclaration: (env)=> ""
    UnitDeclaration: (env)=> ""
    Export: (env)=> ""
    FnCall: (env)=>
        ret_type = get_type(@)
        if ret_type
            node_assert ret_type == Types.Abort or ret_type == Types.NilType, @, "Return value (#{ret_type}) is not being used"
        _, code = env\to_reg @, true
        code = code\gsub("[^\n]- (call [^\n]*\n)$", "%1")
        return code
    Return: (env)=>
        if @value
            reg, code = env\to_reg @value
            if get_type(@value)\is_a(Types.Abort)
                return "#{code}ret\n"
            return "#{code}ret #{reg}\n"
        else
            return "ret\n"
    Stop: (env)=>
        node_assert @jump_label, @, "'stop' statement should only be used inside a loop"
        return "jmp #{@jump_label}\n"
    Skip: (env)=>
        node_assert @jump_label, @, "'skip' statement should only be used inside a loop"
        return "jmp #{@jump_label}\n"
    Do: (env)=>
        _,code = env\to_reg @
        return code
    If: (env)=>
        _,code = env\to_reg @
        return code
    When: (env)=>
        _,code = env\to_reg @
        return code
    Repeat: (env)=> repeat_loop(@, env)
    While: (env)=> while_loop(@, env)
    For: (env)=>
        iter_reg,code = env\to_regs @iterable
        key_reg, value_reg = if @index and @val
            @index.__register, @val.__register
        elseif @val and @iterable.__type\works_like_a(Types.TableType)
            @val.__register, nil
        elseif @val
            nil, @val.__register
        else
            nil, nil

        code ..= env\for_loop {
            type: @iterable.__type, :iter_reg, :key_reg, :value_reg, scope:{@body, @between},
            make_body: -> if @body then env\compile_stmt @body else ""
            make_between: -> if @between then env\compile_stmt @between else ""
        }
        return code
        
compile_prog = (ast, filename)->
    env = Environment(filename)
    return env\compile_program(ast, filename)

return {:compile_prog}
