Types = require 'typecheck'
bp = require 'bp'
import get_type, parse_type from Types
import log, viz, node_assert, node_error, get_node_pos, print_err, each_tag from require 'util'
import Measure, register_unit_alias from require 'units'
concat = table.concat

has_jump = bp.compile('^_("jmp"/"jnz"/"ret")\\b ..$ $$')

local stmt_compilers, expr_compilers

get_function_reg = (scope, name, arg_types, return_type=nil)->
    return nil unless scope
    switch scope.__tag
        when "Block"
            for i=#scope,1,-1
                stmt = scope[i]
                if stmt.__tag == "FnDecl" and stmt.name[0] == name
                    t = get_type(stmt)
                    if t\matches(arg_types, return_type)
                        return node_assert(stmt.__register, stmt, "Function without a name"), false, get_type(stmt)
                elseif stmt.__tag == "Declaration" and stmt.var[0] == name
                    t = get_type stmt.value
                    if t\is_a(Types.FnType) and t\matches(arg_types, return_type)
                        return stmt.var.__register, false, t
                elseif stmt.__tag == "Use"
                    mod_type = get_type(stmt)
                    mem = mod_type.nonnil.members[name]
                    if mem and mem.type\is_a(Types.FnType) and mem.type\matches(arg_types, return_type)
                        t = stmt.orElse and mem.type or OptionalType(mem.type)
                        return mem.__location, true, t
                elseif stmt.__tag == "StructDeclaration"
                    for method in *(stmt[1].methods or {})
                        t = get_type(method)
                        if t\matches(arg_types, return_type)
                            return node_assert(stmt.__register, stmt, "Function without a name"), false, get_type(stmt)

        when "FnDecl","Lambda"
            for a in *scope.args
                if a.arg[0] == name
                    t = parse_type(a.type)
                    if t\is_a(Types.FnType) and t\matches(arg_types, return_type)
                        return a.__register, false, t
        when "For"
            iter_type = get_type(scope.iterable)
            if scope.val and scope.val[0] == name
                if iter_type\is_a(Types.ListType) and iter_type.item_type\is_a(Types.FnType)
                    return scope.val.__register, false, iter_type.item_type
                elseif iter_type\is_a(Types.TableType) and iter_type.value_type\is_a(Types.FnType)
                    return scope.val.__register, false, iter_type.value_type
            if scope.index and scope.index[0] == name
                if iter_type\is_a(Types.TableType) and iter_type.key_type\is_a(Types.FnType)
                    return scope.index.__register, false, iter_type.key_type

    if scope.__parent and (scope.__parent.__tag == "For" or scope.__parent.__tag == "While" or scope.__parent.__tag == "Repeat")
        loop = scope.__parent
        if scope == loop.between
            r,c,t = get_function_reg(loop.body, name, arg_types, return_type)
            return r,c,t if r
    
    return get_function_reg(scope.__parent, name, arg_types, return_type)

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

overload_infix = (env, overload_name, regname="result")=>
    t = get_type @
    lhs_type, rhs_type = get_type(@lhs), get_type(@rhs)
    fn_reg, needs_loading, t2 = get_function_reg @__parent, overload_name, {lhs_type,rhs_type}
    node_assert fn_reg, @, "#{overload_name} is not supported for #{lhs_type} and #{rhs_type}"
    lhs_reg,rhs_reg,operand_code = env\to_regs @lhs, @rhs
    code = ""
    code ..= "#{fn_reg} =l loadl #{fn_reg}\n" if needs_loading
    code ..= operand_code
    result = env\fresh_local regname
    code ..= "#{result} =#{t.base_type} call #{fn_reg}(#{lhs_type.base_type} #{lhs_reg}, #{rhs_type.base_type} #{rhs_reg})\n"
    return result, code

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

check_truthiness = (t, env, reg, truthy_label, falsey_label)->
    if t\is_a(Types.Bool)
        return "jnz #{reg}, #{truthy_label}, #{falsey_label}\n"
    elseif t\is_a(Types.NilType)
        return "jmp #{falsey_label}\n"
    elseif t.base_type == "d"
        tmp = env\fresh_local "is.nonnil"
        return "#{tmp} =l cod #{reg}, d_0.0 # Test for NaN\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
    elseif t.base_type == "s"
        tmp = env\fresh_local "is.nonnil"
        return "#{tmp} =l cos #{reg}, d_0.0 # Test for NaN\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
    elseif t\is_a(Types.OptionalType)
        if t.nonnil\is_a(Types.Bool)
            tmp = env\fresh_local "is.true"
            return "#{tmp} =l ceq#{t.base_type} #{reg}, 1\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
        elseif t.nonnil.base_type == "d"
            tmp = env\fresh_local "is.nonnil"
            return "#{tmp} =l cod #{reg}, d_0.0 # Test for NaN\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
        elseif t.nonnil.base_type == "s"
            tmp = env\fresh_local "is.nonnil"
            return "#{tmp} =l cos #{reg}, s_0.0 # Test for NaN\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
        elseif t.nonnil.nil_value == 0
            return "jnz #{reg}, #{truthy_label}, #{falsey_label}\n"
        else
            tmp = env\fresh_local "is.nonnil"
            return "#{tmp} =l cne#{t.base_type} #{reg}, #{t.nil_value}\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
    else
        return "jmp #{truthy_label}\n"

check_nil = (t, env, reg, nonnil_label, nil_label)->
    if t == Types.NilType
        return "jmp #{nil_label}\n"
    elseif not t\is_a(Types.OptionalType)
        return "jmp #{nonnil_label}\n"
    elseif t.nil_value == 0
        return "jnz #{reg}, #{nonnil_label}, #{nil_label}\n"
    elseif t.nonnil.base_type == "d"
        is_not_nan = env\fresh_local "is.not.NaN"
        return "#{is_not_nan} =w cod #{reg}, d_0.0 # Test for NaN\njnz #{is_not_nan}, #{nonnil_label}, #{nil_label}\n"
    elseif t.nonnil.base_type == "s"
        is_not_nan = env\fresh_local "is.not.NaN"
        return "#{is_not_nan} =w cos #{reg}, s_0.0 # Test for NaN\njnz #{is_not_nan}, #{nonnil_label}, #{nil_label}\n"
    else
        tmp = env\fresh_local "is.nonnil"
        return "#{tmp} =w cne#{t.base_type} #{reg}, #{t.nil_value}\njnz #{tmp}, #{nonnil_label}, #{nil_label}\n"

set_nil = (t, env, reg)->
    if t.base_type == "s" or t.base_type == "d"
        return "#{reg} =#{t.base_type} cast #{t.nil_value}\n"
    else
        return "#{reg} =#{t.base_type} copy #{t.nil_value}\n"

convert_nil = (t, env, src_reg, dest_reg)->
    assert t and env and src_reg and dest_reg, "XXX"
    if t.base_type == "s" or t.base_type == "d"
        bits = env\fresh_local "bits"
        code = "#{bits} =#{if t.base_type == "s" then "w" else "l"} xor #{src_reg}, #{t.nil_value}\n"
        code ..= "#{dest_reg} =#{t.base_type} cast #{bits}\n"
        return code
    elseif t.nil_value != 0
        return "#{dest_reg} =#{t.base_type} xor #{src_reg}, #{t.nil_value}\n"
    else
        return "#{dest_reg} =#{t.base_type} copy #{src_reg}\n"

hash_prep = (value_t, value_reg, dest_reg)->
    assert value_t and value_reg and dest_reg, "XXX"
    if value_t.base_type == "s" or value_t.base_type == "d"
        code = "#{dest_reg} =l cast #{value_reg}\n"
        return code.."#{dest_reg} =l xor #{dest_reg}, #{value_t.nil_value}\n"
    else
        code = if value_t.bytes == 8
            "#{dest_reg} =l copy #{value_reg}\n"
        else
            "#{dest_reg} =l extu#{value_t.abi_type} #{value_reg}\n"

        if value_t.nil_value != 0
            code ..= "#{dest_reg} =l xor #{dest_reg}, #{value_t.nil_value}\n"
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
            chunks = str\gsub('[^ !#-[^-~%]]', (c)->"\",b #{c\byte(1)},b\"")\gsub("\n", "\\n")
            @string_code ..= "data #{name} = {b\"#{chunks}\",b 0}\n"
        return @strings[str]

    declare_function: (fndec)=>
        args = ["#{parse_type(arg.type).base_type} #{arg.arg.__register}" for arg in *fndec.args]
        fn_scope = @inner_scope {"%#{arg.arg[0]}",true for arg in *fndec.args}
        body_code = if fndec.body.__tag == "Block"
            fn_scope\compile_stmt fndec.body
        else
            ret_reg, tmp = fn_scope\to_reg fndec.body
            "#{tmp}ret #{ret_reg}\n"
        body_code = body_code\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))
        fn_type = get_type fndec
        ret_type = fn_type.return_type
        node_assert fndec.__register, fndec, "Function has no name"
        fn_name = fndec.__register
        @fn_code ..= "\nfunction #{ret_type\is_a(Types.Void) and "" or ret_type.base_type.." "}"
        @fn_code ..= "#{fn_name}(#{concat args, ", "}) {\n@start\n#{body_code}"
        if ret_type\is_a(Types.Void) and not has_jump\match(@fn_code)
            @fn_code ..= "  ret\n"
        elseif not has_jump\match(@fn_code)
            @fn_code ..= "  ret 0\n"
        @fn_code ..= "}\n"

    get_tostring_fn: (t, scope)=>
        if t != Types.String
            fn,needs_loading = get_function_reg scope, "tostring", {t}, Types.String
            return fn,needs_loading if fn

        -- HACK: these primitive values' functions only take 1 arg, but it
        -- should be safe to pass them an extra callstack argument, which
        -- they'll just ignore.
        if t\is_a(Types.Int)
            return "$bl_tostring_int",false
        elseif t\is_a(Types.Int32)
            return "$bl_tostring_int32",false
        elseif t\is_a(Types.Int16)
            return "$bl_tostring_int16",false
        elseif t\is_a(Types.Int8)
            return "$bl_tostring_int8",false
        elseif t\is_a(Types.Percent)
            return "$bl_tostring_percent",false
        elseif t\is_a(Types.Num)
            return "$bl_tostring_float",false
        elseif t\is_a(Types.Num32)
            return "$bl_tostring_float32",false
        elseif t\is_a(Types.Bool)
            return "$bl_tostring_bool",false
        elseif t\is_a(Types.String)
            return "$bl_string",false
        elseif t\is_a(Types.Range)
            return "$bl_tostring_range",false

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
        if t\is_a(Types.NilType)
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("nil", "nil")})\n"
        elseif t\is_a(Types.Void)
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("Void", "void")})\n"
        elseif t == Types.Value or t == Types.Value32 or t == Types.Value16 or t == Types.Value8
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("<#{t.name}>", t.name)})\n"
        elseif t\is_a(Types.EnumType)
            init_fields,fields_exist = @fresh_labels "make_fields", "fields_exist"
            tmp = @fresh_local "fieldname"
            code ..= "#{tmp} =l loadl $#{t\id_str!}.fields\n"
            code ..= "jnz #{tmp}, #{fields_exist}, #{init_fields}\n"
            code ..= @block init_fields, ->
                code = ""
                for i,field in ipairs(t.fields)
                    -- str = @fresh_local "str"
                    -- code ..= "#{str} =l call $bl_string(l #{@get_string_reg "#{t.name}.#{field}", "#{t.name}.#{field}"})\n"
                    code ..= "#{tmp} =l add $#{t\id_str!}.fields, #{8*(i-1)}\n"
                    code ..= "storel #{@get_string_reg "#{t.name}.#{field}", "#{t.name}.#{field}"}, #{tmp}\n"
                code ..= "jmp #{fields_exist}\n"
                return code

            code ..= "#{fields_exist}\n"
            code ..= "#{reg} =l sub #{reg}, 1\n"
            code ..= "#{reg} =l mul #{reg}, 8\n"
            code ..= "#{tmp} =l add $#{t\id_str!}.fields, #{reg}\n"
            code ..= "#{dest} =l loadl #{tmp}\n"
        elseif t\is_a(Types.ListType)
            len = @fresh_local "len"
            code ..= "#{len} =l loadl #{reg}\n"

            buf = @fresh_local "buf"
            code ..= "#{buf} =l copy #{@get_string_reg "[", "lsq"}\n"

            item_loc = @fresh_local "item.loc"
            code ..= "#{item_loc} =l add #{reg}, 8\n"
            code ..= "#{item_loc} =l loadl #{item_loc}\n"

            body_label,after_comma,end_label = @fresh_labels "list.loop.body", "list.loop.item", "list.loop.end"

            code ..= "jnz #{len}, #{after_comma}, #{end_label}\n"

            code ..= @block body_label, ->
                code = "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg ", ", "comma.space"})\n"
                code ..= "jmp #{after_comma}\n"
                return code

            code ..= @block after_comma, ->
                item = @fresh_local "list.item"
                code = "#{item} =#{t.item_type.base_type} load#{t.item_type.base_type} #{item_loc}\n"
                item_str = @fresh_local "item.string"
                fn,needs_loading = @get_tostring_fn t.item_type, scope
                code ..= "#{fn} =l loadl #{fn}\n" if needs_loading
                code ..= "#{item_str} =l call #{fn}(#{t.item_type.base_type} #{item}, l #{callstack})\n"
                code ..= "#{buf} =l call $CORD_cat(l #{buf}, l #{item_str})\n"
                code ..= "#{len} =l sub #{len}, 1\n"
                code ..= "#{item_loc} =l add #{item_loc}, #{t.item_type.bytes}\n"
                code ..= "jnz #{len}, #{body_label}, #{end_label}\n"
                return code

            code ..= @block end_label, ->
                code = "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg "]", "rsq"})\n"
                code ..= "#{buf} =l call $CORD_to_const_char_star(l #{buf})\n"
                code ..= "#{dest} =l call $bl_string(l #{buf})\n"
                return code

        elseif t\is_a(Types.TableType)
            len = @fresh_local "len"
            code ..= "#{len} =l call $hashmap_length(l #{reg})\n"

            buf = @fresh_local "buf"
            code ..= "#{buf} =l copy #{@get_string_reg "{", "lbracket"}\n"

            key = @fresh_local "key.raw"
            code ..= "#{key} =l copy 0\n"

            loop_label,body_label,comma_label,end_label = @fresh_labels "table.loop", "table.loop.body", "table.loop.comma", "table.loop.end"

            code ..= "#{key} =l call $hashmap_next(l #{reg}, l #{key})\n"
            code ..= "jnz #{key}, #{body_label}, #{end_label}\n"

            code ..= @block loop_label, ->
                code = "#{key} =l call $hashmap_next(l #{reg}, l #{key})\n"
                code ..= "jnz #{key}, #{comma_label}, #{end_label}\n"
                return code

            code ..= @block comma_label, ->
                code = "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg ", ", "comma"})\n"
                return code.."jmp #{body_label}\n"

            code ..= @block body_label, ->
                key_reg = @fresh_local "key"
                code = hash_prep t.key_type, key, key_reg
                key_str = @fresh_local "key.string"
                fn,needs_loading = @get_tostring_fn t.key_type, scope
                code ..= "#{fn} =l loadl #{fn}\n" if needs_loading
                code ..= "#{key_str} =l call #{fn}(#{t.key_type.base_type} #{key_reg}, l #{callstack})\n"
                code ..= "#{buf} =l call $CORD_cat(l #{buf}, l #{key_str})\n"
                code ..= "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg "=", "equals"})\n"

                value_raw = @fresh_local "value.raw"
                code ..= "#{value_raw} =l call $hashmap_get(l #{reg}, l #{key})\n"
                value_reg = @fresh_local "value"
                code ..= convert_nil t.value_type, @, value_raw, value_reg
                
                value_str = @fresh_local "value.string"
                fn,needs_loading = @get_tostring_fn t.value_type, scope
                code ..= "#{fn} =l loadl #{fn}\n" if needs_loading
                code ..= "#{value_str} =l call #{fn}(#{t.value_type.base_type} #{value_reg}, l #{callstack})\n"
                code ..= "#{buf} =l call $CORD_cat(l #{buf}, l #{value_str})\n"

                code ..= "jmp #{loop_label}\n"
                return code

            code ..= @block end_label, ->
                code = "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg "}", "rbracket"})\n"
                code ..= "#{buf} =l call $CORD_to_const_char_star(l #{buf})\n"
                code ..= "#{dest} =l call $bl_string(l #{buf})\n"
                return code

        elseif t\is_a(Types.StructType)
            content = @fresh_local "struct.content"

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
                code = "#{cycle_parent} =l add #{walker}, 8\n"
                code ..= "#{cycle_parent} =l loadl #{cycle_parent}\n"
                code ..= "#{walker} =l loadl #{walker}\n"
                wasfound = @fresh_local "cycle.wasfound"
                code ..= "#{wasfound} =l ceql #{cycle_parent}, #{reg}\n"
                code ..= "jnz #{wasfound}, #{cycle_found}, #{cycle_next}\n"
                return code

            code ..= @block cycle_found, ->
                code = "#{content} =l copy #{@get_string_reg "...", "ellipsis"}\n"
                code ..= "jmp #{conclusion}\n"
                return code

            code ..= @block cycle_notfound, ->
                new_callstack = @fresh_local "new.callstack"
                code = "#{new_callstack} =l alloc8 #{2*8}\n"
                code ..= "storel #{callstack}, #{new_callstack}\n"
                p = @fresh_local "p"
                code ..= "#{p} =l add #{new_callstack}, 8\n"
                code ..= "storel #{reg}, #{p}\n"
                chunks = @fresh_local "chunks"
                code ..= "#{chunks} =l alloc8 #{8*#t.sorted_members}\n"
                for i,mem in ipairs t.sorted_members
                    member_loc = @fresh_local "#{t\id_str!\lower!}.#{mem.name}.loc"
                    code ..= "#{member_loc} =l add #{reg}, #{8*(i-1)}\n"
                    member_reg = @fresh_local "#{t\id_str!\lower!}.#{mem.name}"
                    code ..= "#{member_reg} =#{mem.type.base_type} load#{mem.type.base_type} #{member_loc}\n"

                    member_str = @fresh_local "#{t\id_str!\lower!}.#{mem.name}.string"
                    fn,needs_loading = @get_tostring_fn mem.type, scope
                    code ..= "#{fn} =l loadl #{fn}\n" if needs_loading
                    code ..= "#{member_str} =l call #{fn}(#{mem.type.base_type} #{member_reg}, l #{new_callstack})\n"

                    if mem.name
                        code ..= "#{member_str} =l call $bl_string_append_string(l #{@get_string_reg("#{mem.name}=")}, l #{member_str})\n"
                    chunk_loc = @fresh_local "string.chunk.loc"
                    code ..= "#{chunk_loc} =l add #{chunks}, #{8*(i-1)}\n"
                    code ..= "storel #{member_str}, #{chunk_loc}\n"
                code ..= "#{content} =l call $bl_string_join(l #{#t.sorted_members}, l #{chunks}, l #{@get_string_reg(", ", "comma.space")})\n"
                code ..= "jmp #{conclusion}\n"
                return code

            code ..= @block conclusion, ->
                final_chunks = @fresh_local "surrounding.chunks"
                code = "#{final_chunks} =l alloc8 #{8*3}\n"
                chunk_loc = @fresh_local "chunk.loc"
                code ..= "#{chunk_loc} =l add #{final_chunks}, #{8*0}\n"
                if t.name\match "^Tuple%.[0-9]+$"
                    code ..= "storel #{@get_string_reg("{", "curly")}, #{chunk_loc}\n"
                else
                    code ..= "storel #{@get_string_reg("#{t.name}{", "#{t\id_str!}.name")}, #{chunk_loc}\n"
                code ..= "#{chunk_loc} =l add #{final_chunks}, #{8*1}\n"
                code ..= "storel #{content}, #{chunk_loc}\n"
                code ..= "#{chunk_loc} =l add #{final_chunks}, #{8*2}\n"
                code ..= "storel #{@get_string_reg("}","closecurly")}, #{chunk_loc}\n"
                code ..= "#{dest} =l call $bl_string_join(l 3, l #{final_chunks}, l 0)\n"
                return code

        elseif t\is_a(Types.UnionType)
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
                    code = "#{val} =#{info.type.base_type} load#{info.type.abi_type} #{val_loc}\n"
                    code ..= "#{tmp} =l call #{@get_tostring_fn info.type, scope}(#{info.type.base_type} #{val}, l #{callstack})\n"
                    code ..= "#{dest} =l call $CORD_cat(l #{dest}, l #{tmp})\n"
                    code ..= "jmp #{done_label}\n"
                    return code
            code ..= "#{done_label}\n"
            code ..= "#{dest} =l call $CORD_to_const_char_star(l #{dest})\n"
            code ..= "#{dest} =l call $bl_string(l #{dest})\n"

        elseif t\is_a(Types.FnType)
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("#{t}")})\n"
        elseif t\is_a(Types.OptionalType)
            nil_label,nonnil_label,end_label = @fresh_labels "optional.nil", "optional.nonnil", "optional.end"
            code ..= check_nil t, @, reg, nonnil_label, nil_label
            code ..= @block nil_label, ->
                code = "#{dest} =l call $bl_string(l #{@get_string_reg("nil", "nil")})\n"
                code ..= "jmp #{end_label}\n"
                return code
            code ..= @block nonnil_label, ->
                fn,needs_loading = @get_tostring_fn t.nonnil, scope
                code = ""
                code ..= "#{fn} =l loadl #{fn}\n" if needs_loading
                code ..= "#{dest} =l call #{fn}(#{t.nonnil.base_type} #{reg}, l #{callstack})\n"
                code ..= "jmp #{end_label}\n"
                return code
            code ..= "#{end_label}\n"
        elseif t\is_a(Types.MeasureType)
            code ..= "#{dest} =l call $bl_tostring_float(d #{reg})\n"
            code ..= "#{dest} =l call $bl_string_append_string(l #{dest}, l #{@get_string_reg("<"..t.units..">", "units")})\n"
        elseif t\is_a(Types.Pointer)
            code ..= "#{dest} =l call $bl_tostring_hex(l #{reg})\n"
        else
            error "Unsupported tostring type: #{t}"

        code ..= "ret #{dest}\n"
        code ..= "}\n"
        code = code\gsub("[^\n]+", =>((@\match("^[@}]") or @\match("^function")) and @ or "  "..@))
        @fn_code ..= code

        return fn_name,false

    to_reg: (node, ...)=>
        node_assert expr_compilers[node.__tag], node, "Expression compiler not implemented for #{node.__tag}"
        return expr_compilers[node.__tag](node, @, ...)

    to_regs: (...)=>
        nodes = {...}
        regs = {}
        codes = {}
        for node in *nodes
            node_assert expr_compilers[node.__tag], node, "Expression compiler not implemented for #{node.__tag}"
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
            return ast unless type(ast) == 'table'
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

            return {k,(if type(k) == 'string' and k\match("^__") then v else apply_macros(v)) for k,v in pairs ast}
                
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
        declared_structs = {}
        for s in coroutine.wrap(-> each_tag(ast, "StructType", "Struct"))
            t = if s.__tag == "StructType" then parse_type(s)
            else get_type(s)

            if declared_structs[t.name]
                node_assert declared_structs[t.name] == t, s, "Struct declaration shadows"
                continue
            declared_structs[t.name] = t
            @type_code ..= "type :#{t.name} = {#{concat [m.type.base_type for m in *t.sorted_members], ","}}\n"

        -- Declared units:
        for u in coroutine.wrap(-> each_tag(ast, "UnitDeclaration"))
            n = tonumber((u.measure.amount[0]\gsub("_","")))
            m = Measure(n, u.measure.units[0]\gsub("[<>]",""))
            register_unit_alias(u.name[0], m)

        -- Enum field names
        for e in coroutine.wrap(-> each_tag(ast, "EnumDeclaration"))
            t = get_type(e)
            assert t\is_a(Types.EnumType), "#{t}"
            fieldnames = "$#{t\id_str!}.fields"
            @type_code ..= "data #{fieldnames} = {#{("l 0,")\rep(#t.fields)}}\n"

        -- Union field names
        for u in coroutine.wrap(-> each_tag(ast, "UnionType"))
            t = parse_type(u)
            assert t\is_a(Types.UnionType), "#{t}"
            fieldnames = "$#{t\id_str!}.member_names"
            @type_code ..= "data #{fieldnames} = {#{concat ["l 0" for _ in pairs t.members], ", "}}\n"

        @used_names["args"] = true
        for v in coroutine.wrap(-> each_tag(ast, "Var"))
            if v[0] == "args"
                v.__location = "$args"

        is_file_scope = (scope)->
            while scope
                return true if scope == ast
                switch scope.__tag
                    when "FnDecl","Lambda","Macro"
                        return false
                scope = scope.__parent
            error("Unexpectedly reached a node not parented to top-level AST")

        file_scope_vars = {}
        -- Set up variable registers:
        hook_up_refs = (var, scope, var_type)->
            if not var.__register and not var.__location
                if var.__parent and var.__parent.__tag == "Declaration" and is_file_scope var
                    var.__location = @fresh_global var[0]
                    file_scope_vars[var] = true
                else
                    var.__register = @fresh_local var[0]

            switch scope.__tag
                when "Var"
                    if scope[0] == var[0]
                        -- node_assert not scope.__register and not scope.__location, var, "Variable shadows earlier declaration #{scope.__decl}"
                        scope.__register = var.__register
                        scope.__location = var.__location
                        scope.__decl = var
                        scope.__type = var_type
                when "Declaration"
                    hook_up_refs var, scope.value, var_type
                when "FnDecl","Lambda"
                    if (var.__register and var.__register\match("^%$")) or var.__location
                        hook_up_refs var, scope.body, var_type
                when "FnCall","MethodCallUpdate"
                    arg_types = {}
                    for arg in *scope
                        hook_up_refs var, arg, var_type
                        if arg.__tag == "KeywordArg"
                            arg_types[arg.name[0]] = get_type(arg.value)
                        else
                            table.insert arg_types, get_type(arg)
                    if var_type and var_type\is_a(Types.FnType) and var_type\matches(arg_types)
                        hook_up_refs var, scope.fn, var_type
                else
                    for k,node in pairs scope
                        if type(node) == 'table' and not (type(k) == 'string' and k\match("^__"))
                            hook_up_refs var, node, var_type

        for glob in coroutine.wrap(-> each_tag(ast, "Global"))
            glob.__register = glob[0]

        for s in coroutine.wrap(-> each_tag(ast, "StructDeclaration", "UnionDeclaration"))
            scope = if s.__parent.__tag == "Block"
                i = 1
                while s.__parent[i] != s
                    i += 1
                {table.unpack(s.__parent, i+1)}
            else s.__parent
            t = s[1] or s.type
            var = {__tag:"Var", [0]: t.name[0], __location: @get_string_reg(t.name[0], "typestring"), __parent:s.__parent}
            hook_up_refs var, scope, parse_type(t)

            for method in *(t.methods or {})
                method.__register = @fresh_global(method.name[0])
                method.__decl = method
                method.name.__register = method.__register
                method.name.__decl = method
                m_t = get_type(method)
                hook_up_refs method.name, s.__parent, m_t

        -- Compile modules:
        for use in coroutine.wrap(-> each_tag(ast, "Use"))
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

        for vardec in coroutine.wrap(-> each_tag(ast, "Declaration"))
            scope = if vardec.__parent.__tag == "Block"
                i = 1
                while vardec.__parent[i] != vardec
                    i += 1
                {table.unpack(vardec.__parent, i+1)}
            elseif (vardec.__parent.__tag == "Clause" or vardec.__parent.__tag == "While") and vardec == vardec.__parent.condition
                vardec.__parent.body
            else vardec.__parent

            t = vardec.type and parse_type(vardec.type) or get_type(vardec.value)
            if (vardec.__parent.__tag == "Clause" or vardec.__parent.__tag == "While") and vardec == vardec.__parent.condition and t\is_a(Types.OptionalType)
                t = t.nonnil
            hook_up_refs vardec.var, scope, t

            block = vardec.__parent
            loop = block and block.__parent
            while loop and not loop.__tag
                loop = loop.__parent
            if loop and (loop.__tag == "For" or loop.__tag == "While" or loop.__tag == "Repeat")
                if block == loop.body and loop.between
                    hook_up_refs vardec.var, loop.between, t

        -- Set up function names (global):
        for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl", "Lambda"))
            fndec.__register or= @fresh_global(fndec.name and fndec.name[0] or "lambda")
            fndec.__decl = fndec
            if fndec.name
                fndec.name.__register = fndec.__register
                fndec.name.__decl = fndec
                t = get_type(fndec)
                hook_up_refs fndec.name, fndec.__parent, t
                    
        for fn in coroutine.wrap(-> each_tag(ast, "FnDecl", "Lambda"))
            for a in *fn.args
                a.arg.__register,a.arg.__location = nil,nil
                hook_up_refs a.arg, fn.body, parse_type(a.type)

        for for_block in coroutine.wrap(-> each_tag(ast, "For"))
            if for_block.val
                for_block.val.__register,for_block.val.__location = nil,nil
                t = get_type(for_block.val)
                hook_up_refs for_block.val, for_block.body, t
                hook_up_refs for_block.val, for_block.between, t if for_block.between
                hook_up_refs for_block.val, for_block.filter, t if for_block.filter
            if for_block.index
                for_block.index.__register,for_block.index.__location = nil,nil
                t = get_type(for_block.index)
                hook_up_refs for_block.index, for_block.body, t
                hook_up_refs for_block.index, for_block.between, t if for_block.between
                hook_up_refs for_block.index, for_block.filter, t if for_block.filter

        -- Look up which function to use for each callsite:
        for call in coroutine.wrap(-> each_tag(ast, "FnCall","MethodCallUpdate"))
            if call.fn.__tag == "Var" and not (call.fn.__register or call.fn.__location)
                call_sig = "(#{concat [tostring(get_type(a)) for a in *call], ","})"
                top = call.__parent
                while top.__parent do top = top.__parent
                candidates = {}
                for decl in coroutine.wrap(-> each_tag(top, "FnDecl"))
                    if decl.name[0] == call.fn[0]
                        table.insert candidates, "#{call.fn[0]}#{get_type(decl)}"

                node_assert #candidates > 0, call.fn, "There is no function with this name"
                node_assert #candidates > 1, call.fn, "This function is being called with: #{call.fn[0]}#{call_sig} which doesn't match the definition: #{candidates[1]}"
                node_error call.fn, "This function is being called with: #{call.fn[0]}#{call_sig} which doesn't match any of the definitions:\n  - #{concat candidates, "\n  - "}"

        -- Compile functions:
        for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl", "Lambda"))
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
        for var in pairs file_scope_vars
            code ..= "data #{var.__location} = {#{get_type(var).base_type} 0}\n"
        code ..= "#{@fn_code}\n" if #@fn_code > 0

        code ..= "export function l $load() {\n"
        code ..= "@start\n"
        code ..= body_code
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

for_loop = (env, make_body)=>
    -- Rough breakdown:
    -- i = 0 | k = NULL
    -- len = #list
    -- jmp @for.next
    -- @for.next
    -- i += 1 | k = hashmap_next(h, k)
    -- jnz (i > len), @for.end, @for.body
    -- @for.body
    -- index = i
    -- item = list[i] | hashmap_get(h, k)
    -- // body code
    -- i += 1 | k = hashmap_next(h, k)
    -- jnz (i <= len), @for.end, @for.between
    -- @for.between
    -- // between code
    -- jmp @for.body
    -- @for.end

    iter_type = get_type @iterable
    next_label,body_label,between_label,end_label = env\fresh_labels "for.next","for.body","for.between","for.end"

    for skip in coroutine.wrap(-> each_tag(@, "Skip"))
        if not skip.target or skip.target[0] == "for" or (@val and skip.target[0] == @val[0]) or (@index and skip.target[0] == @index[0])
            skip.jump_label = next_label

    for stop in coroutine.wrap(-> each_tag(@, "Stop"))
        if not stop.target or stop.target[0] == "for" or (@val and stop.target[0] == @val[0]) or (@index and stop.target[0] == @index[0])
            stop.jump_label = end_label

    i = env\fresh_local(iter_type\is_a(Types.TableType) and "k" or "i")
    len = env\fresh_local "len"
    is_done = env\fresh_local "for.is_done"

    code = "# For loop:\n"
    iter_reg,iter_code = env\to_reg @iterable
    code ..= iter_code
    code ..= "#{i} =l copy 0\n"
    local list_item
    if iter_type\is_a(Types.Range)
        code ..= "#{len} =l call $range_len(l #{iter_reg})\n"
    elseif iter_type\is_a(Types.ListType)
        code ..= "#{len} =l loadl #{iter_reg}\n"
        list_item = env\fresh_local "list.item"
        code ..= "#{list_item} =l add #{iter_reg}, 8\n"
        code ..= "#{list_item} =l loadl #{list_item}\n"
    elseif iter_type\is_a(Types.TableType)
        _=nil -- Len is not used for tables
        -- code ..= "#{len} =l call $hashmap_len(l #{iter_reg})\n"
    else
        node_error @iterable, "Expected an iterable type, not #{iter_type}"
    code ..= "jmp #{next_label}\n"
    code ..= env\block next_label, ->
        code = ""
        if iter_type\is_a(Types.TableType)
            code ..= "#{i} =l call $hashmap_next(l #{iter_reg}, l #{i})\n"
            code ..= "jnz #{i}, #{body_label}, #{end_label}\n"
        else
            code ..= "#{i} =l add #{i}, 1\n"
            code ..= "#{is_done} =l csgtl #{i}, #{len}\n"
            code ..= "jnz #{is_done}, #{end_label}, #{body_label}\n"
        return code

    code ..= env\block body_label, ->
        code = ""
        if @index
            index_reg = assert @index.__register, "Index variable isn't hooked up"
            if iter_type\is_a(Types.TableType)
                code ..= convert_nil(iter_type.key_type, env, i, index_reg)
            else
                code ..= "#{index_reg} =l copy #{i}\n"

        if @val
            var_reg = assert @val.__register, "Iterator value variable isn't hooked up"
            if iter_type\is_a(Types.TableType)
                if @index
                    value_raw = env\fresh_local "value.raw"
                    code ..= "#{value_raw} =l call $hashmap_get(l #{iter_reg}, l #{i})\n"
                    code ..= convert_nil(iter_type.value_type, env, value_raw, var_reg)
                else
                    code ..= convert_nil(iter_type.key_type, env, i, var_reg)
            elseif iter_type\is_a(Types.Range)
                -- TODO: optimize to not use function call and just do var=start ... var += step
                code ..= "#{var_reg} =l call $range_nth(l #{iter_reg}, l #{i})\n"
            else
                code ..= "#{var_reg} =#{iter_type.item_type.base_type} load#{iter_type.item_type.base_type} #{list_item}\n"
                code ..= "#{list_item} =l add #{list_item}, 8\n"

        code ..= env\compile_stmt @filter if @filter
        code ..= (make_body and make_body(index_reg, var_reg) or env\compile_stmt(@body))

        -- If we reached this point, no skips
        unless has_jump\match(code)
            if iter_type\is_a(Types.TableType)
                code ..= "#{i} =l call $hashmap_next(l #{iter_reg}, l #{i})\n"
                code ..= "jnz #{i}, #{between_label}, #{end_label}\n"
            else
                code ..= "#{i} =l add #{i}, 1\n"
                code ..= "#{is_done} =l csgtl #{i}, #{len}\n"
                code ..= "jnz #{is_done}, #{end_label}, #{between_label}\n"

        return code

    code ..= env\block between_label, ->
        code = ""
        if @between
            code ..= env\compile_stmt @between

        unless has_jump\match(code)
            code ..= "jmp #{body_label}\n"
        return code

    code ..= "#{end_label}\n"
    return code

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

expr_compilers =
    Var: (env)=>
        if @__register
            return @__register, ""
        elseif @__location
            t = get_type(@)
            tmp = env\fresh_local "#{@[0]}.value"
            return tmp, "#{tmp} =#{t.base_type} load#{t.base_type} #{@__location}\n"
        elseif get_type(@) == Types.TypeString
            t = parse_type(@)
            return env\get_string_reg(t\verbose_type!, @[0]), ""
        node_error @, "This variable is not defined"
    Declaration: (env)=>
        code = env\compile_stmt @
        var_reg,var_code = env\to_reg @var
        return var_reg, code..var_code
    Global: (env)=>
        return "#{@[0]}", ""
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
            return "d_#{n}",""

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
                t = get_type(other)
                if t\is_a(Types.OptionalType) and t != Types.NilType
                    t = t.nonnil
                return "#{t.nil_value}",""

            t = if parent.__tag == "Declaration"
                get_type parent.value
            elseif parent.__tag == "Assignment"
                get_type parent.lhs
            elseif parent.__tag == "StructField"
                field = parent
                while parent.__tag != "Struct"
                    parent = parent.__parent
                struct_type = get_type parent
                if field.name
                    struct_type.members[field.name].type
                else
                    field_type = nil
                    for i,f in ipairs field.__parent
                        if f == field
                            field_type = node_assert(struct_type.members[i] or struct_type.sorted_members[i], @, "Not a #{struct_type} field").type
                            break
                    field_type
            elseif parent.__tag == "TableEntry"
                entry = parent
                tab = parent.__parent
                while tab.__tag != "Table"
                    tab = tab.__parent
                table_type = get_type(tab)
                child == entry.key and table_type.key_type or table_type.value_type
            elseif parent.__tag == "FnDecl" or parent.__tag == "Lambda"
                break
            else
                get_type(parent)

            if t != Types.NilType and t\is_a(Types.OptionalType)
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
        if abt == "l" and cbt == "w"
            code ..= "#{c} =w copy #{reg}\n"
        elseif abt == "w" and cbt == "l"
            code ..= "#{c} =l extsw #{reg}\n"
        elseif abt == "s" and cbt == "d"
            code ..= "#{c} =d exts #{reg}\n"
        elseif abt == "d" and cbt == "s"
            code ..= "#{c} =d truncd #{reg}\n"
        else
            code ..= "#{c} =#{cast_type.base_type} cast #{reg}\n"
        return c,code
    TypeOf: (env)=>
        return env\get_string_reg(get_type(@expression)\verbose_type!, "typename"), ""
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
                t = get_type(chunk)
                val_reg,val_code = env\to_reg chunk
                code ..= val_code
                if t == Types.String
                    code ..= "#{chunk_reg} =l copy #{val_reg}\n"
                else
                    fn,needs_loading = env\get_tostring_fn t, @
                    code ..= "#{fn} =l loadl #{fn}\n" if needs_loading
                    code ..= "#{chunk_reg} =l call #{fn}(#{t.base_type} #{val_reg}, l 0)\n"

            code ..= "#{cord_reg} =l call $CORD_cat(l #{cord_reg}, l #{chunk_reg})\n"
                
        code ..= "#{cord_reg} =l call $CORD_to_const_char_star(l #{cord_reg})\n"
        code ..= "#{str} =l call $bl_string(l #{cord_reg})\n"
        return str,code

    DSL: (env)=>
        content = @string.content
        str = env\fresh_local "str"
        if #content == 0
            code = "#{str} =l call $bl_string(l #{env\get_string_reg(content[0])})\n"
            return str, code

        code = "#{str} =l call $bl_string(l #{env\get_string_reg("", "emptystr")})\n"
        dsl_type = get_type(@)

        stringify = (val)->
            t = get_type(val)
            val_reg,val_code = env\to_reg val
            code ..= val_code
            safe = if t == dsl_type
                val_reg
            else
                fn_reg,needs_loading = get_function_reg @__parent, "escape", {t}, dsl_type
                node_assert fn_reg, val, "No escape(#{t})=>#{dsl_type} function is implemented, so this value cannot be safely inserted"
                code ..= "#{fn_reg} =l loadl #{fn_reg}\n" if needs_loading
                escaped = env\fresh_local "escaped"
                code ..= "#{escaped} =l call #{fn_reg}(#{t.base_type} #{val_reg})\n"
                escaped
            code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{safe})\n"

        i = content.start
        for interp in *content
            if interp.start > i
                chunk = content[0]\sub(1+(i-content.start), interp.start-content.start)
                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{env\get_string_reg chunk})\n"

            stringify(interp)
            i = interp.after

        if content.after > i
            chunk = content[0]\sub(1+(i-content.start), content.after-content.start)
            code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{env\get_string_reg chunk})\n"

        return str,code

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
        if t\is_a(Types.OptionalType) and t != Types.NilType and t.nonnil\is_a(Types.Int)
            code ..= "#{ret} =w ceq#{t.base_type} #{b}, #{t.nil_value}\n"
        elseif t\is_a(Types.OptionalType) and t != Types.NilType and t.nonnil.base_type == "d"
            code ..= "#{ret} =w cuod #{reg}, d_0.0 # Test for NaN\n"
        elseif t\is_a(Types.Bool)
            code ..= "#{ret} =w cne#{t.base_type} #{b}, 1\n"
        else
            code ..= "#{ret} =w ceq#{t.base_type} #{b}, 0\n"
        return ret, code
    IndexedTerm: (env)=>
        t = get_type @value
        t0 = get_type @
        if t0\is_a(Types.EnumType) and t == Types.TypeString
            for i,field in ipairs(t0.fields)
                if field == @index[0]
                    -- Enum values start with 1, so nil is 0
                    return "#{i}",""
            node_error @, "Couldn't find enum field: .#{@index[0]} on type #{t0}"

        is_optional = t\is_a(Types.OptionalType) and t != Types.NilType
        t = t.nonnil if is_optional
        nil_guard = (check_reg, output_reg, output_type, get_nonnil_code)->
            unless is_optional
                return get_nonnil_code!

            ifnil,ifnonnil,done = env\fresh_labels "if.nil", "if.nonnil", "if.nil.done"
            code = check_nil get_type(@value), env, check_reg, ifnonnil, ifnil
            code ..= env\block ifnonnil, -> (get_nonnil_code!.."jmp #{done}\n")
            code ..= env\block ifnil, -> set_nil(output_type, env, output_reg)
            code ..= "#{done}\n"
            return code
            
        if t\is_a(Types.ListType)
            item_type = t.item_type
            index_type = get_type(@index)
            list_reg, index_reg, code = env\to_regs @value, @index
            if index_type\is_a(Types.Int) or index_type == Types.OptionalType(Types.Int)
                item = env\fresh_local "list.item"
                code = nil_guard list_reg, item, item_type, ->
                    not_too_low,not_too_high,outside_bounds,done = env\fresh_labels "not.too.low", "not.too.high", "outside.bounds", "done"
                    len, bounds_check = env\fresh_locals "len", "bounds.check"
                    code ..= "#{bounds_check} =w csgel #{index_reg}, 1\n"
                    code ..= "jnz #{bounds_check}, #{not_too_low}, #{outside_bounds}\n"
                    code ..= env\block not_too_low, ->
                        code = "#{len} =l loadl #{list_reg}\n"
                        code ..= "#{bounds_check} =w cslel #{index_reg}, #{len}\n"
                        return code.."jnz #{bounds_check}, #{not_too_high}, #{outside_bounds}\n"

                    code ..= env\block not_too_high, ->
                        code = ""
                        items = env\fresh_local "items"
                        code ..= "#{items} =l add #{list_reg}, 8\n"
                        code ..= "#{items} =l loadl #{items}\n"
                        offset = env\fresh_local "offset"
                        code ..= "#{offset} =l sub #{index_reg}, 1\n"
                        code ..= "#{offset} =l mul #{offset}, #{item_type.bytes}\n"
                        code ..= "#{items} =l add #{items}, #{offset}\n"
                        if item_type.base_type == "d" or item_type.base_type == "s"
                            tmp = env\fresh_local "list.item.as_int"
                            int_type = item_type.base_type == "d" and "l" or "w"
                            code ..= "#{tmp} =#{int_type} load#{int_type} #{items}\n"
                            code ..= "#{item} =d cast #{tmp}\n"
                        elseif item_type.bytes < 8
                            code ..= "#{item} =#{item_type.base_type} loadu#{item_type.abi_type} #{items}\n"
                        else
                            code ..= "#{item} =l loadl #{items}\n"
                        return code .. "jmp #{done}\n"

                    code ..= env\block outside_bounds, ->
                        code = set_nil(item_type, env, item)
                        return code.."jmp #{done}\n"

                    return code.."#{done}\n"

                return item,code
            elseif index_type\is_a(Types.Range)
                slice = env\fresh_local "slice"
                code ..= nil_guard list_reg, slice, t, ->
                    range,code = env\to_reg @index
                    -- use_aliasing = if @__parent.__tag == "For" and @ == @__parent.iterable
                    --     "1"
                    -- else
                    --     "0"
                    use_aliasing = "1" -- Should always be safe
                    code ..= "#{slice} =l call $bl_list_slice(l #{list_reg}, l #{range}, l #{t.item_type.bytes}, w #{use_aliasing})\n"
                    return code
                return slice,code
            else
                node_error @index, "Index is #{index_type} instead of Int or Range"
        elseif t\is_a(Types.TableType)
            tab_reg, index_reg, code = env\to_regs @value, @index
            value_reg = env\fresh_local "value"
            code ..= nil_guard tab_reg, value_reg, t.key_type, ->
                code = ""
                key_getter = env\fresh_local "key.getter"
                code ..= hash_prep t.key_type, index_reg, key_getter
                raw_value = env\fresh_local "value.raw"
                code ..= "#{raw_value} =l call $hashmap_get(l #{tab_reg}, l #{key_getter})\n"
                code ..= convert_nil t.value_type, @, raw_value, value_reg
                return code

            return value_reg,code
        elseif t\is_a(Types.StructType)
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
                code = "#{loc} =l add #{struct_reg}, #{member.offset}\n"
                return code.."#{ret} =#{member.type.base_type} load#{member.type.base_type} #{loc}\n"
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
                code ..= "#{ret} =#{member.type.base_type} load#{member.type.abi_type} #{value_loc}\n"
                code ..= "jmp #{done}\n"
                return code
            code ..= env\block use_nil, ->
                set_nil(member.type, env, ret).."jmp #{done}\n"
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
            node_error @value, "Indexing is not valid on type #{t}"
    List: (env)=>
        list,list_items,size,p = env\fresh_locals "list", "list.items", "list.size", "p"
        code = "#{list} =l call $gc_alloc(l 16)\n"
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
            code ..= "store#{item_type.abi_type} #{item_reg}, #{p}\n"
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
                    code ..= check_truthiness get_type(cond), env, cond_reg, true_label, next_label
                    code ..= "#{true_label}\n"
                    code ..= add_item(expr)
                when "For"
                    code ..= for_loop val, env, (-> add_item(val.body[1]))
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

        return list, code
    Table: (env)=>
        t = get_type @
        node_assert not t.key_type\is_a(Types.OptionalType) and not t.value_type\is_a(Types.OptionalType), @,
            "Nil cannot be stored in a table, but this table is #{t}"

        tab = env\fresh_local "table.empty"
        code = "#{tab} =l call $hashmap_new(l 0)\n"
        if #@ == 0
            return tab, code

        add_entry = (entry)->
            key_reg, value_reg, code = env\to_regs entry.key, entry.value
            key_setter = env\fresh_local "key.setter"
            code ..= hash_prep t.key_type, key_reg, key_setter
            value_setter = env\fresh_local "value.setter"
            code ..= hash_prep t.value_type, value_reg, value_setter
            code ..= "call $hashmap_set(l #{tab}, l #{key_setter}, l #{value_setter})\n"
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
                    code ..= check_truthiness get_type(cond), env, cond_reg, true_label, next_label
                    code ..= "#{true_label}\n"
                    code ..= add_entry expr
                when "For"
                    code ..= for_loop val, env, (-> add_entry(val.body[1]))
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
                code ..= check_truthiness get_type(val), env, val_reg, done_label, false_label
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
                code ..= check_truthiness get_type(val), env, val_reg, true_label, done_label
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
            elseif t_lhs == t_rhs and t_lhs\is_a(Types.String)
                return infixop @, env, (ret,lhs,rhs)->
                    "#{ret} =l call $bl_string_append_string(l #{lhs}, l #{rhs})\n"
            elseif t_lhs\is_a(Types.ListType) and t_rhs\is_a(t_lhs.item_type)
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
                    code ..= "store#{item_type.abi_type} #{item_reg}, #{tmp}\n"
                    code ..= "#{ret} =l call $gc_alloc(l 16)\n"
                    code ..= "storel #{new_len}, #{ret}\n"
                    code ..= "#{tmp} =l add #{ret}, 8\n"
                    code ..= "storel #{new_items}, #{tmp}\n"
                    code ..= "\n"
                    return code
            elseif t_rhs\is_a(Types.ListType) and t_lhs\is_a(t_rhs.item_type)
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
                    code ..= "store#{item_type.abi_type} #{item_reg}, #{new_items}\n"
                    code ..= "#{tmp} =l add #{new_items}, #{item_type.bytes}\n"
                    code ..= "call $memcpy(l #{tmp}, l #{items}, l #{size})\n"
                    code ..= "#{ret} =l call $gc_alloc(l 16)\n"
                    code ..= "storel #{new_len}, #{ret}\n"
                    code ..= "#{tmp} =l add #{ret}, 8\n"
                    code ..= "storel #{new_items}, #{tmp}\n"
                    code ..= "\n"
                    return code
            elseif t_lhs == t_rhs and t_lhs\is_a(Types.ListType)
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
                return overload_infix @, env, "add", "sum"
        else -- "-"
            if tl_nn == tr_nn and (tl_nn\is_numeric! or tl_nn\is_a(Types.MeasureType))
                return infixop @, env, "sub"
            else
                return overload_infix @, env, "subtract", "difference"
    MulDiv: (env)=>
        t_lhs,t_rhs = get_type(@lhs),get_type(@rhs)
        tl_nn, tr_nn = (t_lhs.nonnil or t_lhs), (t_rhs.nonnil or t_rhs)
        if @op[0] == "*"
            if tl_nn == tr_nn and tl_nn\is_numeric!
                return infixop @, env, "mul"
            elseif (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.Num)) or (tl_nn\is_a(Types.Num) and tr_nn\is_a(Types.MeasureType)) or (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.MeasureType))
                return infixop @, env, "mul"
            else
                return overload_infix @, env, "multiply", "product"
        else -- "/"
            if tl_nn == tr_nn and tl_nn\is_numeric!
                return infixop @, env, "div"
            elseif (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.Num)) or (tl_nn\is_a(Types.Num) and tr_nn\is_a(Types.MeasureType)) or (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.MeasureType))
                return infixop @, env, "div"
            else
                return overload_infix @, env, "divide", "quotient"
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
            return overload_infix @, env, "modulus", "remainder"
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
            return overload_infix @, env, "raise", "raised"
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

                node_assert get_type(override.value)\is_a(member.type), override.value, "Not a #{member.type}"
                val_reg,val_code = env\to_reg override.value
                code ..= val_code
                code ..= "#{p} =l add #{ret}, #{member.offset}\n"
                code ..= "store#{member.type.base_type} #{val_reg}, #{p}\n"

            -- code ..= "#{ret} =l call $intern_bytes(l #{ret}, l #{struct_size})\n"
            return ret, code
        else
            node_error @, "| operator is only supported for List and Struct types"
    In: (env)=>
        haystack_type = get_type(@haystack)
        needle_type = get_type(@needle)
        if haystack_type\is_a(Types.ListType) and needle_type\is_a(haystack_type.item_type)
            found = env\fresh_locals "found"
            done = env\fresh_label "in.done"
            needle_reg,code = env\to_reg @needle
            code ..= "#{found} =w copy 0\n"
            item_reg = env\fresh_local("item")
            code ..= for_loop {iterable: @haystack, val:{__register:item_reg}}, env, ->
                base_type = haystack_type.item_type.base_type
                code = if needle_type == Types.NilType and (base_type == 's' or base_type == 'd')
                    "#{found} =w cuo#{base_type} #{item_reg}, #{base_type}_0.0\n"
                else
                    "#{found} =w ceq#{base_type} #{item_reg}, #{needle_reg}\n"
                keep_going = env\fresh_label "keep_going"
                code ..= "jnz #{found}, #{done}, #{keep_going}\n"
                code ..= "#{keep_going}\n"
                return code
            code ..= "#{done}\n"
            return found, code
        elseif haystack_type\is_a(Types.TableType) and needle_type\is_a(haystack_type.key_type)
            needle_reg,haystack_reg,code = env\to_regs @needle, @haystack
            key_getter = env\fresh_local "key.getter"
            code ..= hash_prep haystack_type.key_type, needle_reg, key_getter
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
    TernaryOp: (env)=>
        overall_type = get_type @
        cond_reg,code = env\to_reg @condition
        true_reg,true_code = env\to_reg @ifTrue
        false_reg,false_code = env\to_reg @ifFalse
        true_label,false_label,end_label = env\fresh_labels "ternary.true","ternary.false","ternary.end"
        ret_reg = env\fresh_local "ternary.result"
        code ..= check_truthiness get_type(@condition), env, cond_reg, true_label, false_label
        code ..= env\block true_label, ->
            "#{true_code}#{ret_reg} =#{overall_type.base_type} copy #{true_reg}\njmp #{end_label}\n"
        code ..= env\block false_label, ->
            "#{false_code}#{ret_reg} =#{overall_type.base_type} copy #{false_reg}\njmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return ret_reg, code

    FnCall: (env, skip_ret=false)=>
        fn_type = get_type @fn
        fn_reg,code = env\to_reg @fn

        local arg_list
        if fn_type
            node_assert fn_type\is_a(Types.FnType), @fn, "This is not a function, it's a #{fn_type or "???"}"
            arg_types,arg_text = {},{}
            for arg in *@
                if arg.__tag == "KeywordArg"
                    arg_types[arg.name[0]] = get_type(arg.value)
                    table.insert arg_text, "#{arg.name[0]}=#{get_type arg.value}"
                else
                    table.insert arg_types, get_type(arg)
                    table.insert arg_text, "#{get_type arg}"
            node_assert fn_type\matches(arg_types), @,
                "This function is being called with #{@fn[0]}(#{concat arg_text, ", "}) but is defined as #{fn_type}"

            kw_args = {}
            pos_args = {}
            for arg in *@
                if arg.__tag == "KeywordArg"
                    arg_reg, arg_code = env\to_reg arg.value
                    code ..= arg_code
                    kw_args[arg.name[0]] = arg_reg
                else
                    arg_reg, arg_code = env\to_reg arg
                    code ..= arg_code
                    table.insert pos_args, arg_reg

            if fn_type.arg_names
                arg_list = {}
                assert fn_type.arg_names, "No arg names: #{fn_type}"
                for i,name in ipairs fn_type.arg_names
                    arg_reg = kw_args[name] or table.remove(pos_args, 1)
                    if not arg_reg
                        arg_reg = env\fresh_local name
                        code ..= set_nil fn_type.arg_types[i], env, arg_reg
                    table.insert arg_list, "#{fn_type.arg_types[i].base_type} #{arg_reg}"

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
        code ..= "#{ret_reg} =#{ret_type.base_type} call #{fn_reg}(#{concat arg_list, ", "})\n"
        return ret_reg, code

    Lambda: (env)=>
        node_assert @__register, @, "Unreferenceable lambda"
        return @__register,""

    Struct: (env)=>
        t = get_type @
        ret = env\fresh_local "#{t.name\lower!}"
        code = "#{ret} =l call $gc_alloc(l #{t.memory_size})\n"
        i = 0
        unpopulated = {n:memb for n,memb in pairs t.members}
        for field in *@
            memb = if field.name
                t.members[field.name[0]]
            else
                i += 1
                t.members[i] or t.sorted_members[i]

            node_assert memb, field, "Not a valid struct member"
            m_t = get_type field.value
            node_assert m_t\is_a(memb.type), field, "Expected this value to have type #{memb.type}, but got #{m_t}"

            loc = env\fresh_local "#{t\id_str!\lower!}.#{memb.name}.loc"
            code ..= "#{loc} =l add #{ret}, #{memb.offset}\n"
            val_reg,val_code = env\to_reg field.value
            code ..= val_code
            code ..= "store#{m_t.base_type} #{val_reg}, #{loc}\n"
            unpopulated[memb.name] = nil

        for name,memb in pairs unpopulated
            continue unless memb\is_a(Types.OptionalType)
            unpopulated[name] = nil
            continue if memb.type.nil_value == 0
            loc = env\fresh_local "#{t\id_str!\lower!}.#{memb.name}.loc"
            code ..= "#{loc} =l add #{ret}, #{memb.offset}\n"
            code ..= "store#{memb.type.base_type} #{memb.type.nil_value}, #{loc}\n"

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
        ret = env\fresh_local "if.value"
        code = ""
        end_label,false_label = env\fresh_labels "if.end", "if.else"
        for cond in *@
            r,cond_code = env\to_reg cond.condition
            code ..= cond_code
            true_label = env\fresh_label "if.true"
            code ..= check_truthiness get_type(cond.condition), env, r, true_label, false_label
            code ..= "#{true_label}\n"
            t = get_type(cond.body)
            if t == Types.Void
                code ..= env\compile_stmt cond.body
            else
                block_reg,block_code = env\to_reg cond.body
                code ..= block_code
                code ..= "#{ret} =#{t.base_type} copy #{block_reg}\n"
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
            code ..= "#{false_label}\n"
            false_label = env\fresh_label "if.else"

        if @elseBody
            t = get_type(@elseBody)
            if t == Types.Void
                code ..= env\compile_stmt @elseBody
            else
                block_reg,block_code = env\to_reg @elseBody
                code ..= block_code
                code ..= "#{ret} =#{t.base_type} copy #{block_reg}\n"
                
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
        else
            code ..= set_nil get_type(@), env, ret

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
            code ..= check_nil Types.OptionalType(get_type(@)), env, mod, success_label, fail_label
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
            code ..= check_nil Types.OptionalType(get_type(@)), env, mod, success_label, fail_label
            code ..= env\block fail_label, -> env\compile_stmt(@orElse)
            code ..= "jmp #{done_label}\n" unless has_jump\match(code)
            code ..= "#{success_label}\n"

        for i,mem in ipairs @__imports
            loc = env\fresh_local "#{name}.#{mem[0]}.loc"
            code ..= "#{loc} =l add #{mod}, #{8*(i-1)}\n"
            tmp = env\fresh_local "#{name}.#{mem[0]}"
            code ..= "#{tmp} =#{mem.__type.base_type} load#{mem.__type.base_type} #{loc}\n"
            code ..= "storel #{tmp}, #{mem.__location}\n"

        if @orElse
            code ..= "jmp #{done_label}\n" unless has_jump\match(code)
            code ..= "#{done_label}\n"
        return code
    Declaration: (env)=>
        value_type = get_type @value
        val_reg,code = env\to_reg @value
        if @var.__register
            code ..= "#{@var.__register} =#{value_type.base_type} copy #{val_reg}\n"
        elseif @var.__location
            code ..= "store#{value_type.base_type} #{val_reg}, #{@var.__location}\n"
        else
            node_error @var, "Undefined variable"
        return code
    Assignment: (env)=>
        lhs_type,rhs_type = get_type(@lhs), get_type(@rhs)
        if @lhs.__tag == "Var"
            node_assert rhs_type\is_a(lhs_type), @rhs, "Assignment value is type #{rhs_type}, but it's being assigned to something with type #{lhs_type}"
            rhs_reg,code = env\to_reg @rhs
            if @lhs.__register
                return code.."#{@lhs.__register} =#{lhs_type.base_type} copy #{rhs_reg}\n"
            elseif @lhs.__location
                return code.."store#{lhs_type.base_type} #{rhs_reg}, #{@lhs.__location}\n"
            node_assert @lhs.__register or @lhs.__location, @lhs, "Undefined variable"
        
        node_assert @lhs.__tag == "IndexedTerm", @lhs, "Expected a Var or an indexed value"
        t = get_type(@lhs.value)
        is_optional = t\is_a(Types.OptionalType)
        t = t.nonnil if is_optional
        if t\is_a(Types.ListType)
            index_type = get_type(@lhs.index)
            list_reg,index_reg,rhs_reg,code = env\to_regs @lhs.value, @lhs.index, @rhs
            if index_type\is_a(Types.Int) or index_type == Types.OptionalType(Types.Int)
                if rhs_type.base_type == "d"
                    rhs_casted = env\fresh_local "list.item.float"
                    code ..= "#{rhs_casted} =d cast #{rhs_reg}\n"
                    rhs_reg = rhs_casted
                nonnil_label, end_label = env\fresh_labels "if.nonnil", "if.nonnil.done"
                code ..= check_nil get_type(@lhs.value), env, list_reg, nonnil_label, end_label
                code ..= env\block nonnil_label, ->
                    not_too_low,not_too_high = env\fresh_labels "not.too.low", "not.too.high"
                    len, bounds_check = env\fresh_locals "len", "bounds.check"
                    code = "#{bounds_check} =w csgel #{index_reg}, 1\n"
                    code ..= "jnz #{bounds_check}, #{not_too_low}, #{end_label}\n"
                    code ..= env\block not_too_low, ->
                        code = "#{len} =l loadl #{list_reg}\n"
                        code ..= "#{bounds_check} =w cslel #{index_reg}, #{len}\n"
                        return code.."jnz #{bounds_check}, #{not_too_high}, #{end_label}\n"

                    code ..= env\block not_too_high, ->
                        p = env\fresh_local "p"
                        code = "#{p} =l add #{list_reg}, 8\n"
                        code ..= "#{p} =l loadl #{p}\n"
                        offset = env\fresh_local "offset"
                        code ..= "#{offset} =l sub #{index_reg}, 1\n"
                        code ..= "#{offset} =l mul #{offset}, #{t.item_type.bytes}\n"
                        code ..= "#{p} =l add #{p}, #{offset}\n"
                        code ..= "store#{t.item_type.abi_type} #{rhs_reg}, #{p}\n"
                        return code.."jmp #{end_label}\n"

                    return code
                code ..= "#{end_label}\n"
                return code
            elseif index_type\is_a(Types.Range)
                node_error @lhs.index, "Assigning to list slices is not supported."
            else
                node_error @lhs.index, "Index is #{index_type} instead of Int or Range"
            return
        elseif t\is_a(Types.TableType)
            key_type = get_type(@lhs.index)
            tab_reg,key_reg,val_reg,code = env\to_regs @lhs.value, @lhs.index, @rhs

            key_setter = env\fresh_local "key.setter"
            code ..= hash_prep t.key_type, key_reg, key_setter
            value_setter = env\fresh_local "value.setter"
            code ..= hash_prep t.value_type, val_reg, value_setter

            nonnil_label, end_label = env\fresh_labels "if.nonnil", "if.nonnil.done"
            code ..= check_nil get_type(@lhs.value), env, tab_reg, nonnil_label, end_label

            code ..= env\block nonnil_label, ->
                ("call $hashmap_set(l #{tab_reg}, l #{key_setter}, l #{value_setter})\n"..
                 "jmp #{end_label}\n")
            code ..= "#{end_label}\n"
            return code
        elseif t\is_a(Types.StructType)
            memb = if @lhs.index.__tag == "FieldName"
                member_name = @lhs.index[0]
                node_assert t.members[member_name], @lhs.index, "Not a valid struct member of #{t}"
                t.members[member_name]
            elseif @lhs.index.__tag == "Int"
                i = tonumber(@lhs.index[0])
                node_assert t.members, @lhs.index, "#{t} only has members between 1 and #{#t.members}"
                t.members[i]
            else
                node_error @lhs.index, "Structs can only be indexed by a field name or Int literal"
            struct_reg,rhs_reg,code = env\to_regs @lhs.value, @rhs
            nonnil_label, end_label = env\fresh_labels "if.nonnil", "if.nonnil.done"
            code ..= check_nil get_type(@lhs.value), env, struct_reg, nonnil_label, end_label
            code ..= env\block nonnil_label, ->
                loc = env\fresh_local "member.loc"
                code = "#{loc} =l add #{struct_reg}, #{memb.offset}\n"
                code ..= "store#{rhs_type.base_type} #{rhs_reg}, #{loc}\n"
                code ..= "jmp #{end_label}\n"
                return code
            code ..= "#{end_label}\n"

            return code
        else
            node_error @lhs.value, "Only Lists and Structs are mutable, not #{t}"
            return
    AddUpdate: (env)=>
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
        store_code = @lhs.__location and "store#{lhs_type.base_type} #{lhs_reg}, #{@lhs.__location}\n" or ""
        if nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            return code.."#{lhs_reg} =#{lhs_type.base_type} add #{lhs_reg}, #{rhs_reg}\n"..store_code
        elseif lhs_type == rhs_type and lhs_type\is_a(Types.String)
            return code.."#{lhs_reg} =l call $bl_string_append_string(l #{lhs_reg}, l #{rhs_reg})\n"..store_code
        elseif lhs_type\is_a(Types.ListType) and rhs_type\is_a(lhs_type.item_type)
            len,size,items,tmp = env\fresh_locals "len","size","items","tmp"
            code ..= "\n# Append\n"
            code ..= "#{len} =l loadl #{lhs_reg}\n"
            code ..= "#{tmp} =l add #{lhs_reg}, 8\n"
            code ..= "#{items} =l loadl #{tmp}\n"
            code ..= "#{len} =l add #{len}, 1\n"
            code ..= "storel #{len}, #{lhs_reg}\n"
            code ..= "#{size} =l mul #{len}, #{lhs_type.item_type.bytes}\n"

            -- code ..= "#{items} =l call $gc_realloc(l #{items}, l #{size})\n"
            -- NOTE: for correctness, this is deliberately *not* using realloc, but instead
            -- using allocation and copying. This is to handle situations where a list
            -- is being modified while it's being iterated over.
            new_items = env\fresh_local "new_items"
            code ..= "#{new_items} =l call $gc_alloc(l #{size})\n"
            code ..= "call $memcpy(l #{new_items}, l #{items}, l #{size})\n"

            code ..= "#{tmp} =l add #{lhs_reg}, 8\n"
            code ..= "storel #{new_items}, #{tmp}\n"
            code ..= "#{tmp} =l add #{new_items}, #{size}\n"
            code ..= "#{tmp} =l sub #{tmp}, #{lhs_type.item_type.bytes}\n"
            code ..= "storel #{rhs_reg}, #{tmp}\n"
            code ..= "\n"
            return code
        elseif lhs_type == rhs_type and lhs_type\is_a(Types.ListType)
            len1,len2,new_len,size,items1,items2,tmp = env\fresh_locals "len1","len2","new_len","size","items1","items2","tmp"
            code ..= "\n# Add Update\n"
            code ..= "#{len1} =l loadl #{lhs_reg}\n"
            code ..= "#{tmp} =l add #{lhs_reg}, 8\n"
            code ..= "#{items1} =l loadl #{tmp}\n"
            code ..= "#{len2} =l loadl #{rhs_reg}\n"
            code ..= "#{new_len} =l add #{len1}, #{len2}\n"
            code ..= "#{size} =l mul #{new_len}, #{lhs_type.item_type.bytes}\n"

            -- code ..= "#{items1} =l call $gc_realloc(l #{items1}, l #{size})\n"
            -- NOTE: this uses gc_alloc instead of gc_realloc intentionally, see previous note
            new_items = env\fresh_local "new_items"
            code ..= "#{new_items} =l call $gc_alloc(l #{size})\n"
            code ..= "#{size} =l mul #{len1}, #{lhs_type.item_type.bytes}\n"
            code ..= "call $memcpy(l #{new_items}, l #{items1}, l #{size})\n"

            p = env\fresh_local "p"
            code ..= "#{tmp} =l add #{lhs_reg}, 8\n"
            code ..= "storel #{new_items}, #{tmp}\n"
            code ..= "#{p} =l mul #{len1}, #{lhs_type.item_type.bytes}\n"
            code ..= "#{p} =l add #{p}, #{new_items}\n"
            code ..= "#{size} =l mul #{len2}, #{lhs_type.item_type.bytes}\n"
            code ..= "#{tmp} =l add #{rhs_reg}, 8\n"
            code ..= "#{items2} =l loadl #{tmp}\n"
            code ..= "call $memcpy(l #{p}, l #{items2}, l #{size})\n"
            code ..= "storel #{new_len}, #{lhs_reg}\n"
            code ..= "\n"
            return code
        else
            fn_reg, needs_loading, t2 = get_function_reg @__parent, "add", {lhs_type,rhs_type}, lhs_type
            node_assert fn_reg, @, "addition is not supported for #{lhs_type} and #{rhs_type}"
            code ..= "#{fn_reg} =l loadl #{fn_reg}\n" if needs_loading
            return code.."#{lhs_reg} =#{lhs_type.base_type} call #{fn_reg}(#{lhs_type.base_type} #{lhs_reg}, #{rhs_type.base_type} #{rhs_reg})\n"..store_code
    SubUpdate: (env)=>
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
        store_code = @lhs.__location and "store#{lhs_type.base_type} #{lhs_reg}, #{@lhs.__location}\n" or ""
        if nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            return code.."#{lhs_reg} =#{lhs_type.base_type} sub #{lhs_reg}, #{rhs_reg}\n"..store_code
        else
            fn_reg, needs_loading, t2 = get_function_reg @__parent, "subtract", {lhs_type,rhs_type}, lhs_type
            node_assert fn_reg, @, "subtraction is not supported for #{lhs_type} and #{rhs_type}"
            code ..= "#{fn_reg} =l loadl #{fn_reg}\n" if needs_loading
            return code.."#{lhs_reg} =#{lhs_type.base_type} call #{fn_reg}(#{lhs_type.base_type} #{lhs_reg}, #{rhs_type.base_type} #{rhs_reg})\n"..store_code
    MulUpdate: (env)=>
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
        store_code = @lhs.__location and "store#{lhs_type.base_type} #{lhs_reg}, #{@lhs.__location}\n" or ""
        if nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            return code.."#{lhs_reg} =#{lhs_type.base_type} mul #{lhs_reg}, #{rhs_reg}\n"..store_code
        else
            fn_reg, needs_loading, t2 = get_function_reg @__parent, "multiply", {lhs_type,rhs_type}, lhs_type
            node_assert fn_reg, @, "multiplication is not supported for #{lhs_type} and #{rhs_type}"
            code ..= "#{fn_reg} =l loadl #{fn_reg}\n" if needs_loading
            return code.."#{lhs_reg} =#{lhs_type.base_type} call #{fn_reg}(#{lhs_type.base_type} #{lhs_reg}, #{rhs_type.base_type} #{rhs_reg})\n"..store_code
    DivUpdate: (env)=>
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
        store_code = @lhs.__location and "store#{lhs_type.base_type} #{lhs_reg}, #{@lhs.__location}\n" or ""
        if nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            return code.."#{lhs_reg} =#{lhs_type.base_type} div #{lhs_reg}, #{rhs_reg}\n"..store_code
        else
            fn_reg, needs_loading, t2 = get_function_reg @__parent, "divide", {lhs_type,rhs_type}, lhs_type
            node_assert fn_reg, @, "division is not supported for #{lhs_type} and #{rhs_type}"
            code ..= "#{fn_reg} =l loadl #{fn_reg}\n" if needs_loading
            return code.."#{lhs_reg} =#{lhs_type.base_type} call #{fn_reg}(#{lhs_type.base_type} #{lhs_reg}, #{rhs_type.base_type} #{rhs_reg})\n"..store_code
    OrUpdate: (env)=>
        t_lhs, t_rhs = get_type(@lhs), get_type(@rhs)
        true_label,false_label = env\fresh_labels "or.lhs.true", "or.lhs.false"
        lhs_reg,code = env\to_reg @lhs
        code ..= check_truthiness t_lhs, env, lhs_reg, true_label, false_label
        code ..= env\block false_label, ->
            rhs_reg,code = env\to_reg @rhs
            code ..= "#{lhs_reg} =#{t_lhs.base_type} copy #{rhs_reg}\n"
            code ..= "store#{t_lhs.base_type} #{lhs_reg}, #{@lhs.__location}\n" if @lhs.__location
            code ..= "jmp #{true_label}\n"
            return code
        code ..= "#{true_label}\n"
        return code
    AndUpdate: (env)=>
        t_lhs, t_rhs = get_type(@lhs), get_type(@rhs)
        true_label,false_label = env\fresh_labels "and.lhs.true", "and.lhs.false"
        lhs_reg,code = env\to_reg @lhs
        code ..= check_truthiness t_lhs, env, lhs_reg, true_label, false_label
        code ..= env\block true_label, ->
            rhs_reg,code = env\to_reg @rhs
            code ..= "#{lhs_reg} =#{t_lhs.base_type} copy #{rhs_reg}\n"
            code ..= "store#{t_lhs.base_type} #{lhs_reg}, #{@lhs.__location}\n" if @lhs.__location
            code ..= "jmp #{false_label}\n"
            return code
        code ..= "#{false_label}\n"
        return code
    XorUpdate: (env)=>
        t_lhs, t_rhs = get_type(@lhs), get_type(@rhs)
        lhs_reg,rhs_reg,code = env\to_regs @lhs, @rhs
        store_code = @lhs.__location and "store#{t_lhs.base_type} #{lhs_reg}, #{@lhs.__location}\n" or ""
        lhs_true,lhs_false,use_rhs,use_false,xor_done = env\fresh_labels "xor.lhs.true","xor.lhs.false","xor.use.rhs","xor.false","xor.done"

        code ..= check_truthiness t_lhs, env, lhs_reg, lhs_true, lhs_false
        code ..= env\block lhs_true, ->
            check_truthiness t_rhs, env, rhs_reg, use_false, xor_done
        code ..= env\block lhs_false, ->
            check_truthiness t_rhs, env, rhs_reg, use_rhs, xor_done
        code ..= env\block use_rhs, ->
            "#{lhs_reg} =#{t_lhs.base_type} copy #{rhs_reg}\n"..store_code
        code ..= env\block use_false, ->
            if t_lhs\is_a(Types.Optional)
                code ..= set_nil t_lhs, env, lhs_reg
            else
                code ..= "#{lhs_reg} =l copy 0"..store_code
            code ..= "jmp #{xor_true}\n"

        code ..= "#{xor_done}\n"
        return code
    ButWithUpdate: (env)=>
        t = get_type @base
        if t\is_a(Types.ListType)
            error "Not impl"
        elseif t\is_a(Types.String)
            error "Not impl"
        elseif t\is_a(Types.StructType)
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
                code ..= "store#{memb.type.base_type} #{val_reg}, #{p}\n"

            code ..= "store#{t.base_type} #{base_reg}, #{@base.__location}\n" if @base.__location
            return code
        else
            node_error @, "| operator is only supported for List and Struct types"

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
            code ..= "store#{ret_type.base_type} #{ret}, #{dest.__location}\n"
        return code

    FnDecl: (env)=> ""
    Macro: (env)=> ""
    Pass: (env)=> ""
    Fail: (env)=>
        if @message
            node_assert get_type(@message)\is_a(Types.OptionalType(Types.String)), @message,
                "Failure messages must be a String or nil, not #{get_type @message}"
            msg,code = env\to_reg @message
            fail_label,empty_label = env\fresh_labels "failure", "empty.message"
            code ..= "jnz #{msg}, #{fail_label}, #{empty_label}\n"
            code ..= "#{empty_label}\n"
            code ..= "#{msg} =l copy #{env\get_string_reg("Unexpected failure!", "default.failure")}\n"
            code ..= "jmp #{fail_label}\n#{fail_label}\n"
            code ..= "call $dprintf(l 2, l #{env\get_string_reg(get_node_pos(@)..': %s\n', "failure.location")}, l #{msg})\n"
            code ..= "call $_exit(l 1)\n"
            return code
        else
            code = "call $dprintf(l 2, l #{env\get_string_reg(get_node_pos(@)..': A failure occurred!\n', "failure.location")})\n"
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
            node_assert ret_type == Types.Void or ret_type == Types.NilType, @, "Return value (#{ret_type}) is not being used"
        _, code = env\to_reg @, true
        code = code\gsub("[^\n]- (call [^\n]*\n)$", "%1")
        return code
    Return: (env)=>
        if @value
            reg, code = env\to_reg @value
            if get_type(@value)\is_a(Types.Void)
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
        end_label,next_label = env\fresh_labels "do.end", "do.else"
        code = ""
        for i,block in ipairs @
            for jmp in coroutine.wrap(-> each_tag(block, "Stop"))
                if not jmp.target or jmp.target[0] == "do"
                    jmp.jump_label = end_label
            for jmp in coroutine.wrap(-> each_tag(block, "Skip"))
                if not jmp.target or jmp.target[0] == "do"
                    jmp.jump_label = next_label

            code ..= env\compile_stmt(block)
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
            if i < #@
                code ..= "#{next_label}\n"
                next_label = env\fresh_label "do.else"
        code ..= "#{next_label}\n"
        code ..= "jmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return code
    If: (env)=>
        code = ""
        end_label,false_label = env\fresh_labels "if.end", "if.else"
        for cond in *@
            r,cond_code = env\to_reg cond.condition
            code ..= cond_code
            true_label = env\fresh_label "if.true"
            code ..= check_truthiness get_type(cond.condition), env, r, true_label, false_label
            code ..= "#{true_label}\n"
            code ..= env\compile_stmt cond.body
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
            code ..= "#{false_label}\n"
            false_label = env\fresh_label "if.else"
        if @elseBody
            code ..= env\compile_stmt @elseBody
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return code
    When: (env)=>
        t = get_type @what
        what_reg,code = env\to_reg @what
        end_label,next_case,next_body = env\fresh_labels "when.end","when.case","when.body"
        match_reg = env\fresh_local "when.matches"
        code ..= "jmp #{next_case}\n"
        for branch in *@
            for case in *branch.cases
                node_assert get_type(case)\is_a(t), case, "'when' value is not a #{t}"
                code ..= "#{next_case}\n"
                next_case = env\fresh_label "when.case"
                case_reg,case_code = env\to_reg case
                code ..= "#{case_code}#{match_reg} =l ceql #{what_reg}, #{case_reg}\n"
                code ..= "jnz #{match_reg}, #{next_body}, #{next_case}\n"
            code ..= "#{next_body}\n"
            next_body = env\fresh_label "when.body"
            code ..= env\compile_stmt branch.body
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
        if @elseBody
            code ..= "#{next_case}\n"
            code ..= env\compile_stmt @elseBody
            unless has_jump\match(code)
                code ..= "jmp #{end_label}\n"
        else
            code ..= "#{next_case}\n"
            code ..= "jmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return code
    Repeat: (env)=> repeat_loop(@, env)
    While: (env)=> while_loop(@, env)
    For: (env)=> for_loop(@, env)
        
compile_prog = (ast, filename)->
    env = Environment(filename)
    return env\compile_program(ast, filename)

return {:compile_prog}
