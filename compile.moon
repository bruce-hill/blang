Types = require 'typecheck'
bp = require 'bp'
import add_parenting, get_type, parse_type from Types
import log, viz, node_assert, node_error, get_node_pos, print_err from require 'util'
concat = table.concat

INT_NIL = tostring(0x7FFFFFFFFFFFFFFF)
FLOAT_NIL = INT_NIL

has_jump = bp.compile('^_("jmp"/"jnz"/"ret")\\b ..$ $$')

local stmt_compilers, expr_compilers

each_tag = (...)=>
    return unless type(@) == 'table'

    tags = {...}
    for tag in *tags
        coroutine.yield @ if @__tag == tag

    for k,v in pairs(@)
        each_tag(v, ...) if type(v) == 'table' and not (type(k) == 'string' and k\match("^__"))

get_function_reg = (scope, name, signature)->
    return nil unless scope
    switch scope.__tag
        when "Block"
            for i=#scope,1,-1
                stmt = scope[i]
                if stmt.__tag == "FnDecl" and stmt.name[0] == name
                    t = get_type(stmt)
                    if "#{t}" == signature or t\arg_signature! == signature
                        return node_assert(stmt.__register, stmt, "Function without a name"), get_type(stmt)
                elseif stmt.__tag == "Declaration" and stmt.var[0] == name
                    t = if stmt.type
                        parse_type(stmt.type)
                    else
                        get_type stmt.value
                    if t\is_a(Types.FnType) and ("#{t}" == signature or t\arg_signature! == signature)
                        return stmt.var.__register, t
        when "FnDecl","Lambda"
            for a in *scope.args
                if a.arg[0] == name
                    t = parse_type(a.type)
                    if t\is_a(Types.FnType) and ("#{t}" == signature or t\arg_signature! == signature)
                        return a.__register, t
        when "For","ListComprehension"
            iter_type = get_type(scope.iterable)
            if scope.var and scope.var[0] == name
                if iter_type\is_a(Types.ListType) and iter_type.item_type\is_a(Types.FnType)
                    return scope.var.__register, iter_type.item_type
                elseif iter_type\is_a(Types.TableType) and iter_type.value_type\is_a(Types.FnType)
                    return scope.var.__register, iter_type.value_type
            if scope.index and scope.index[0] == name
                if iter_type\is_a(Types.TableType) and iter_type.key_type\is_a(Types.FnType)
                    return scope.index.__register, iter_type.key_type

    if scope.__parent and (scope.__parent.__tag == "For" or scope.__parent.__tag == "While" or scope.__parent.__tag == "Repeat")
        loop = scope.__parent
        if scope == loop.between
            r,t = get_function_reg(loop.body, name, signature)
            return r,t if r
    
    return get_function_reg(scope.__parent, name, signature)

infixop = (env, op)=>
    assert @lhs and @rhs, "Infix node doesn't have lhs/rhs: #{viz @}"
    t = get_type @lhs
    lhs_reg, lhs_code = env\to_reg @lhs
    code = lhs_code
    ret_reg = env\fresh_local "result"
    rhs = @rhs
    rhs_type = get_type rhs
    node_assert rhs_type == t, rhs, "Expected type: #{t} but got type #{rhs_type}"
    rhs_reg, rhs_code = env\to_reg rhs
    code ..= rhs_code
    if type(op) == 'string'
        code ..= "#{ret_reg} =#{t.abi_type} #{op} #{lhs_reg}, #{rhs_reg}\n"
    else
        code ..= op(ret_reg, lhs_reg, rhs_reg)
    lhs_reg = ret_reg
    return ret_reg, code

overload_infix = (env, overload_name, regname="result")=>
    t = get_type @
    lhs_type, rhs_type = get_type(@lhs), get_type(@rhs)
    fn_reg, t2 = get_function_reg @__parent, overload_name, "(#{lhs_type},#{rhs_type})"
    node_assert fn_reg, @, "#{overload_name} is not supported for #{lhs_type} and #{rhs_type}"
    lhs_reg,code = env\to_reg @lhs
    rhs_reg,rhs_code = env\to_reg @rhs
    code ..= rhs_code
    result = env\fresh_local regname
    code ..= "#{result} =#{t.abi_type} call #{fn_reg}(#{lhs_type.abi_type} #{lhs_reg}, #{rhs_type.abi_type} #{rhs_reg})\n"
    return result, code

comparison = (env, cmp)=>
    t = get_type @lhs
    node_assert get_type(@rhs) == t, @rhs, "Expected #{t} but got #{get_type(@rhs)}"

    prev_val = nil
    lhs_reg,code = env\to_reg @lhs
    rhs_reg,rhs_code = env\to_reg @rhs
    code ..= rhs_code

    result = env\fresh_local "comparison"
    if t\is_a(Types.String)
        code ..= "#{result} =l call $strcmp(l #{lhs_reg}, l #{rhs_reg})\n"
        code ..= "#{result} =l #{cmp} 0, #{result}\n"
    else
        code ..= "#{result} =l #{cmp} #{lhs_reg}, #{rhs_reg}\n"

    return result, code

check_truthiness = (t, env, reg, truthy_label, falsey_label)->
    if t\is_a(Types.Bool)
        return "jnz #{reg}, #{truthy_label}, #{falsey_label}\n"
    elseif t\is_a(Types.Nil)
        return "jmp #{falsey_label}\n"
    elseif t\is_a(Types.OptionalType)
        if t.nonnil\is_a(Types.Bool)
            tmp = env\fresh_local "is.true"
            return "#{tmp} =l ceql #{reg}, 1\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
        elseif t.nonnil\is_a(Types.Int)
            tmp = env\fresh_local "is.nonnil"
            return "#{tmp} =l cnel #{reg}, #{INT_NIL}\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
        elseif t.nonnil\is_a(Types.Num)
            tmp = env\fresh_local "is.nonnil"
            return "#{tmp} =l cod #{reg}, d_0.0 # Test for NaN\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
        else
            return "jnz #{reg}, #{truthy_label}, #{falsey_label}\n"
    else
        return "jmp #{truthy_label}\n"

check_nil = (t, env, reg, nonnil_label, nil_label)->
    if t == Types.Nil
        return "jmp #{nil_label}\n"
    elseif not t\is_a(Types.OptionalType)
        return "jmp #{nonnil_label}\n"
    else
        if t.nonnil\is_a(Types.Bool) or t.nonnil\is_a(Types.Int)
            tmp = env\fresh_local "is.nonnil"
            return "#{tmp} =l cnel #{reg}, #{INT_NIL}\njnz #{tmp}, #{nonnil_label}, #{nil_label}\n"
        elseif t.nonnil\is_a(Types.Num)
            tmp = env\fresh_local "is.nonnil"
            return "#{tmp} =l cod #{reg}, d_0.0 # Test for NaN\njnz #{tmp}, #{nonnil_label}, #{nil_label}\n"
        else
            return "jnz #{reg}, #{nil_label}, #{nonnil_label}\n"
        return "jmp #{truthy_label}\n"

class Environment
    new: =>
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
        @dups[base_name] += 1
        name = "#{base_name}.#{@dups[base_name]}"
        assert not @used_names[name], "How is this used? #{name}"
        @used_names[name] = true
        return name

    fresh_local: (suggestion="x")=> @fresh_name("%#{suggestion}")
    fresh_global: (suggestion="g")=> @fresh_name("$#{suggestion}")
    fresh_label: (suggestion="label")=> @fresh_name("@#{suggestion}")

    get_string_reg: (str, suggestion="str")=>
        unless @strings[str]
            name = @fresh_global suggestion
            @strings[str] = name
            chunks = str\gsub('[^ !#-[^-~]', (c)->"\",b #{c\byte(1)},b\"")\gsub("\n", "\\n")
            @string_code ..= "data #{name} = {b\"#{chunks}\",b 0}\n"
        return @strings[str]

    declare_function: (fndec)=>
        args = ["#{parse_type(arg.type).abi_type} #{arg.arg.__register}" for arg in *fndec.args]
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
        @fn_code ..= "function #{ret_type\is_a(Types.Void) and "" or ret_type.abi_type.." "}"
        @fn_code ..= "#{fn_name}(#{concat args, ", "}) {\n@start\n#{body_code}"
        if ret_type\is_a(Types.Void) and not has_jump\match(@fn_code)
            @fn_code ..= "  ret\n"
        elseif not has_jump\match(@fn_code)
            @fn_code ..= "  ret 0\n"
        @fn_code ..= "}\n"

    get_tostring_fn: (t, scope)=>
        if t != Types.String
            fn = get_function_reg scope, "tostring", "(#{t})=>String"
            -- log "Getting tostring: #{t} -> #{fn}"
            return fn if fn

        if t\is_a(Types.Int)
            return "$bl_tostring_int"
        elseif t\is_a(Types.Num)
            return "$bl_tostring_float"
        elseif t\is_a(Types.Bool)
            return "$bl_tostring_bool"
        elseif t\is_a(Types.String)
            return "$bl_string"
        elseif t\is_a(Types.Range)
            return "$bl_tostring_range"

        if @tostring_funcs["#{t}"]
            return @tostring_funcs["#{t}"]

        typename = t\id_str!
        fn_name = @fresh_global "tostring.#{typename}"
        @tostring_funcs["#{t}"] = fn_name

        reg = "%#{typename\lower()}"
        code = "function l #{fn_name}(#{t.base_type} #{reg}) {\n@start\n"

        dest = @fresh_local "string"
        if t\is_a(Types.Nil)
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("nil", "nil")})\n"
        elseif t\is_a(Types.Void)
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("Void", "void")})\n"
        elseif t\is_a(Types.ListType)
            len = @fresh_local "len"
            code ..= "#{len} =l call $bl_list_len(l #{reg})\n"

            item_strs = @fresh_local "item.strings"
            code ..= "#{item_strs} =l call $gc_calloc(l 8, l #{len})\n"

            i = @fresh_local "i"
            code ..= "#{i} =l copy 0\n"

            loop_label = @fresh_label "list.loop"
            body_label = @fresh_label "list.loop.body"
            end_label = @fresh_label "list.loop.end"

            code ..= "jmp #{loop_label}\n#{loop_label}\n"
            finished = @fresh_local "list.finished"
            code ..= "#{finished} =l csgel #{i}, #{len}\n"
            code ..= "jnz #{finished}, #{end_label}, #{body_label}\n"
            code ..= "#{body_label}\n"
            item_strloc = @fresh_local "item.str.loc"
            code ..= "#{item_strloc} =l mul 8, #{i}\n"
            code ..= "#{item_strloc} =l add #{item_strs}, #{item_strloc}\n"
            code ..= "#{i} =l add #{i}, 1\n"
            
            item = @fresh_local "list.item"
            code ..= "#{item} =l call $bl_list_nth(l #{reg}, l #{i})\n"
            if t.item_type.abi_type == "d"
                item2 = @fresh_local "list.item.float"
                code ..= "#{item2} =d cast #{item}\n"
                item = item2

            item_str = @fresh_local "item.string"
            code ..= "#{item_str} =l call #{@get_tostring_fn t.item_type, scope}(#{t.item_type.base_type} #{item})\n"

            code ..= "storel #{item_str}, #{item_strloc}\n"
            code ..= "jmp #{loop_label}\n#{end_label}\n"

            chunks = @fresh_local "chunks"
            chunk = @fresh_local "chunk"
            code ..= "#{chunks} =l alloc8 #{8*3}\n"
            code ..= "#{chunk} =l add #{chunks}, #{0*8}\n"
            code ..= "storel #{@get_string_reg("[","sqbracket.open")}, #{chunk}\n"
            content_str = @fresh_local "list.content.str"
            code ..= "#{content_str} =l call $bl_string_join(l #{len}, l #{item_strs}, l #{@get_string_reg(", ", "comma.space")})\n"
            code ..= "call $gc_free(l #{item_strs})\n"
            code ..= "#{chunk} =l add #{chunks}, #{1*8}\n"
            code ..= "storel #{content_str}, #{chunk}\n"
            code ..= "#{chunk} =l add #{chunks}, #{2*8}\n"
            code ..= "storel #{@get_string_reg("]","sqbracket.close")}, #{chunk}\n"
            code ..= "#{dest} =l call $bl_string_join(l 3, l #{chunks}, l 0)\n"
        elseif t\is_a(Types.TableType)
            len = @fresh_local "len"
            code ..= "#{len} =l call $hashmap_length(l #{reg})\n"

            entry_strs = @fresh_local "entry.strings"
            code ..= "#{entry_strs} =l call $gc_calloc(l 8, l #{len})\n"
            chunk_ptr = @fresh_local "chunk.ptr"
            code ..= "#{chunk_ptr} =l copy #{entry_strs}\n"

            key = @fresh_local "key.raw"
            code ..= "#{key} =l copy 0\n"

            loop_label = @fresh_label "table.loop"
            body_label = @fresh_label "table.loop.body"
            end_label = @fresh_label "table.loop.end"

            code ..= "jmp #{loop_label}\n#{loop_label}\n"

            code ..= "#{key} =l call $hashmap_next(l #{reg}, l #{key})\n"
            code ..= "jnz #{key}, #{body_label}, #{end_label}\n"
            code ..= "#{body_label}\n"

            entry_chunks = @fresh_local "entry.chunks"
            code ..= "#{entry_chunks} =l alloc8 #{3*8}\n"
            p = @fresh_local "p"
            code ..= "#{p} =l copy #{entry_chunks}\n"

            key_reg = if t.key_type\is_a(Types.Int) or t.key_type\is_a(Types.Bool)
                tmp = @fresh_local "key.int"
                code ..= "#{tmp} =l xor #{key}, #{INT_NIL}\n"
                tmp
            elseif t.key_type\is_a(Types.Num)
                bits = @fresh_local "key.bits"
                code ..= "#{bits} =l xor #{key}, #{FLOAT_NIL}\n"
                tmp2 = @fresh_local "key.float"
                code ..= "#{tmp2} =d cast #{bits}\n"
                tmp2
            else
                key
            
            key_str = @fresh_local "key.string"
            code ..= "#{key_str} =l call #{@get_tostring_fn t.key_type, scope}(#{t.key_type.base_type} #{key_reg})\n"
            code ..= "storel #{key_str}, #{p}\n"
            code ..= "#{p} =l add #{p}, 8\n"

            code ..= "storel #{@get_string_reg "=", "equals"}, #{p}\n"
            code ..= "#{p} =l add #{p}, 8\n"

            value_raw = @fresh_local "value.raw"
            code ..= "#{value_raw} =l call $hashmap_get(l #{reg}, l #{key})\n"
            value_reg = if t.value_type\is_a(Types.Int) or t.value_type\is_a(Types.Bool)
                tmp = @fresh_local "value.int"
                code ..= "#{tmp} =l xor #{value_raw}, #{INT_NIL}\n"
                tmp
            elseif t.value_type\is_a(Types.Num)
                bits = @fresh_local "value.bits"
                code ..= "#{bits} =l xor #{value_raw}, #{FLOAT_NIL}\n"
                tmp2 = @fresh_local "key.float"
                code ..= "#{tmp2} =d cast #{bits}\n"
                tmp2
            else
                value_raw
            
            value_str = @fresh_local "value.string"
            code ..= "#{value_str} =l call #{@get_tostring_fn t.value_type, scope}(#{t.value_type.base_type} #{value_reg})\n"
            code ..= "storel #{value_str}, #{p}\n"

            entry_str = @fresh_local "entry.str"
            code ..= "#{entry_str} =l call $bl_string_join(l 3, l #{entry_chunks}, l 0)\n"
            code ..= "storel #{entry_str}, #{chunk_ptr}\n"
            code ..= "#{chunk_ptr} =l add #{chunk_ptr}, 8\n"

            code ..= "jmp #{loop_label}\n#{end_label}\n"

            chunks = @fresh_local "chunks"
            chunk = @fresh_local "chunk"
            code ..= "#{chunks} =l alloc8 #{8*3}\n"
            code ..= "#{chunk} =l add #{chunks}, #{0*8}\n"
            code ..= "storel #{@get_string_reg("{","curly.open")}, #{chunk}\n"
            content_str = @fresh_local "table.content.str"
            code ..= "#{content_str} =l call $bl_string_join(l #{len}, l #{entry_strs}, l #{@get_string_reg(", ", "comma.space")})\n"
            code ..= "call $gc_free(l #{entry_strs})\n"
            code ..= "#{chunk} =l add #{chunks}, #{1*8}\n"
            code ..= "storel #{content_str}, #{chunk}\n"
            code ..= "#{chunk} =l add #{chunks}, #{2*8}\n"
            code ..= "storel #{@get_string_reg("}","curly.close")}, #{chunk}\n"
            code ..= "#{dest} =l call $bl_string_join(l 3, l #{chunks}, l 0)\n"
        elseif t\is_a(Types.StructType)
            chunks = @fresh_local "chunks"
            code ..= "#{chunks} =l alloc8 #{8*#t.members}\n"

            for i,mem in ipairs t.members
                member_loc = @fresh_local "#{t\id_str!\lower!}.#{mem.name}.loc"
                code ..= "#{member_loc} =l add #{reg}, #{8*(i-1)}\n"
                member_reg = @fresh_local "#{t\id_str!\lower!}.#{mem.name}"
                code ..= "#{member_reg} =#{mem.type.base_type} load#{mem.type.base_type} #{member_loc}\n"

                member_str = @fresh_local "#{t\id_str!\lower!}.#{mem.name}.string"
                code ..= "#{member_str} =l call #{@get_tostring_fn mem.type, scope}(#{mem.type.base_type} #{member_reg})\n"

                if mem.name
                    code ..= "#{member_str} =l call $bl_string_append_string(l #{@get_string_reg("#{mem.name}=")}, l #{member_str})\n"
                chunk_loc = @fresh_local "string.chunk.loc"
                code ..= "#{chunk_loc} =l add #{chunks}, #{8*(i-1)}\n"
                code ..= "storel #{member_str}, #{chunk_loc}\n"

            final_chunks = @fresh_local "surrounding.chunks"
            code ..= "#{final_chunks} =l alloc8 #{8*3}\n"
            chunk_loc = @fresh_local "chunk.loc"
            code ..= "#{chunk_loc} =l add #{final_chunks}, #{8*0}\n"
            if t.name\match "^Tuple%.[0-9]+$"
                code ..= "storel #{@get_string_reg("{", "curly")}, #{chunk_loc}\n"
            else
                code ..= "storel #{@get_string_reg("#{t.name}{", "#{t\id_str!}.name")}, #{chunk_loc}\n"
            content = @fresh_local "struct.content"
            code ..= "#{content} =l call $bl_string_join(l #{#t.members}, l #{chunks}, l #{@get_string_reg(", ", "comma.space")})\n"
            code ..= "#{chunk_loc} =l add #{final_chunks}, #{8*1}\n"
            code ..= "storel #{content}, #{chunk_loc}\n"
            code ..= "#{chunk_loc} =l add #{final_chunks}, #{8*2}\n"
            code ..= "storel #{@get_string_reg("}","closecurly")}, #{chunk_loc}\n"
            code ..= "#{dest} =l call $bl_string_join(l 3, l #{final_chunks}, l 0)\n"
        elseif t\is_a(Types.FnType)
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("#{t}")})\n"
        elseif t\is_a(Types.OptionalType)
            nil_label = @fresh_label "optional.nil"
            nonnil_label = @fresh_label "optional.nonnil"
            end_label = @fresh_label "optional.end"
            code ..= check_truthiness t, @, reg, nonnil_label, nil_label
            code ..= "#{nil_label}\n"
            code ..= "#{dest} =l call $bl_string(l #{@get_string_reg("nil", "nil")})\n"
            code ..= "jmp #{end_label}\n"
            code ..= "#{nonnil_label}\n"
            code ..= "#{dest} =l call #{@get_tostring_fn t.nonnil, scope}(#{t.nonnil.base_type} #{reg})\n"
            code ..= "jmp #{end_label}\n"
            code ..= "#{end_label}\n"
        else
            error "Unsupported concat type: #{t}"

        code ..= "ret #{dest}\n"
        code ..= "}\n"
        code = code\gsub("[^\n]+", =>((@\match("^[@}]") or @\match("^function")) and @ or "  "..@))
        @fn_code ..= code

        return fn_name

    to_reg: (node, ...)=>
        if not node.__tag
            error "WTF: #{viz node}"
            return @to_reg node[1], ...
        node_assert expr_compilers[node.__tag], node, "Expression compiler not implemented for #{node.__tag}"
        return expr_compilers[node.__tag](node, @, ...)

    compile_stmt: (node)=>
        if not node.__tag
            error "WTF: #{viz node}"
            return @compile_stmt node[1]
        node_assert stmt_compilers[node.__tag], node, "Not implemented: #{node.__tag}"
        return stmt_compilers[node.__tag](node, @)

    compile_program: (ast, filename)=>
        add_parenting(ast)

        @type_code = "type :Range = {l,l,l}\n"
        declared_structs = {}
        for s in coroutine.wrap(-> each_tag(ast, "StructType", "Struct"))
            t = if s.__tag == "StructType" then parse_type(s)
            else get_type(s)

            if declared_structs[t.name]
                node_assert declared_structs[t.name] == t, s, "Struct declaration shadows"
                continue
            declared_structs[t.name] = t
            @type_code ..= "type :#{t.name} = {#{concat [m.type.base_type for m in *t.members], ","}}\n"

        @used_names["%__argc"] = true
        @used_names["%argc"] = true
        @used_names["%__argv"] = true
        @used_names["%argv"] = true
        for v in coroutine.wrap(-> each_tag(ast, "Var"))
            if v[0] == "argc"
                v.__register = "%argc"
            elseif v[0] == "argv"
                v.__register = "%argv"

        -- Set up variable registers:
        hook_up_refs = (var, scope, arg_signature)->
            assert var.__tag == "Var" and scope and scope != var
            var.__register or= @fresh_local var[0]
            -- log "Hook up #{var} in #{viz scope}"
            assert scope.__tag != "Var"
            for k,node in pairs scope
                continue unless type(node) == 'table' and not (type(k) == 'string' and k\match("^__"))
                switch node.__tag
                    when "Var"
                        if node[0] == var[0]
                            node_assert not node.__register, var, "Variable shadows earlier declaration #{node.__decl}"
                            node.__register = var.__register
                            node.__decl = var
                    when "FnDecl","Lambda"
                        hook_up_refs var, node.body, arg_signature if var.__register\match("^%$")
                    when "FnCall","MethodCall"
                        call_sig = "(#{concat [tostring(get_type(a)) for a in *node], ","})"
                        if not arg_signature or call_sig == arg_signature
                            hook_up_refs var, {node.fn}, arg_signature
                            assert node.fn[0] != var[0] or node.fn.__register, "WTF"
                        hook_up_refs var, {table.unpack(node)}, arg_signature
                    else
                        hook_up_refs var, node, arg_signature

        -- Set up function names (global):
        for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl", "Lambda"))
            fndec.__register = @fresh_global(fndec.name and fndec.name[0] or "lambda")
            fndec.__decl = fndec
            if fndec.name
                fndec.name.__register = fndec.__register
                fndec.name.__decl = fndec
                hook_up_refs fndec.name, fndec.__parent, get_type(fndec)\arg_signature!
                    
        for fn in coroutine.wrap(-> each_tag(ast, "FnDecl", "Lambda"))
            for a in *fn.args
                hook_up_refs a.arg, fn.body

        for vardec in coroutine.wrap(-> each_tag(ast, "Declaration"))
            scope = if vardec.__parent.__tag == "Block"
                i = 1
                while vardec.__parent[i] != vardec
                    i += 1
                {table.unpack(vardec.__parent, i+1)}
            else vardec.__parent
            hook_up_refs vardec.var, scope

            block = vardec.__parent
            loop = block and block.__parent
            while loop and not loop.__tag
                loop = loop.__parent
            if loop and (loop.__tag == "For" or loop.__tag == "While" or loop.__tag == "Repeat")
                if block == loop.body and loop.between
                    hook_up_refs vardec.var, loop.between

        for for_block in coroutine.wrap(-> each_tag(ast, "For"))
            if for_block.var
                hook_up_refs for_block.var, for_block.body
                hook_up_refs for_block.var, for_block.between if for_block.between
            if for_block.index
                hook_up_refs for_block.index, for_block.body
                hook_up_refs for_block.index, for_block.between if for_block.between

        for comp in coroutine.wrap(-> each_tag(ast, "ListComprehension"))
            if comp.index
                hook_up_refs comp.index, {comp.expression}
                hook_up_refs comp.index, {comp.condition} if comp.condition
            if comp.var
                hook_up_refs comp.var, {comp.expression}
                hook_up_refs comp.var, {comp.condition} if comp.condition

        -- Compile functions:
        for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl", "Lambda"))
            @declare_function fndec

        body_code = @compile_stmt(ast)\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))

        code = "# Source file: #{filename}\n\n"
        code ..= "#{@type_code}\n" if #@type_code > 0
        code ..= "#{@string_code}\n" if #@string_code > 0
        code ..= "#{@fn_code}\n" if #@fn_code > 0
        code ..= "export function w $main(w %__argc, l %__argv) {\n"
        code ..= "@start\n"
        code ..= "  %argc =l extsw %__argc\n"
        code ..= "  %argv =l call $bl_list_new(l %argc, l %__argv)\n"
        code ..= body_code
        code ..= "  ret 0\n}\n"
        return code

expr_compilers =
    Var: (env)=>
        node_assert @__register, @, "This variable is not defined"
        return @__register, ""
    Global: (env)=>
        return "#{@[0]}", ""
    Int: (env)=>
        s = @[0]\gsub("_","")
        if s\match("^0x")
            return "#{tonumber(s\sub(3), 16)}",""
        else
            return "#{tonumber(s)}",""
    Float: (env)=>
        s = @[0]\gsub("_","")
        return "d_#{tonumber(s)}",""
    Nil: (env)=>
        -- Figure out what kind of nil this is, since different types have different binary
        -- representations of nil (Int -> INT_MAX, Float -> NaN, otherwise -> 0)
        values_for = (nonnil)->
            if nonnil\is_a(Types.Int) or nonnil\is_a(Types.Bool)
                return "#{INT_NIL}",""
            elseif nonnil\is_a(Types.Num) or nonnil.base_type == "d"
                return "#{FLOAT_NIL}",""
            else
                return "0",""

        child = @
        parent = @__parent
        while parent
            if parent.__tag == "Return"
                while parent and not (parent.__tag == "FnDecl" or parent.__tag == "Lambda")
                    parent,child = parent.__parent,parent
                continue

            if parent.__tag == "Equal" or parent.__tag == "NotEqual"
                other = (child == parent.lhs) and parent.rhs or parent.lhs
                t = get_type(other)
                if t\is_a(Types.OptionalType) and t != Types.Nil
                    t = t.nonnil
                return values_for(t)

            t = if parent.__tag == "Declaration" and parent.type
                parse_type parent.type
            elseif parent.__tag == "FnDecl" or parent.__tag == "Lambda" or parent.__tag == "Declaration"
                break
            else
                get_type(parent)

            if t != Types.Nil and t\is_a(Types.OptionalType)
                return values_for(t.nonnil)

            parent,child = parent.__parent,parent
        return "0",""
    Bool: (env)=> (@[0] == "yes" and "1" or "0"),""
    Cast: (env)=>
        reg,code = env\to_reg @expr
        t = parse_type @type
        actual_type = get_type(@expr)
        if actual_type and t.abi_type == actual_type.abi_type
            return reg,code
        c = env\fresh_local "casted"
        code ..= "#{c} =#{t.abi_type} cast #{reg}\n"
        return c,code
    String: (env)=>
        return env\get_string_reg(@content[0]),"" if #@content == 0

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

        chunks_reg = env\fresh_local "string.chunks"
        code = "#{chunks_reg} =l alloc8 #{8*#chunks}\n"
        chunk_loc = env\fresh_local "string.chunk.loc"
        for i,chunk in ipairs chunks
            code ..= "#{chunk_loc} =l add #{chunks_reg}, #{(i-1)*8}\n"
            if type(chunk) == 'string'
                code ..= "storel #{env\get_string_reg chunk, "str"}, #{chunk_loc}\n"
            else
                t = get_type(chunk)
                val_reg,val_code = env\to_reg chunk
                code ..= val_code
                interp_reg = if t == Types.String
                    val_reg
                else
                    fn_name = env\get_tostring_fn t, @
                    interp_reg = env\fresh_local "string.interp"
                    code ..= "#{interp_reg} =l call #{fn_name}(#{t.base_type} #{val_reg})\n"
                    interp_reg
                code ..= "storel #{interp_reg}, #{chunk_loc}\n"
                
        str = env\fresh_local "str"
        code ..= "#{str} =l call $bl_string_join(l #{#chunks}, l #{chunks_reg}, l 0)\n"
        return str,code

    DSL: (env)=>
        content = @string.content
        return env\get_string_reg(content[0]),"" if #content == 0
        str = env\fresh_local "str"
        code = "#{str} =l call $bl_string(l #{env\get_string_reg("", "emptystr")})\n"
        dsl_type = get_type(@)

        stringify = (val)->
            t = get_type(val)
            val_reg,val_code = env\to_reg val
            code ..= val_code
            safe = if t == dsl_type
                val_reg
            else
                fn_reg = get_function_reg @__parent, "escape", "(#{t})=>#{dsl_type}"
                node_assert fn_reg, val, "No escape(#{t})=>#{dsl_type} function is implemented, so this value cannot be safely inserted"
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
        if t\is_a(Types.Int) or t\is_a(Types.Num)
            reg,code = env\to_reg @value
            ret = env\fresh_local "neg"
            return ret, "#{code}#{ret} =#{t.abi_type} neg #{reg}\n"
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
            return len, "#{code}#{len} =l call $bl_list_len(l #{list})\n"
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
        node_assert get_type(@value)\is_a(Types.Bool), @value, "Expected a Bool"
        b,code = env\to_reg @value
        ret = env\fresh_local "not"
        code ..= "#{ret} =l ceql #{b}, 0\n"
        return ret, code
    IndexedTerm: (env)=>
        t = get_type @value
        is_optional = t\is_a(Types.OptionalType) and t != Types.Nil
        t = t.nonnil if is_optional
        nil_guard = (check_reg, output_reg, get_nonnil_code)->
            unless is_optional
                return get_nonnil_code!

            ifnil,ifnonnil,done = env\fresh_label("if.nil"), env\fresh_label("if.nonnil"), env\fresh_label("if.nil.done")
            code = check_truthiness get_type(@value), env, check_reg, ifnonnil, ifnil
            code ..= "#{ifnonnil}\n"
            code ..= get_nonnil_code!
            code ..= "jmp #{done}\n"
            code ..= "#{ifnil}\n"
            if t\is_a(Types.Int) or t\is_a(Types.Bool)
                code ..= "#{output_reg} =l copy #{INT_NIL}\n"
            elseif t\is_a(Types.Num) or t.base_type == "d"
                code ..= "#{output_reg} =d copy #{FLOAT_NIL}\n"
            else
                code ..= "#{output_reg} =l copy 0\n"
            code ..= "jmp #{done}\n"
            code ..= "#{done}\n"
            return code
            
        if t\is_a(Types.ListType)
            item_type = t.item_type
            index_type = get_type(@index)
            list_reg,list_code = env\to_reg @value
            index_reg,index_code = env\to_reg @index
            code = list_code..index_code
            if index_type\is_a(Types.Int)
                item = env\fresh_local "list.item"
                code ..= nil_guard list_reg, item, ->
                    if t.item_type.base_type == "d"
                        tmp = env\fresh_local "list.item.as_int"
                        code = "#{tmp} =l call $bl_list_nth(l #{list_reg}, l #{index_reg})\n"
                        return code.."#{item} =d cast #{tmp}\n"
                    else
                        return "#{item} =l call $bl_list_nth(l #{list_reg}, l #{index_reg})\n"
                return item,code
            elseif index_type\is_a(Types.Range)
                slice = env\fresh_local "slice"
                code ..= nil_guard list_reg, slice, ->
                    "#{slice} =l call $bl_list_slice_range(l #{list_reg}, l #{index_reg})\n"
                return slice,code
            else
                node_error @index, "Index is #{index_type} instead of Int or Range"
        elseif t\is_a(Types.TableType)
            tab_reg,code = env\to_reg @value
            index_reg,index_code = env\to_reg @index
            code ..= index_code
            value_reg = env\fresh_local "value"
            code ..= nil_guard tab_reg, value_reg, ->
                code = ""
                key_getter = env\fresh_local "key.getter"
                if t.key_type\is_a(Types.Int) or t.key_type\is_a(Types.Bool)
                    code ..= "#{key_getter} =l xor #{index_reg}, #{INT_NIL}\n"
                elseif t.key_type\is_a(Types.Num)
                    code ..= "#{key_getter} =l cast #{index_reg}\n"
                    code ..= "#{key_getter} =l xor #{key_getter}, #{INT_NIL}\n"
                else
                    code ..= "#{key_getter} =l copy #{index_reg}\n"

                raw_value = env\fresh_local "value.raw"
                code ..= "#{raw_value} =l call $hashmap_get(l #{tab_reg}, l #{key_getter})\n"

                if t.value_type\is_a(Types.Int) or t.value_type\is_a(Types.Bool)
                    code ..= "#{value_reg} =l xor #{raw_value}, #{INT_NIL}\n"
                elseif t.value_type\is_a(Types.Num)
                    bits = @fresh_local "value.bits"
                    code ..= "#{bits} =l xor #{raw_value}, #{FLOAT_NIL}\n"
                    code ..= "#{value_reg} =d cast #{bits}\n"
                else
                    code ..= "#{value_reg} =l copy #{raw_value}\n"
                return code

            return value_reg,code
        elseif t\is_a(Types.StructType)
            i,member_type = if @index.__tag == "FieldName"
                member_name = @index[0]
                node_assert t.members_by_name[member_name], @index, "Not a valid struct member of #{t}"
                t.members_by_name[member_name].index, t.members_by_name[member_name].type
            elseif @index.__tag == "Int"
                i = tonumber(@index[0])
                node_assert 1 <= i and i <= #t.members, @index, "#{t} only has members between 1 and #{#t.members}"
                i, t.members[i].type
            else
                node_error @index, "Structs can only be indexed by a field name or Int literal"
            struct_reg,code = env\to_reg @value
            ret = env\fresh_local "member"
            code ..= nil_guard struct_reg, ret, ->
                loc = env\fresh_local "member.loc"
                code = "#{loc} =l add #{struct_reg}, #{8*(i-1)}\n"
                return code.."#{ret} =#{member_type.abi_type} load#{member_type.base_type} #{loc}\n"
            return ret,code
        elseif t\is_a(Types.Range)
            index_type = get_type(@index)
            -- TODO: Slice ranges
            node_assert index_type\is_a(Types.Int), @index, "Index is #{index_type} instead of Int"
            range_reg,code = env\to_reg @value
            index_reg,index_code = env\to_reg @index
            code ..= index_code
            ret = env\fresh_local "range.nth"
            code ..= nil_guard range_reg, ret, ->
                "#{ret} =l call $range_nth(l #{range_reg}, l #{index_reg})\n"
            return ret, code
        elseif t\is_a(Types.String)
            index_type = get_type(@index)
            str,code = env\to_reg @value
            index_reg,index_code = env\to_reg @index
            code ..= index_code
            if index_type\is_a(Types.Int) -- Get nth character as an Int
                char = env\fresh_local "char"
                code ..= nil_guard str, char, -> "#{char} =l call $bl_string_nth_char(l #{str}, l #{index_reg})\n"
                return char, code
            elseif index_type\is_a(Types.Range) -- Get a slice of the string
                slice = env\fresh_local "slice"
                code ..= nil_guard str, slice, -> "#{slice} =l call $bl_string_slice(l #{str}, l #{index_reg})\n"
                return slice, code
            else
                node_error @index, "Index is #{index_type} instead of Int or Range"
        else
            node_error @value, "Indexing is not valid on type #{t}"
    List: (env)=>
        if #@ == 0
            list = env\fresh_local "list.empty"
            code = "#{list} =l call $bl_list_new(l 0, l 0)\n"
            return list, code

        buf = env\fresh_local "list.buf"
        code = "#{buf} =l alloc8 #{8*#@}\n"
        for i,val in ipairs @
            val_reg,val_code = env\to_reg val
            code ..= val_code
            t = get_type val
            if t.base_type == "d"
                val_i = env\fresh_local "item.int"
                code ..= "#{val_i} =l cast #{val_reg}\n"
                val_reg = val_i
            ptr = env\fresh_local "list.item.ptr"
            code ..= "#{ptr} =l add #{buf}, #{8*(i-1)}\n"
            code ..= "storel #{val_reg}, #{ptr}\n"
        list = env\fresh_local "list"
        code ..= "#{list} =l call $bl_list_new(l #{#@}, l #{buf})\n"
        return list, code
    ListComprehension: (env)=>
        -- Rough breakdown:
        -- comp = empty_list()
        -- len = #iter
        -- i = 0
        -- jmp @comprehension.next
        -- @comprehension.body
        -- item = list[i]
        -- // conditional
        -- jnz cond, @comprehension.include, @comprehension.next
        -- @comprehension.include
        -- expr = ...item...
        -- comp = list_append(comp, expr)
        -- jmp @comprehension.next
        -- @comprehension.next
        -- i += 1
        -- jnz (i <= len), @comprehension.end, @comprehension.body
        -- @comprehension.end
        -- TODO: optimize allocation spam
        comprehension = env\fresh_local "comprehension"
        code = "#{comprehension} =l call $bl_list_new(l 0, l 0)\n"

        iter_type = get_type @iterable

        body_label = env\fresh_label "comprehension.body"
        include_label = env\fresh_label "comprehension.include"
        next_label = env\fresh_label "comprehension.next"
        end_label = env\fresh_label "comprehension.end"

        i = env\fresh_local "i"
        len = env\fresh_local "len"

        iter_reg,iter_code = env\to_reg @iterable
        code ..= iter_code
        code ..= "#{i} =l copy 0\n"
        if iter_type\is_a(Types.Range)
            code ..= "#{len} =l call $range_len(l #{iter_reg})\n"
        elseif iter_type\is_a(Types.ListType)
            code ..= "#{len} =l call $bl_list_len(l #{iter_reg})\n"
        else
            node_error @iterable, "Expected a list or a range, not #{iter_type}"
        code ..= "jmp #{next_label}\n"
        code ..= "#{body_label}\n"
        if @index
            index_reg = @index.__register
            env.used_names[index_reg] = true
            code ..= "#{index_reg} =l copy #{i}\n"
        if @var
            var_reg = @var.__register
            env.used_names[var_reg] = true
            if iter_type\is_a(Types.Range)
                code ..= "#{var_reg} =l call $range_nth(l #{iter_reg}, l #{i})\n"
            else
                if iter_type.item_type.base_type == "d"
                    tmp = env\fresh_local "item.int"
                    code ..= "#{tmp} =l call $bl_list_nth(l #{iter_reg}, l #{i})\n"
                    code ..= "#{var_reg} =#{iter_type.item_type.abi_type} cast #{tmp}\n"
                else
                    code ..= "#{var_reg} =#{iter_type.item_type.abi_type} call $bl_list_nth(l #{iter_reg}, l #{i})\n"

        if @condition
            cond_reg,cond_code = env\to_reg @condition
            code ..= cond_code
            if @control and @control.__tag == "Skip"
                code ..= "jnz #{cond_reg}, #{next_label}, #{include_label}\n"
            elseif @control and @control.__tag == "Stop"
                code ..= "jnz #{cond_reg}, #{end_label}, #{include_label}\n"
            else
                code ..= "jnz #{cond_reg}, #{include_label}, #{next_label}\n"
        else
            code ..= "jmp #{include_label}\n"

        code ..= "#{include_label}\n"
        expr_reg,expr_code = env\to_reg @expression
        code ..= expr_code
        expr_i = env\fresh_local "comprehension.expr.int"
        if get_type(@expression).base_type != "l"
            code ..= "#{expr_i} =l cast #{expr_reg}\n"
        else
            expr_i = expr_reg
        code ..= "call $bl_list_append(l #{comprehension}, l #{expr_i})\n"
        code ..= "jmp #{next_label}\n"
        code ..= "#{next_label}\n"
        code ..= "#{i} =l add #{i}, 1\n"
        is_finished = env\fresh_local "comprehension.is_finished"
        code ..= "#{is_finished} =l csgtl #{i}, #{len}\n"
        code ..= "jnz #{is_finished}, #{end_label}, #{body_label}\n"
        code ..= "#{end_label}\n"
        return comprehension, code
    Table: (env)=>
        t = get_type @
        node_assert not t.key_type\is_a(Types.OptionalType) and not t.value_type\is_a(Types.OptionalType), @,
            "Nil cannot be stored in a table, but this table is #{t}"

        tab = env\fresh_local "table.empty"
        code = "#{tab} =l call $gc_hashmap_new(l 0)\n"

        if #@ == 0
            return tab, code

        convert_nils = (t2, src_reg, dest_reg)->
            if t2\is_a(Types.Int) or t2\is_a(Types.Bool)
                code ..= "#{dest_reg} =l xor #{src_reg}, #{INT_NIL}\n"
            elseif t2\is_a(Types.Num)
                code ..= "#{dest_reg} =d cast #{src_reg}\n"
                code ..= "#{dest_reg} =l xor #{dest_reg}, #{FLOAT_NIL}\n"
            else
                code ..= "#{dest_reg} =l copy #{src_reg}\n"

        for entry in *@
            key_reg,key_code = env\to_reg entry.key
            code ..= key_code
            value_reg,value_code = env\to_reg entry.value
            code ..= key_code

            key_setter = env\fresh_local "key.setter"
            convert_nils t.key_type, key_reg, key_setter
            value_setter = env\fresh_local "value.setter"
            convert_nils t.value_type, value_reg, value_setter
            code ..= "call $hashmap_set(l #{tab}, l #{key_setter}, l #{value_setter})\n"
        return tab, code
    Range: (env)=>
        range = env\fresh_local "range"
        local code
        if @first and @next and @last
            first_reg,code = env\to_reg @first
            next_reg,next_code = env\to_reg @next
            code ..= next_code
            last_reg,last_code = env\to_reg @last
            code ..= last_code
            code ..= "#{range} =l call $range_new(l #{first_reg}, l #{next_reg}, l #{last_reg})\n"
        elseif @first and @next and not @last
            first_reg,code = env\to_reg @first
            next_reg,next_code = env\to_reg @next
            code ..= next_code
            code ..= "#{range} =l call $range_new_first_next(l #{first_reg}, l #{next_reg})\n"
        elseif @first and not @next and @last
            first_reg,code = env\to_reg @first
            last_reg,last_code = env\to_reg @last
            code ..= last_code
            code ..= "#{range} =l call $range_new_first_last(l #{first_reg}, l #{last_reg})\n"
        elseif @first and not @next and not @last
            first_reg,code = env\to_reg @first
            code ..= "#{range} =l call $range_new_first_last(l #{first_reg}, l 999999999999999999)\n"
        elseif not @first and not @next and @last
            last_reg,code = env\to_reg @last
            code = "#{range} =l call $range_new_first_last(l -999999999999999999, l #{last_reg})\n"
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
    Add: (env)=>
        t_lhs,t_rhs = get_type(@lhs),get_type(@rhs)
        if t_lhs == t_rhs and (t_lhs\is_a(Types.Int) or t_lhs\is_a(Types.Num))
            return infixop @, env, "add"
        elseif t_lhs == t_rhs and t_lhs\is_a(Types.String)
            return infixop @, env, (ret,lhs,rhs)->
                "#{ret} =l call $bl_string_append_string(l #{lhs}, l #{rhs})\n"
        elseif t_lhs == t_rhs and t_lhs\is_a(Types.ListType)
            return infixop @, env, (ret,lhs,rhs)->
                "#{ret} =l call $bl_list_concat(l #{lhs}, l #{rhs})\n"
        else
            return overload_infix @, env, "add", "sum"

    Sub: (env)=>
        t_lhs,t_rhs = get_type(@lhs),get_type(@rhs)
        if t_lhs == t_rhs and (t_lhs\is_a(Types.Int) or t_lhs\is_a(Types.Num))
            return infixop @, env, "sub"
        else
            return overload_infix @, env, "subtract", "difference"
    Mul: (env)=>
        t_lhs,t_rhs = get_type(@lhs),get_type(@rhs)
        if t_lhs == t_rhs and (t_lhs\is_a(Types.Int) or t_lhs\is_a(Types.Num))
            return infixop @, env, "mul"
        else
            return overload_infix @, env, "multiply", "product"
    Div: (env)=>
        t_lhs,t_rhs = get_type(@lhs),get_type(@rhs)
        if t_lhs == t_rhs and (t_lhs\is_a(Types.Int) or t_lhs\is_a(Types.Num))
            return infixop @, env, "div"
        else
            return overload_infix @, env, "divide", "quotient"
    Mod: (env)=>
        t = get_type(@)
        if t\is_a(Types.Int) or t\is_a(Types.Num)
            lhs_reg,code = env\to_reg @lhs
            rhs_reg,rhs_code = env\to_reg @rhs
            code ..= rhs_code
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
        base_reg, base_code = env\to_reg @base
        exponent_reg, exponent_code = env\to_reg @exponent
        ret_reg = env\fresh_local "result"
        if base_type == exponent_type and base_type\is_a(Types.Int)
            return ret_reg, "#{base_code}#{exponent_code}#{ret_reg} =l call $ipow(l #{base_reg}, l #{exponent_reg})\n"
        elseif base_type == exponent_type and base_type\is_a(Types.Num)
            return ret_reg, "#{base_code}#{exponent_code}#{ret_reg} =d call $pow(d #{base_reg}, d #{exponent_reg})\n"
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
            struct_size = 8*#t.members
            code ..= "#{ret} =l alloc8 #{struct_size}\n"
            code ..= "call $memcpy(l #{ret}, l #{lhs_reg}, l #{struct_size})\n"
            p = env\fresh_local "#{t.name\lower!}.butwith.member.loc"
            used = {}
            for override in *@
                i = if override.index
                    tonumber(override.index[0])
                elseif override.field
                    t.members_by_name[override.field[0]].index
                else
                    node_error override, "I don't know what this is"

                node_assert not used[i], override, "Redundant value, this field is already being overwritten"
                used[i] = true

                node_assert 1 <= i and i <= #t.members, override, "Not a valid member of #{t}"
                node_assert get_type(override.value)\is_a(t.members[i].type), override.value, "Not a #{t.members[i].type}"
                val_reg,val_code = env\to_reg override.value
                code ..= val_code
                code ..= "#{p} =l add #{ret}, #{8*(i-1)}\n"
                code ..= "store#{t.members[i].type.base_type} #{val_reg}, #{p}\n"

            code ..= "#{ret} =l call $intern_bytes(l #{ret}, l #{struct_size})\n"
            return ret, code
        else
            node_error @, "| operator is only supported for List and Struct types"
    Less: (env)=>
        t = get_type(@lhs)
        if t\is_a(Types.Int) or t\is_a(Types.String)
            return comparison @, env, "csltl"
        elseif t\is_a(Types.Num)
            return comparison @, env, "cltd"
        else node_error @, "Comparison is not supported for #{t}"
    LessEq: (env)=>
        t = get_type(@lhs)
        if t\is_a(Types.Int) or t\is_a(Types.String)
            return comparison @, env, "cslel"
        elseif t\is_a(Types.Num)
            return comparison @, env, "cled"
        else node_error @, "Comparison is not supported for #{t}"
    Greater: (env)=>
        t = get_type(@lhs)
        if t\is_a(Types.Int) or t\is_a(Types.String)
            return comparison @, env, "csgtl"
        elseif t\is_a(Types.Num)
            return comparison @, env, "cgtd"
        else node_error @, "Comparison is not supported for #{t}"
    GreaterEq: (env)=>
        t = get_type(@lhs)
        if t\is_a(Types.Int) or t\is_a(Types.String)
            return comparison @, env, "csgel"
        elseif t\is_a(Types.Num)
            return comparison @, env, "cged"
        else node_error @, "Comparison is not supported for #{t}"
    Equal: (env)=>
        lhs_type, rhs_type = get_type(@lhs), get_type(@rhs)
        if lhs_type\is_a(rhs_type) or rhs_type\is_a(lhs_type)
            lhs_reg,lhs_code = env\to_reg @lhs
            rhs_reg,rhs_code = env\to_reg @rhs
            result = env\fresh_local "comparison"
            code = lhs_code..rhs_code.."#{result} =l ceql #{lhs_reg}, #{rhs_reg}\n"
            return result,code
        return comparison @, env, "ceql"
    NotEqual: (env)=>
        lhs_type, rhs_type = get_type(@lhs), get_type(@rhs)
        if lhs_type\is_a(rhs_type) or rhs_type\is_a(lhs_type)
            lhs_reg,lhs_code = env\to_reg @lhs
            rhs_reg,rhs_code = env\to_reg @rhs
            result = env\fresh_local "comparison"
            code = lhs_code..rhs_code.."#{result} =l cnel #{lhs_reg}, #{rhs_reg}\n"
            return result,code
        return comparison @, env, "cnel"
    TernaryOp: (env)=>
        overall_type = get_type @
        cond_reg,code = env\to_reg @condition
        true_reg,true_code = env\to_reg @ifTrue
        false_reg,false_code = env\to_reg @ifFalse
        true_label = env\fresh_label "ternary.true"
        false_label = env\fresh_label "ternary.false"
        end_label = env\fresh_label "ternary.end"
        ret_reg = env\fresh_local "ternary.result"
        code ..= check_truthiness get_type(@condition), env, cond_reg, true_label, false_label
        code ..= "#{true_label}\n#{true_code}#{ret_reg} =#{overall_type.base_type} copy #{true_reg}\njmp #{end_label}\n"
        code ..= "#{false_label}\n#{false_code}#{ret_reg} =#{overall_type.base_type} copy #{false_reg}\njmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return ret_reg, code

    FnCall: (env, skip_ret=false)=>
        call_sig = "(#{concat [tostring(get_type(a)) for a in *@], ","})"
        if @fn.__tag == "Var" and not @fn.__register
            top = @.__parent
            while top.__parent do top = top.__parent
            candidates = {}
            for decl in coroutine.wrap(-> each_tag(top, "FnDecl"))
                if decl.name[0] == @fn[0]
                    table.insert candidates, "#{@fn[0]}#{get_type(decl)}"

            node_assert #candidates > 0, @, "There is no function with this name"
            node_assert #candidates > 1, @, "This function is being called with: #{@fn[0]}#{call_sig} which doesn't match the definition: #{candidates[1]}"
            node_error @, "This function is being called with: #{@fn[0]}#{call_sig} which doesn't match any of the definitions:\n  - #{concat candidates, "\n  - "}"
        
        code = ""
        local fn_type, fn_reg
        fn_type = get_type @fn
        fn_reg,fn_code = env\to_reg @fn
        code ..= fn_code

        if fn_type
            node_assert fn_type\is_a(Types.FnType), @fn, "This is not a function, it's a #{fn_type or "???"}"
            node_assert fn_type\arg_signature! == call_sig, @, "This function is being called with #{@fn[0]}#{call_sig} but is defined as #{fn_type}"

        args = {}
        for arg in *@
            arg_reg, arg_code = env\to_reg arg
            code ..= arg_code
            table.insert args, "#{get_type(arg).abi_type} #{arg_reg}"

        if skip_ret
            return nil, "#{code}call #{fn_reg}(#{concat args, ", "})\n"

        ret_reg = env\fresh_local "return"
        ret_type = fn_type and fn_type.return_type or get_type(@)
        code ..= "#{ret_reg} =#{ret_type.abi_type} call #{fn_reg}(#{concat args, ", "})\n"
        return ret_reg, code

    MethodCall: (env, skip_ret=false)=> expr_compilers.FnCall(@, env, skip_ret)

    Lambda: (env)=>
        node_assert @__register, @, "Unreferenceable lambda"
        return @__register,""

    Struct: (env)=>
        t = get_type @
        struct_size = 8*#t.members
        ret = env\fresh_local "#{t.name\lower!}"
        code = "#{ret} =l alloc8 #{struct_size}\n"
        p = env\fresh_local "#{t.name\lower!}.member.loc"
        named_members = {m.name[0],m.value for m in *@ when m.name}
        unnamed_members = [m.value for m in *@ when not m.name]
        for i,m in ipairs t.members
            val = if named_members[m.name]
                named_members[m.name]
            elseif #unnamed_members > 0
                table.remove unnamed_members, 1
            else
                nil

            if val
                code ..= "#{p} =l add #{ret}, #{8*(i-1)}\n"
                val_reg,val_code = env\to_reg val
                code ..= val_code
                m_t = get_type val
                code ..= "store#{m_t.base_type} #{val_reg}, #{p} #xxx\n"
        code ..= "#{ret} =l call $intern_bytes(l #{ret}, l #{struct_size})\n"
        return ret, code

    Fail: (env)=> "0",env\compile_stmt(@).."#{env\fresh_label "unreachable"}\n"
    Return: (env)=> "0",env\compile_stmt(@).."#{env\fresh_label "unreachable"}\n"
    Skip: (env)=> "0",env\compile_stmt(@).."#{env\fresh_label "unreachable"}\n"
    Stop: (env)=> "0",env\compile_stmt(@).."#{env\fresh_label "unreachable"}\n"

stmt_compilers =
    Block: (env)=>
        concat([env\compile_stmt(stmt) for stmt in *@], "")
    Declaration: (env)=>
        varname = "%#{@var[0]}"
        node_assert not env.used_names[varname], @var, "Variable being shadowed: #{varname}"
        env.used_names[varname] = true
        value_type = get_type @value
        decl_type = value_type
        if @type
            decl_type = Types.parse_type @type
            node_assert value_type, @value, "Can't infer the type of this value"
            node_assert value_type\is_a(decl_type) or decl_type\is_a(value_type), @value, "Value is type #{value_type}, not declared type #{decl_type}"
        val_reg,code = env\to_reg @value
        node_assert @var.__register, @var, "Undefined variable"
        code ..= "#{@var.__register} =#{decl_type.base_type} copy #{val_reg}\n"
        return code
    Assignment: (env)=>
        lhs_type,rhs_type = get_type(@lhs), get_type(@rhs)
        node_assert rhs_type\is_a(lhs_type), @rhs, "Value is type #{rhs_type}, but it's being assigned to something with type #{lhs_type}"
        if @lhs.__tag == "Var"
            node_assert @lhs.__register, @lhs, "Undefined variable"
            rhs_reg,code = env\to_reg @rhs
            return "#{code}#{@lhs.__register} =#{lhs_type.base_type} copy #{rhs_reg}\n"
        
        node_assert @lhs.__tag == "IndexedTerm", @lhs, "Expected a Var or an indexed value"
        t = get_type(@lhs.value)
        is_optional = t\is_a(Types.OptionalType)
        t = t.nonnil if is_optional
        if t\is_a(Types.ListType)
            index_type = get_type(@lhs.index)
            list_reg,list_code = env\to_reg @lhs.value
            index_reg,index_code = env\to_reg @lhs.index
            rhs_reg,rhs_code = env\to_reg @rhs
            code = list_code..index_code..rhs_code
            if index_type\is_a(Types.Int)
                if rhs_type.abi_type == "d"
                    rhs_casted = env\fresh_local "list.item.float"
                    code ..= "#{rhs_casted} =d cast #{rhs_reg}\n"
                    rhs_reg = rhs_casted
                nonnil_label, end_label = env\fresh_label("if.nonnil"), env\fresh_label("if.nonnil.done")
                code ..= check_nil get_type(@lhs.value), env, list_reg, nonnil_label, end_label
                code ..= "#{nonnil_label}\n"
                code ..= "call $bl_list_set_nth(l #{list_reg}, l #{index_reg}, l #{rhs_reg})\n"
                code ..= "jmp #{end_label}\n"
                code ..= "#{end_label}\n"
                return code
            elseif index_type\is_a(Types.Range)
                node_error @lhs.index, "Assigning to list slices is not supported."
            else
                node_error @lhs.index, "Index is #{index_type} instead of Int or Range"
            return
        elseif t\is_a(Types.TableType)
            key_type = get_type(@lhs.index)
            tab_reg,code = env\to_reg @lhs.value
            key_reg,key_code = env\to_reg @lhs.index
            code ..= key_code
            val_reg,val_code = env\to_reg @rhs
            code ..= val_code

            convert_nils = (t2, src_reg, dest_reg)->
                if t2\is_a(Types.Int) or t2\is_a(Types.Bool)
                    code ..= "#{dest_reg} =l xor #{src_reg}, #{INT_NIL}\n"
                elseif t2\is_a(Types.Num)
                    code ..= "#{dest_reg} =d cast #{src_reg}\n"
                    code ..= "#{dest_reg} =l xor #{dest_reg}, #{FLOAT_NIL}\n"
                else
                    code ..= "#{dest_reg} =l copy #{src_reg}\n"

            key_setter = env\fresh_local "key.setter"
            convert_nils t.key_type, key_reg, key_setter
            value_setter = env\fresh_local "value.setter"
            convert_nils t.value_type, val_reg, value_setter

            nonnil_label, end_label = env\fresh_label("if.nonnil"), env\fresh_label("if.nonnil.done")
            code ..= check_nil get_type(@lhs.value), env, tab_reg, nonnil_label, end_label
            code ..= "#{nonnil_label}\n"
            code ..= "call $hashmap_set(l #{tab_reg}, l #{key_setter}, l #{value_setter})\n"
            code ..= "jmp #{end_label}\n"
            code ..= "#{end_label}\n"

            return code
        elseif t\is_a(Types.StructType)
            i,member_type = if @lhs.index.__tag == "FieldName"
                member_name = @lhs.index[0]
                node_assert t.members_by_name[member_name], @lhs.index, "Not a valid struct member of #{t}"
                t.members_by_name[member_name].index, t.members_by_name[member_name].type
            elseif @lhs.index.__tag == "Int"
                i = tonumber(@lhs.index[0])
                node_assert 1 <= i and i <= #t.members, @lhs.index, "#{t} only has members between 1 and #{#t.members}"
                i, t.members[i].type
            else
                node_error @lhs.index, "Structs can only be indexed by a field name or Int literal"
            struct_reg,code = env\to_reg @lhs.value
            loc = env\fresh_local "member.loc"
            rhs_reg,rhs_code = env\to_reg @rhs
            code ..= rhs_code

            nonnil_label, end_label = env\fresh_label("if.nonnil"), env\fresh_label("if.nonnil.done")
            code ..= check_nil get_type(@lhs.value), env, struct_reg, nonnil_label, end_label
            code ..= "#{nonnil_label}\n"
            code ..= "#{loc} =l add #{struct_reg}, #{8*(i-1)}\n"
            code ..= "store#{rhs_type.base_type} #{rhs_reg}, #{loc}\n"
            code ..= "jmp #{end_label}\n"
            code ..= "#{end_label}\n"

            return code
        else
            node_error @lhs.value, "Only Lists and Structs are mutable, not #{t}"
            return
    AddUpdate: (env)=>
        node_assert @lhs.__register, @lhs, "Undefined variable"
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        rhs_reg,code = env\to_reg @rhs
        if lhs_type == rhs_type and (lhs_type\is_a(Types.Int) or lhs_type\is_a(Types.Num))
            return code.."#{@lhs.__register} =#{lhs_type.abi_type} add #{@lhs.__register}, #{rhs_reg}\n"
        elseif lhs_type == rhs_type and lhs_type\is_a(Types.String)
            return code.."#{@lhs.__register} =l call $bl_string_append_string(l #{@lhs.__register}, l #{rhs_reg})\n"
        elseif lhs_type == rhs_type and lhs_type\is_a(Types.ListType)
            return code.."#{@lhs.__register} =l call $bl_list_concat(l #{@lhs.__register}, l #{rhs_reg})\n"
        else
            fn_reg, t2 = get_function_reg @__parent, "add", "(#{lhs_type},#{rhs_type})"
            node_assert fn_reg, @, "addition is not supported for #{lhs_type} and #{rhs_type}"
            node_assert t2.return_type == lhs_type, @, "Return type for add(#{lhs_type},#{rhs_type}) is #{t2.return_type} instead of #{lhs_type}"
            return code.."#{@lhs.__register} =#{lhs_type.abi_type} call #{fn_reg}(#{lhs_type.abi_type} #{@lhs.__register}, #{rhs_type.abi_type} #{rhs_reg})\n"
    SubUpdate: (env)=>
        node_assert @lhs.__register, @lhs, "Undefined variable"
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        rhs_reg,code = env\to_reg @rhs
        if lhs_type == rhs_type and (lhs_type\is_a(Types.Int) or lhs_type\is_a(Types.Num))
            return code.."#{@lhs.__register} =#{lhs_type.abi_type} sub #{@lhs.__register}, #{rhs_reg}\n"
        else
            fn_reg, t2 = get_function_reg @__parent, "subtract", "(#{lhs_type},#{rhs_type})"
            node_assert fn_reg, @, "subtraction is not supported for #{lhs_type} and #{rhs_type}"
            node_assert t2.return_type == lhs_type, @, "Return type for subtract(#{lhs_type},#{rhs_type}) is #{t2.return_type} instead of #{lhs_type}"
            return code.."#{@lhs.__register} =#{lhs_type.abi_type} call #{fn_reg}(#{lhs_type.abi_type} #{@lhs.__register}, #{rhs_type.abi_type} #{rhs_reg})\n"
    MulUpdate: (env)=>
        node_assert @lhs.__register, @lhs, "Undefined variable"
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        rhs_reg,code = env\to_reg @rhs
        if lhs_type == rhs_type and (lhs_type\is_a(Types.Int) or lhs_type\is_a(Types.Num))
            return code.."#{@lhs.__register} =#{lhs_type.abi_type} mul #{@lhs.__register}, #{rhs_reg}\n"
        else
            fn_reg, t2 = get_function_reg @__parent, "multiply", "(#{lhs_type},#{rhs_type})"
            node_assert fn_reg, @, "multiplication is not supported for #{lhs_type} and #{rhs_type}"
            node_assert t2.return_type == lhs_type, @, "Return type for multiply(#{lhs_type},#{rhs_type}) is #{t2.return_type} instead of #{lhs_type}"
            return code.."#{@lhs.__register} =#{lhs_type.abi_type} call #{fn_reg}(#{lhs_type.abi_type} #{@lhs.__register}, #{rhs_type.abi_type} #{rhs_reg})\n"
    DivUpdate: (env)=>
        node_assert @lhs.__register, @lhs, "Undefined variable"
        lhs_type,rhs_type = get_type(@lhs),get_type(@rhs)
        rhs_reg,code = env\to_reg @rhs
        if lhs_type == rhs_type and (lhs_type\is_a(Types.Int) or lhs_type\is_a(Types.Num))
            return code.."#{@lhs.__register} =#{lhs_type.abi_type} div #{@lhs.__register}, #{rhs_reg}\n"
        else
            fn_reg, t2 = get_function_reg @__parent, "divide", "(#{lhs_type},#{rhs_type})"
            node_assert fn_reg, @, "division is not supported for #{lhs_type} and #{rhs_type}"
            node_assert t2.return_type == lhs_type, @, "Return type for divide(#{lhs_type},#{rhs_type}) is #{t2.return_type} instead of #{lhs_type}"
            return code.."#{@lhs.__register} =#{lhs_type.abi_type} call #{fn_reg}(#{lhs_type.abi_type} #{@lhs.__register}, #{rhs_type.abi_type} #{rhs_reg})\n"
    OrUpdate: (env)=>
        for val in *@
            node_assert get_type(val)\is_a(Types.Bool), val, "Expected Bool here, but got #{get_type val}"
        node_assert @lhs.__register, @lhs, "Undefined variable"
        true_label = env\fresh_label "or.equal.true"
        false_label = env\fresh_label "or.equal.false"
        code = "jnz #{@lhs.__register}, #{true_label}, #{false_label}\n"
        code ..= "#{false_label}\n"
        rhs_reg,rhs_code = env\to_reg @rhs
        code ..= rhs_code
        code ..= "#{@lhs.__register} =l copy #{rhs_reg}\n"
        code ..= "jmp #{true_label}\n#{true_label}\n"
        return code
    AndUpdate: (env)=>
        for val in *@
            node_assert get_type(val)\is_a(Types.Bool), val, "Expected Bool here, but got #{get_type val}"
        node_assert @lhs.__register, @lhs, "Undefined variable"
        true_label = env\fresh_label "and.equal.true"
        false_label = env\fresh_label "and.equal.false"
        code = "jnz #{@lhs.__register}, #{true_label}, #{false_label}\n"
        code ..= "#{true_label}\n"
        rhs_reg,rhs_code = env\to_reg @rhs
        code ..= rhs_code
        code ..= "#{@lhs.__register} =l copy #{rhs_reg}\n"
        code ..= "jmp #{false_label}\n#{false_label}\n"
        return code
    XorUpdate: (env)=>
        for val in *@
            node_assert get_type(val)\is_a(Types.Bool), val, "Expected Bool here, but got #{get_type val}"
        node_assert @lhs.__register, @lhs, "Undefined variable"
        rhs_reg,code = env\to_reg @rhs
        return code.."#{@lhs.__register} =#{lhs_type.abi_type} xor #{@lhs.__register}, #{rhs_reg}\n"
    ButWithUpdate: (env)=>
        t = get_type @base
        if t\is_a(Types.ListType)
            error "Not impl"
        elseif t\is_a(Types.String)
            error "Not impl"
        elseif t\is_a(Types.StructType)
            node_assert @base.__register, @base, "Undefined variable"
            struct_size = 8*#t.members
            ret = env\fresh_local "#{t.name\lower!}.butwith"
            code = "#{ret} =l alloc8 #{struct_size}\n"
            code ..= "call $memcpy(l #{ret}, l #{@base.__register}, l #{struct_size})\n"
            p = env\fresh_local "#{t.name\lower!}.butwith.member.loc"
            used = {}
            for override in *@
                i = if override.index
                    tonumber(override.index[0])
                elseif override.field
                    t.members_by_name[override.field[0]].index
                else
                    node_error override, "I don't know what this is"

                node_assert not used[i], override, "Redundant value, this field is already being overwritten"
                used[i] = true

                node_assert 1 <= i and i <= #t.members, override, "Not a valid member of #{t}"
                node_assert get_type(override.value)\is_a(t.members[i].type), override.value, "Not a #{t.members[i].type}"
                val_reg,val_code = env\to_reg override.value
                code ..= val_code
                code ..= "#{p} =l add #{ret}, #{8*(i-1)}\n"
                code ..= "store#{t.members[i].type.base_type} #{val_reg}, #{p}\n"

            code ..= "#{@base.__register} =l call $intern_bytes(l #{ret}, l #{struct_size})\n"
            return code
        else
            node_error @, "| operator is only supported for List and Struct types"

    MethodCallUpdate: (env)=>
        dest = @[1]
        node_assert dest and dest.__tag == "Var", dest, "Method call updates expect a variable"
        update_sig = "(#{concat [tostring(get_type(a)) for a in *@], ","})=>#{get_type(dest)}"
        if @fn.__tag == "Var" and not @fn.__register
            top = @.__parent
            while top.__parent do top = top.__parent
            candidates = {}
            for decl in coroutine.wrap(-> each_tag(top, "FnDecl"))
                if decl.name[0] == @fn[0]
                    table.insert candidates, "#{@fn[0]}#{get_type(decl)}"

            node_assert #candidates > 0, @, "There is no function with this name"
            node_assert #candidates > 1, @, "For this to work, #{@fn[0]} should be #{update_sig}, not #{candidates[1]}"
            node_error @, "For this to work, #{@fn[0]} should be #{update_sig} which doesn't match any of the definitions:\n  - #{concat candidates, "\n  - "}"
        
        fn_type = get_type @fn
        fn_reg,code = env\to_reg @fn

        if fn_type
            node_assert fn_type\is_a(Types.FnType), @fn, "This is not a function, it's a #{fn_type or "???"}"
            node_assert "#{fn_type}" == update_sig, @, "For this to work, #{@fn[0]} should be #{update_sig}, not #{fn_type}"

        args = {}
        for arg in *@
            arg_reg, arg_code = env\to_reg arg
            code ..= arg_code
            table.insert args, "#{get_type(arg).abi_type} #{arg_reg}"

        ret_type = fn_type and fn_type.return_type or get_type(dest)
        code ..= "#{dest.__register} =#{ret_type.abi_type} call #{fn_reg}(#{concat args, ", "})\n"
        return code

    FnDecl: (env)=> ""
    Pass: (env)=> ""
    Fail: (env)=>
        if @message
            node_assert get_type(@message) == Types.String, @message, "Failure messages must be a String, not a #{get_type @message}"
            msg,code = env\to_reg @message
            full_msg = env\fresh_local "failure.message"
            code ..= "#{full_msg} =l call $bl_string_append_string(l #{env\get_string_reg(get_node_pos(@)..': ', "failure.location")}, l #{msg})\n"
            code ..= "call $errx(l 1, l #{full_msg})\n"
            return code
        else
            return "call $errx(l 1, l #{env\get_string_reg(get_node_pos(@)..': Unexpected failure!', "failure.message")})\n"
    TypeDeclaration: (env)=> ""
    StructDeclaration: (env)=> ""
    FnCall: (env)=>
        _, code = env\to_reg @, true
        code = code\gsub("[^\n]- (call [^\n]*\n)$", "%1")
        return code
    MethodCall: (env)=>
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
        assert @jump_label, "Jump label should have been populated by outer loop"
        return "jmp #{@jump_label}\n"
    Skip: (env)=>
        assert @jump_label, "Jump label should have been populated by outer loop"
        return "jmp #{@jump_label}\n"
    If: (env)=>
        code = ""
        end_label = env\fresh_label "if.end"
        false_label = env\fresh_label "if.else"
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
        end_label = env\fresh_label "when.end"
        next_case = env\fresh_label "when.case"
        next_body = env\fresh_label "when.body"
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
        code ..= "#{end_label}\n"
        return code
    Repeat: (env)=>
        -- Rough breakdown:
        -- jmp @repeat
        -- @repeat
        -- // body code
        -- jmp @repeat.between
        -- // between code
        -- jmp @repeat
        -- @repeat.end
        repeat_label = env\fresh_label "repeat"
        between_label = env\fresh_label "repeat.between"
        end_label = env\fresh_label "repeat.end"

        for skip in coroutine.wrap(-> each_tag(@, "Skip"))
            if not skip.target or skip.target[0] == "repeat"
                skip.jump_label = repeat_label

        for stop in coroutine.wrap(-> each_tag(@, "Stop"))
            if not stop.target or stop.target[0] == "repeat"
                stop.jump_label = end_label

        code = "jmp #{repeat_label}\n#{repeat_label}\n"
        code ..= env\compile_stmt @body
        if @between
            unless has_jump\match(code)
                code ..= "jmp #{between_label}\n"
            code ..= "#{between_label}\n#{env\compile_stmt @between}"
        unless has_jump\match(code)
            code ..= "jmp #{repeat_label}\n"
        code ..= "#{end_label}\n"
        return code
    While: (env)=>
        -- Rough breakdown:
        -- jmp @while.condition
        -- jnz (condition), @while.body, @while.end
        -- @while.body
        -- // body code
        -- jmp @while.between
        -- // between code
        -- jnz (condition), @while.body, @while.end
        -- @while.end
        cond_label = env\fresh_label "while.condition"
        body_label = env\fresh_label "while.body"
        between_label = env\fresh_label "while.between"
        end_label = env\fresh_label "while.end"

        for skip in coroutine.wrap(-> each_tag(@, "Skip"))
            if not skip.target or skip.target[0] == "while"
                skip.jump_label = cond_label

        for stop in coroutine.wrap(-> each_tag(@, "Stop"))
            if not stop.target or stop.target[0] == "while"
                stop.jump_label = end_label

        cond_reg,cond_code = env\to_reg @condition
        code = "jmp #{cond_label}\n#{cond_label}\n"
        code ..= cond_code
        code ..= "jnz #{cond_reg}, #{body_label}, #{end_label}\n"
        code ..= "#{body_label}\n#{env\compile_stmt @body}"
        if @between
            code ..= cond_code
            unless has_jump\match(code)
                code ..= "jnz #{cond_reg}, #{between_label}, #{end_label}\n"
            code ..= "#{between_label}\n#{env\compile_stmt @between}"
            unless has_jump\match(code)
                code ..= "jmp #{body_label}\n"
        else
            unless has_jump\match(code)
                code ..= "jmp #{cond_label}\n"
        code ..= "#{end_label}\n"
        return code
    For: (env)=>
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

        next_label = env\fresh_label "for.next"
        body_label = env\fresh_label "for.body"
        between_label = env\fresh_label "for.between"
        end_label = env\fresh_label "for.end"

        for skip in coroutine.wrap(-> each_tag(@, "Skip"))
            if not skip.target or skip.target[0] == "for" or (@var and skip.target[0] == @var[0]) or (@index and skip.target[0] == @index[0])
                skip.jump_label = next_label

        for stop in coroutine.wrap(-> each_tag(@, "Stop"))
            if not stop.target or stop.target[0] == "for" or (@var and stop.target[0] == @var[0]) or (@index and stop.target[0] == @index[0])
                stop.jump_label = end_label

        i = env\fresh_local(iter_type\is_a(Types.TableType) and "k" or "i")
        len = env\fresh_local "len"
        is_done = env\fresh_local "for.is_done"

        iter_reg,code = env\to_reg @iterable
        code ..= "#{i} =l copy 0\n"
        if iter_type\is_a(Types.Range)
            code ..= "#{len} =l call $range_len(l #{iter_reg})\n"
        elseif iter_type\is_a(Types.ListType)
            code ..= "#{len} =l call $bl_list_len(l #{iter_reg})\n"
        elseif iter_type\is_a(Types.TableType)
            _=nil -- Len is not used for tables
            -- code ..= "#{len} =l call $hashmap_len(l #{iter_reg})\n"
        else
            node_error @iterable, "Expected an iterable type, not #{iter_type}"
        code ..= "jmp #{next_label}\n"
        code ..= "#{next_label}\n"
        if iter_type\is_a(Types.TableType)
            code ..= "#{i} =l call $hashmap_next(l #{iter_reg}, l #{i})\n"
            code ..= "jnz #{i}, #{body_label}, #{end_label}\n"
        else
            code ..= "#{i} =l add #{i}, 1\n"
            code ..= "#{is_done} =l csgtl #{i}, #{len}\n"
            code ..= "jnz #{is_done}, #{end_label}, #{body_label}\n"

        code ..= "#{body_label}\n"
        if @index
            index_reg = @index.__register
            env.used_names[index_reg] = true
            if iter_type\is_a(Types.TableType) and (iter_type.key_type\is_a(Types.Int) or iter_type.key_type\is_a(Types.Bool))
                code ..= "#{index_reg} =l xor #{i}, #{INT_NIL}\n"
            elseif iter_type\is_a(Types.TableType) and iter_type.key_type\is_a(Types.Num)
                bits = @fresh_local "key.bits"
                code ..= "#{bits} =l xor #{i}, #{FLOAT_NIL}\n"
                code ..= "#{index_reg} =d cast #{bits}\n"
            else
                code ..= "#{index_reg} =l copy #{i}\n"

        if @var
            var_reg = @var.__register
            env.used_names[var_reg] = true
            if iter_type\is_a(Types.TableType)
                if @index
                    if iter_type.value_type\is_a(Types.Int) or iter_type.value_type\is_a(Types.Bool)
                        value_raw = env\fresh_local "value.raw"
                        code ..= "#{value_raw} =l call $hashmap_get(l #{iter_reg}, l #{i})\n"
                        code ..= "#{var_reg} =l xor #{value_raw}, #{INT_NIL}\n"
                    elseif iter_type.value_type\is_a(Types.Num)
                        value_raw = env\fresh_local "value.raw"
                        code ..= "#{value_raw} =l call $hashmap_get(l #{iter_reg}, l #{i})\n"
                        code ..= "#{value_raw} =l xor #{value_raw}, #{FLOAT_NIL}\n"
                        code ..= "#{var_reg} =d cast #{bits}\n"
                    else
                        code ..= "#{var_reg} =l call $hashmap_get(l #{iter_reg}, l #{i})\n"
                else
                    if iter_type.key_type\is_a(Types.Int) or iter_type.key_type\is_a(Types.Bool)
                        code ..= "#{var_reg} =l xor #{i}, #{INT_NIL}\n"
                    elseif iter_type.key_type\is_a(Types.Num)
                        key_bits = env\fresh_local "key.bits"
                        code ..= "#{key_bits} =l xor #{i}, #{FLOAT_NIL}\n"
                        code ..= "#{var_reg} =d cast #{key_bits}\n"
                    else
                        code ..= "#{var_reg} =l copy #{i}\n"
            elseif iter_type\is_a(Types.Range)
                code ..= "#{var_reg} =l call $range_nth(l #{iter_reg}, l #{i})\n"
            else
                if iter_type.item_type.base_type == "d"
                    tmp = env\fresh_local "item.int"
                    code ..= "#{tmp} =l call $bl_list_nth(l #{iter_reg}, l #{i})\n"
                    code ..= "#{var_reg} =#{iter_type.item_type.abi_type} cast #{tmp}\n"
                else
                    code ..= "#{var_reg} =#{iter_type.item_type.abi_type} call $bl_list_nth(l #{iter_reg}, l #{i})\n"

        code ..= "#{env\compile_stmt @body}"

        -- If we reached this point, no skips
        unless has_jump\match(code)
            if iter_type\is_a(Types.TableType)
                code ..= "#{i} =l call $hashmap_next(l #{iter_reg}, l #{i})\n"
                code ..= "jnz #{i}, #{between_label}, #{end_label}\n"
            else
                code ..= "#{i} =l add #{i}, 1\n"
                code ..= "#{is_done} =l csgtl #{i}, #{len}\n"
                code ..= "jnz #{is_done}, #{end_label}, #{between_label}\n"

        code ..= "#{between_label}\n"
        if @between
            code ..= env\compile_stmt @between

        unless has_jump\match(code)
            code ..= "jmp #{body_label}\n"

        code ..= "#{end_label}\n"
        return code
        
compile_prog = (ast, filename)->
    env = Environment!
    return env\compile_program(ast, filename)

return {:compile_prog}
