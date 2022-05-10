Types = require 'typecheck'
bp = require 'bp'
import add_parenting, get_type, parse_type from Types
import log, viz, assert_node, print_err from require 'util'
concat = table.concat

has_jump = bp.compile('^_("jmp"/"jnz"/"ret")\\b ..$ $$')

local compile_stmt, to_reg, store_to, stmt_compilers, expr_compilers

each_tag = (...)=>
    return unless type(@) == 'table'

    tags = {...}
    for tag in *tags
        coroutine.yield @ if @__tag == tag

    for k,v in pairs(@)
        each_tag(v, ...) if type(v) == 'table' and not (type(k) == 'string' and k\match("^__"))

get_function_reg = (scope, name, arg_signature)->
    return nil unless scope
    switch scope.__tag
        when "Block"
            for i=#scope,1,-1
                stmt = scope[i]
                log "Checking for #{name} #{arg_signature} in #{stmt}" if stmt.__tag == "FnDecl"
                if stmt.__tag == "FnDecl" and stmt.name[0] == name and get_type(stmt)\arg_signature! == arg_signature
                    return assert_node(stmt.__register, stmt, "Function without a name"), get_type(stmt)
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

infixop = (env, op)=>
    t = get_type @[1]
    lhs_reg, lhs_code = env\to_reg @[1]
    code = lhs_code
    ret_reg = env\fresh_local "result"
    for i=2,#@
        rhs = @[i]
        rhs_type = get_type rhs
        assert_node rhs_type == t, rhs, "Expected type: #{t} but got type #{rhs_type}"
        rhs_reg, rhs_code = env\to_reg rhs
        code ..= rhs_code
        if type(op) == 'string'
            code ..= "#{ret_reg} =#{t.abi_type} #{op} #{lhs_reg}, #{rhs_reg}\n"
        else
            code ..= op(ret_reg, lhs_reg, rhs_reg)
        lhs_reg = ret_reg
    return ret_reg, code

comparison = (env, cmp)=>
    t = get_type @[1]
    for val in *@
        assert_node get_type(val) == t, val, "Expected #{t} but got #{get_type(val)}"

    prev_val = nil
    lhs_reg,code = env\to_reg @[1]
    rhs_reg,rhs_code = env\to_reg @[2]
    code ..= rhs_code

    result = env\fresh_local "comparison"
    if t == Types.String
        code ..= "#{result} =l call $strcmp(l #{lhs_reg}, l #{rhs_reg})\n"
        code ..= "#{result} =l #{cmp} 0, #{result}\n"
    else
        code ..= "#{result} =#{t.abi_type} #{cmp} #{lhs_reg}, #{rhs_reg}\n"

    return result, code

updater = (op, flop)->
    (env)=>
        lhs,rhs = @[1],@[2]
        make_rhs = (lhs_reg)->
            rhs_reg, code = env\to_reg rhs
            lhs_type = get_type lhs
            if lhs_type.abi_type == "d" and flop
                op = flop
            result_reg = env\fresh_local "result"
            code ..= "#{result_reg} =#{lhs_type.abi_type} #{op} #{lhs_reg}, #{rhs_reg}\n"
            return get_type(rhs),result_reg,code
        return store_to @[1], make_rhs, env

class Environment
    new: =>
        @strings = {}
        @used_names = {}
        @dups = setmetatable({}, {__index:->0})
        @type_code = ""
        @string_code = ""
        @fn_code = ""
        @main_code = ""
        @concat_funcs = {}

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
            chunks = str\gsub('[^ !#-[^-~]]', (c)->"\",b #{c\byte(1)},b\"")
            @string_code ..= "data #{name} = {b\"#{chunks}\",b 0}\n"
        return @strings[str]

    declare_function: (fndec)=>
        args = ["#{parse_type(arg.type[1]).abi_type} #{arg.arg[1].__register}" for arg in *fndec.args]
        fn_scope = @inner_scope {"%#{arg.arg[0]}",true for arg in *fndec.args}
        body_code = if fndec.body[1].__tag == "Block"
            fn_scope\compile_stmt fndec.body[1]
        else
            ret_reg, tmp = fn_scope\to_reg fndec.body[1]
            "#{tmp}ret #{ret_reg}\n"
        body_code = body_code\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))
        fn_type = get_type fndec
        ret_type = fn_type.return_type
        assert_node fndec.__register, fndec, "Function has no name"
        fn_name = fndec.__register
        @fn_code ..= "function #{ret_type == Types.Void and "" or ret_type.abi_type.." "}"
        @fn_code ..= "#{fn_name}(#{concat args, ", "}) {\n@start\n#{body_code}"
        if ret_type == Types.Void
            @fn_code ..= "  ret\n"
        elseif not has_jump\match(@fn_code)
            @fn_code ..= "  ret 0\n"
        @fn_code ..= "}\n"

    get_concat_fn: (t)=>
        if @concat_funcs["#{t}"]
            return @concat_funcs["#{t}"]

        fn_name = @fresh_global "concat.value"
        @concat_funcs["#{t}"] = fn_name

        code = "function l #{fn_name}(l %initialstring, #{t.base_type} %obj) {\n@start\n"
        str = "%initialstring"

        append_reg = (reg, t)->
            if t == Types.Int
                code ..= "#{str} =l call $bl_string_append_int(l #{str}, l #{reg})\n"
            elseif t == Types.Float
                code ..= "#{str} =l call $bl_string_append_float(l #{str}, d #{reg})\n"
            elseif t == Types.Bool
                code ..= "#{str} =l call $bl_string_append_bool(l #{str}, l #{reg})\n"
            elseif t == Types.Nil
                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg("nil", "nil")})\n"
            elseif t == Types.Void
                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg("Void", "void")})\n"
            elseif t == Types.String
                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{reg})\n"
            elseif t == Types.Range
                code ..= "#{str} =l call $bl_string_append_range(l #{str}, :Range #{reg})\n"
            elseif t.__class == Types.ListType
                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg("[","sqbracket.open")})\n"

                len = @fresh_local "list.len"
                code ..= "#{len} =l loadl #{reg}\n"
                i = @fresh_local "list.i"
                code ..= "#{i} =l copy 1\n"

                loop_label = @fresh_label "list.loop"
                body_label = @fresh_label "list.loop.body"
                end_label = @fresh_label "list.loop.end"

                code ..= "jmp #{loop_label}\n#{loop_label}\n"
                finished = @fresh_local "list.finished"
                code ..= "#{finished} =l csgtl #{i}, #{len}\n"
                code ..= "jnz #{finished}, #{end_label}, #{body_label}\n"
                code ..= "#{body_label}\n"

                comma_label = @fresh_label "list.loop.needscomma"
                skip_comma_label = @fresh_label "list.loop.skipcomma"
                comma = @fresh_local "list.needscomma"
                code ..= "#{comma} =l csgtl #{i}, 1\n"
                code ..= "jnz #{comma}, #{comma_label}, #{skip_comma_label}\n"
                code ..= "#{comma_label}\n"
                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg(", ","comma.space")})\n"
                code ..= "jmp #{skip_comma_label}\n"
                code ..= "#{skip_comma_label}\n"
                
                item = @fresh_local "list.item"
                code ..= "#{item} =l call $bl_list_nth(l #{reg}, l #{i})\n"
                if t.item_type.abi_type == "d"
                    item2 = @fresh_local "list.item.float"
                    code ..= "#{item2} =d cast #{item}\n"
                    item = item2

                append_reg item, t.item_type

                code ..= "#{i} =l add #{i}, 1\n"

                code ..= "jmp #{loop_label}\n#{end_label}\n"

                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg("]","sqbracket.close")})\n"
            elseif t.__class == Types.StructType
                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg("#{t.name}{#{t.members[1].name}=")})\n"
                ptr_reg = @fresh_local "member.loc"
                for i,mem in ipairs t.members
                    if i > 1
                        code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg(", #{mem.name}=")})\n"
                    code ..= "#{ptr_reg} =l add #{reg}, #{8*(i-1)}\n"
                    member_reg = @fresh_local "member.#{mem.name}"
                    code ..= "#{member_reg} =#{mem.type.abi_type} load#{mem.type.base_type} #{ptr_reg}\n"
                    append_reg member_reg, mem.type

                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg("}","closecurly")})\n"
            elseif t.__class == Types.FnType
                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg("#{t}")})\n"
            else
                assert_node false, val, "Unsupported concat type"

        append_reg "%obj", t
        code ..= "ret #{str}\n"
        code ..= "}\n"
        code = code\gsub("[^\n]+", =>((@\match("^[@}]") or @\match("^function")) and @ or "  "..@))
        @fn_code ..= code

        return fn_name

    to_reg: (node, ...)=>
        if not node.__tag
            return @to_reg node[1], ...
        assert_node expr_compilers[node.__tag], node, "Expression compiler implemented for #{node.__tag}"
        return expr_compilers[node.__tag](node, @, ...)

    compile_stmt: (node)=>
        if not node.__tag
            return @compile_stmt node[1]
        assert_node stmt_compilers[node.__tag], node, "Not implemented: #{node.__tag}"
        return stmt_compilers[node.__tag](node, @)

    compile_program: (ast, filename)=>
        add_parenting(ast)

        @type_code = "type :Range = { l, l, l }\n"
        for s in coroutine.wrap(-> each_tag(ast, "StructType"))
            t = parse_type s
            @type_code ..= "type :#{t.name} = { #{concat [m.type.abi_type for m in *t.members], ", "} }"

        @used_names["%__argc"] = true
        @used_names["%argc"] = true
        @used_names["%argv"] = true
        for v in coroutine.wrap(-> each_tag(ast, "Var"))
            if v[0] == "argc"
                v.__register = "%argc"
            elseif v[0] == "argv"
                v.__register = "%argv"
            elseif v[0] == "__argc"
                v.__register = "%__argc"

        -- Set up variable registers:
        hook_up_refs = (var, scope)->
            assert var.__tag == "Var" and scope and scope != var
            var.__register or= @fresh_local var[0]
            for k,node in pairs scope
                continue unless type(node) == 'table' and not (type(k) == 'string' and k\match("^__"))
                switch node.__tag
                    when "Var"
                        if node[0] == var[0]
                            assert_node not node.__register, var, "Variable shadows earlier declaration #{node.__decl}"
                            node.__register = var.__register
                            node.__decl = var
                    when "FnDecl"
                        hook_up_refs var, node.body, true if var.__register\match("^%$")
                    else
                        hook_up_refs var, node

        -- Set up function names (global):
        for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl", "Lambda"))
            fndec.__register = @fresh_global(fndec.name and fndec.name[0] or "lambda")
            fndec.__decl = fndec
            if fndec.name
                fndec.name[1].__register = fndec.__register
                fndec.name[1].__decl = fndec
                hook_up_refs fndec.name[1], fndec.__parent
                    
        for fn in coroutine.wrap(-> each_tag(ast, "FnDecl", "Lambda"))
            for a in *fn.args
                hook_up_refs a.arg[1], fn.body
        for vardec in coroutine.wrap(-> each_tag(ast, "Declaration"))
            scope = if vardec.__parent.__tag == "Block"
                i = 1
                while vardec.__parent[i] != vardec
                    i += 1
                {table.unpack(vardec.__parent, i+1)}
            else vardec.__parent
            hook_up_refs vardec.var[1], scope -- vardec.__parent
        for for_block in coroutine.wrap(-> each_tag(ast, "For"))
            if for_block.var
                hook_up_refs for_block.var[1], for_block.body
            if for_block.index
                hook_up_refs for_block.index[1], for_block.body

        -- Compile functions:
        for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl", "Lambda"))
            @declare_function fndec

        body_code = @compile_stmt(ast)\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))

        code = "# Source file: #{filename}\n\n"
        code ..= "#{@type_code}\n" if #@type_code > 0
        code ..= "#{@string_code}\n" if #@string_code > 0
        code ..= "#{@fn_code}\n" if #@fn_code > 0
        code ..= "export function w $main(w %__argc, l %argv) {\n@start\n  %argc =l extsw %__argc\n#{body_code}  ret 0\n}\n"
        return code

expr_compilers =
    Var: (env)=>
        assert_node @__register, @, "Undefined variable"
        return @__register, ""
    Global: (env)=>
        return "#{@[0]}", ""
    Int: (env)=>
        return "#{@[0]}",""
    Nil: (env)=> "0",""
    Bool: (env)=> (@[0] == "yes" and "1" or "0"),""
    Float: (env)=> "d_#{@[0]}",""
    String: (env)=>
        return env\get_string_reg(@content[0]),"" if #@content == 0
        str = env\fresh_local "str"
        code = "#{str} =l call $bl_string(l #{env\get_string_reg("", "emptystr")})\n"

        stringify = (val)->
            if val.__tag == "Escape"
               --Escape:: `\ (`x 2 hex / `a,b,t,n,r,v / 3 `0-8 / .)
                esc = {a:'\a',b:'\b',t:'\t',n:'\n',r:'\r',v:'\v'}
                text = val[0]\sub(2)
                c = if esc[text]
                    esc[text]\byte(1)
                elseif text\match('[0-8][0-8][0-8]')
                    tonumber(text, 8)
                elseif text\match('x[0-9a-fA-F][0-9a-fA-F]')
                    tonumber(text\sub(2), 16)
                else
                    text\byte(1)
                code ..= "#{str} =l call $bl_string_append_char(l #{str}, l #{c})\n"
            else
                t = get_type(val)
                fn_name = env\get_concat_fn t
                val_reg,val_code = env\to_reg val
                code ..= val_code
                code ..= "#{str} =l call #{fn_name}(l #{str}, #{t.base_type} #{val_reg})\n"

        i = @content.start
        for interp in *@content
            if interp.start > i
                chunk = @content[0]\sub(1+(i-@content.start), interp.start-@content.start)
                code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{env\get_string_reg chunk})\n"

            stringify interp[1]
            i = interp.after

        if @content.after > i
            chunk = @content[0]\sub(1+(i-@content.start), @content.after-@content.start)
            code ..= "#{str} =l call $bl_string_append_string(l #{str}, l #{env\get_string_reg chunk})\n"

        return str,code

    Negative: (env)=>
        t = get_type @[1]
        if t == Types.Int or t == Types.Float
            reg,code = env\to_reg @[1]
            ret = env\fresh_local "neg"
            return ret, "#{code}#{ret} =#{t.abi_type} neg #{reg}\n"
        elseif t == Types.Range
            orig,code = env\to_reg @[1]
            range = env\fresh_local "neg.range"
            code ..= "#{range} =l call $range_backwards(l #{orig})\n"
            return range, code
        else
            assert_node false, @, "Invalid type to negate: #{t}"
    Len: (env)=>
        t = get_type @[1]
        if t == Types.Range
            range,code = env\to_reg @[1]
            len = env\fresh_local "range.len"
            code ..= "#{len} =l call $range_len(l #{range})\n"
            return len, code
        elseif t.__class == Types.ListType
            list,code = env\to_reg @[1]
            len = env\fresh_local "list.len"
            return len, "#{code}#{len} =l loadl #{list}\n"
        elseif t == Types.String
            str,code = env\to_reg @[1]
            len = env\fresh_local "str.len"
            return len, "#{code}#{len} =l call $strlen(l #{str})\n"
        else
            assert_node false, @, "Expected List or Range type, not #{t}"
    Not: (env)=>
        assert_node get_type(@[1]) == Types.Bool, @[1], "Expected a Bool"
        b,code = env\to_reg @[1]
        ret = env\fresh_local "not"
        code ..= "#{ret} =l ceql #{b}, 0\n"
        return ret, code
    IndexedTerm: (env)=>
        t = get_type @[1]
        if t.__class == Types.ListType
            item_type = t.item_type
            index_type = get_type(@[2])
            list_reg,list_code = env\to_reg @[1]
            index_reg,index_code = env\to_reg @[2]
            code = list_code..index_code
            if index_type == Types.Int
                item = env\fresh_local "list.item"
                code ..= "#{item} =l call $bl_list_nth(l #{list_reg}, l #{index_reg})\n"
                if t.item_type.abi_type == "d"
                    item2 = env\fresh_local "list.item.float"
                    code ..= "#{item2} =d cast #{item}\n"
                    item = item2
                return item,code
            elseif index_type == Types.Range
                slice = env\fresh_local "slice"
                code ..= "#{slice} =l call $bl_list_slice(l #{list_reg}, l #{index_reg})\n"
                return slice,code
            else
                assert_node false, @[2], "Index is #{index_type} instead of Int or Range"
        elseif t.__class == Types.StructType
            assert_node @[2].__tag == "Var", @[2], "Structs can only be indexed by member"
            member_name = @[2][0]
            assert_node t.members_by_name[member_name], @[2], "Not a valid struct member of #{t}"
            struct_reg,struct_code = env\to_reg @[1]
            i = t.members_by_name[member_name].index
            member_type = t.members_by_name[member_name].type
            code = struct_code
            loc = env\fresh_local "member.loc"
            code ..= "#{loc} =l add #{struct_reg}, #{8*(i-1)}\n"
            ret = env\fresh_local "member"
            code ..= "#{ret} =#{member_type.abi_type} load#{member_type.base_type} #{loc}\n"
            return ret,code
        elseif t.__class == Types.Range
            index_type = get_type(@[2])
            -- TODO: Slice ranges
            assert_node index_type == Types.Int, @[2], "Index is #{index_type} instead of Int"
            range_reg,code = env\to_reg @[1]
            index_reg,index_code = env\to_reg @[1]
            code ..= index_code
            ret = env\fresh_local "range.nth"
            code ..= "#{ret} =l call $range_nth(l #{range_reg}, l #{index_reg})\n"
            return ret, code
        elseif t == Types.String
            index_type = get_type(@[2])
            str,code = env\to_reg @[1]
            index_reg,index_code = env\to_reg @[2]
            code ..= index_code
            if index_type == Types.Int -- Get nth character as an Int
                char = env\fresh_local "char"
                code ..= "#{char} =l call $bl_string_nth_char(l #{str}, l #{index_reg})\n"
                -- code ..= "#{char} =l add #{str}, #{index_reg}\n"
                -- code ..= "#{char} =l sub #{char}, 1\n"
                -- code ..= "#{char} =l loadub #{char}\n"
                return char, code
            elseif index_type == Types.Range -- Get a slice of the string
                slice = env\fresh_local "slice"
                code ..= "#{slice} =l call $bl_string_slice(l #{str}, l #{index_reg})\n"
                return slice, code
            else
                assert_node false, @[2], "Index is #{index_type} instead of Int or Range"
        else
            assert_node false, @[1], "Indexing is only valid on lists and structs, not #{t}"
    List: (env)=>
        if #@ == 0
            list = env\fresh_local "list.empty"
            code = "#{list} =l call $bl_empty_list()\n"
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
        code ..= "#{list} =l call $bl_list_new(l 0, l 0, l #{#@}, l #{buf})\n"
        return list, code
    Range: (env)=>
        range = env\fresh_local "range"
        first_reg,code = env\to_reg @first[1]
        last_reg,last_code = env\to_reg @last[1]
        code ..= last_code
        if @next
            next_reg,next_code = env\to_reg @next[1]
            code ..= next_code
            code ..= "#{range} =l call $range_new3(l #{first_reg}, l #{next_reg}, l #{last_reg})\n"
        else
            code ..= "#{range} =l call $range_new2(l #{first_reg}, l #{last_reg})\n"
        return range, code
    Or: (env)=>
        true_label = env\fresh_label "or.true"
        done_label = env\fresh_label "or.end"
        code = ""
        for val in *@
            assert_node get_type(val) == Types.Bool, val, "Expected Bool here, but got #{get_type val}"
            val_reg, val_code = env\to_reg val
            false_label = env\fresh_label "or.false"
            code ..= "#{val_code}jnz #{val_reg}, #{true_label}, #{false_label}\n#{false_label}\n"
        ret_reg = env\fresh_local "any"
        code ..= "#{ret_reg} =#{Types.Bool.base_type} copy 0\njmp #{done_label}\n#{true_label}\n#{ret_reg} =#{Types.Bool.base_type} copy 1\n#{done_label}\n"
        return ret_reg, code
    And: (env)=>
        false_label = env\fresh_label "and.false"
        done_label = env\fresh_label "and.end"
        code = ""
        for val in *@
            assert_node get_type(val) == Types.Bool, val, "Expected Bool here, but got #{get_type val}"
            val_reg, val_code = env\to_reg val
            true_label = env\fresh_label "and.true"
            code ..= "#{val_code}jnz #{val_reg}, #{true_label}, #{false_label}\n#{true_label}\n"
        ret_reg = env\fresh_local "any"
        code ..= "#{ret_reg} =#{Types.Bool.base_type} copy 1\njmp #{done_label}\n#{false_label}\n#{ret_reg} =#{Types.Bool.base_type} copy 0\n#{done_label}\n"
        return ret_reg, code
    Xor: (env)=>
        for val in *@
            assert_node get_type(val) == Types.Bool, val, "Expected Bool here, but got #{get_type val}"
        return infixop @, env, "xor"
    Add: (env)=>
        t = get_type(@)
        if t == Types.Int or t == Types.Float
            return infixop @, env, "add"
        elseif t == Types.String
            return infixop @, env, (ret,lhs,rhs)->
                "#{ret} =l call $bl_string_append_string(l #{lhs}, l #{rhs})\n"
        elseif t.__class == Types.List
            return infixop @, env, (ret,lhs,rhs)->
                "#{ret} =l call $bl_list_concat(l #{lhs}, l #{rhs})\n"
        elseif t.__class == Types.Struct
            -- Pairwise
            error "Not impl"
        else
            assert_node false, @, "Addition is not supported for #{t}"
    Sub: (env)=>
        t = get_type(@)
        if t == Types.Int or t == Types.Float
            return infixop @, env, "sub"
        elseif t == Types.String
            -- Concat
            error "Not impl"
        elseif t.__class == Types.Struct
            -- Pairwise
            error "Not impl"
        else
            assert_node false, @, "Subtraction is not supported for #{t}"
    Mul: (env)=>
        t = get_type(@)
        if t == Types.Int or t == Types.Float
            return infixop @, env, "mul"
        elseif t.__class == Types.Struct
            -- Dot product
            error "Not impl"
        else
            assert_node false, @, "Multiplication is not supported for #{t}"
    Div: (env)=>
        t = get_type(@)
        if t == Types.Int or t == Types.Float
            return infixop @, env, "div"
        else
            assert_node false, @, "Division is not supported for #{t}"
    Mod: (env)=>
        t = get_type(@)
        if t == Types.Int or t == Types.Float
            lhs_reg,code = env\to_reg @[1]
            rhs_reg,rhs_code = env\to_reg @[2]
            code ..= rhs_code
            ret = env\fresh_local "remainder"
            if t == Types.Float
                code ..= "#{ret} =d call $sane_fmod(d #{lhs_reg}, d #{rhs_reg})\n"
            else
                code ..= "#{ret} =l call $sane_lmod(l #{lhs_reg}, l #{rhs_reg})\n"
            return ret, code
        else
            assert_node false, @, "Modulus is not supported for #{t}"
    Less: (env)=>
        t = get_type(@[1])
        if t == Types.Int or t == Types.String
            return comparison @, env, "csltl"
        elseif t == Types.Float
            return comparison @, env, "cltd"
        else assert_node false, @, "Comparison is not supported for #{t}"
    LessEq: (env)=>
        t = get_type(@[1])
        if t == Types.Int or t == Types.String
            return comparison @, env, "cslel"
        elseif t == Types.Float
            return comparison @, env, "cled"
        else assert_node false, @, "Comparison is not supported for #{t}"
    Greater: (env)=>
        t = get_type(@[1])
        if t == Types.Int or t == Types.String
            return comparison @, env, "csgtl"
        elseif t == Types.Float
            return comparison @, env, "cgtd"
        else assert_node false, @, "Comparison is not supported for #{t}"
    GreaterEq: (env)=>
        t = get_type(@[1])
        if t == Types.Int or t == Types.String
            return comparison @, env, "csgel"
        elseif t == Types.Float
            return comparison @, env, "cged"
        else assert_node false, @, "Comparison is not supported for #{t}"
    Equal: (env)=> comparison @, env, "ceql"
    NotEqual: (env)=> comparison @, env, "cnel"
    TernaryOp: (env)=>
        cond_reg,code = env\to_reg @condition[1]
        true_reg,true_code = env\to_reg @ifTrue[1]
        false_reg,false_code = env\to_reg @ifFalse[1]
        true_label = env\fresh_label "ternary.true"
        false_label = env\fresh_label "ternary.false"
        end_label = env\fresh_label "ternary.end"
        ret_reg = env\fresh_local "ternary.result"
        code ..= "jnz #{cond_reg}, #{true_label}, #{false_label}\n"
        code ..= "#{true_label}\n#{true_code}#{ret_reg} =#{get_type(@ifTrue[1]).base_type} copy #{true_reg}\njmp #{end_label}\n"
        code ..= "#{false_label}\n#{false_code}#{ret_reg} =#{get_type(@ifFalse[1]).base_type} copy #{false_reg}\njmp #{end_label}\n"
        code ..= "#{end_label}\n"
        return ret_reg, code
    Pow: (env)=>
        t = get_type @base[1]
        base_reg, base_code = env\to_reg @base
        exponent_reg, exponent_code = env\to_reg @exponent
        ret_reg = env\fresh_local "result"
        if t == Types.Int
            return ret_reg, "#{base_code}#{exponent_code}#{ret_reg} =l call $ipow(l #{base_reg}, l #{exponent_reg})\n"
        else
            return ret_reg, "#{base_code}#{exponent_code}#{ret_reg} =d call $pow(d #{base_reg}, d #{exponent_reg})\n"

    FnCall: (env, skip_ret=false)=>
        code = ""
        local fn_type, fn_reg
        target_sig = "(#{concat [tostring(get_type(a)) for a in *@args], ","})"
        fn_type = get_type @fn[1]
        fn_reg,fn_code = env\to_reg @fn
        code ..= fn_code

        if fn_type
            assert_node fn_type and fn_type.__class == Types.FnType, @fn[1], "This is not a function, it's a #{fn_type}"

        args = {}
        for arg in *@args
            arg_reg, arg_code = env\to_reg arg
            code ..= arg_code
            table.insert args, "#{get_type(arg).abi_type} #{arg_reg}"

        if skip_ret
            return nil, "#{code}call #{fn_reg}(#{concat args, ", "})\n"

        ret_reg = env\fresh_local "return"
        ret_type = fn_type and fn_type.return_type or get_type(@)
        code ..= "#{ret_reg} =#{ret_type.abi_type} call #{fn_reg}(#{concat args, ", "})\n"
        return ret_reg, code

    Lambda: (env)=>
        assert_node @__register, @, "Unreferenceable lambda"
        return @__register,""

    Struct: (env)=>
        t = get_type @
        struct_size = 8*#t.members
        ret = env\fresh_local "#{t.name\lower!}"
        code = "#{ret} =#{t.abi_type} call $calloc(l 1, l #{struct_size})\n"
        p = env\fresh_local "#{t.name\lower!}.member.loc"
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
                val_reg,val_code = env\to_reg val
                code ..= val_code
                m_t = get_type val
                code ..= "store#{m_t.base_type} #{val_reg}, #{p}\n"
                
        return ret, code

stmt_compilers =
    Block: (env)=>
        concat([env\compile_stmt(stmt) for stmt in *@], "")
    Declaration: (env)=>
        varname = "%#{@var[0]}"
        assert_node not env.used_names[varname], @var, "Variable being shadowed: #{varname}"
        env.used_names[varname] = true
        if @type
            decl_type = Types.parse_type @type[1]
            value_type = get_type @value[1]
            assert_node value_type, @value[1], "Can't infer the type of this value"
            assert_node value_type\is_a(decl_type), @value[1], "Value is type #{value_type}, not declared type #{decl_type}"
        return store_to @var[1], @value[1], env
    Assignment: (env)=>
        var_type = get_type @[1]
        value_type = get_type @[2]
        assert_node value_type\is_a(var_type), @[2], "Value is type #{value_type}, but it's being assigned to something with type #{var_type}"
        return store_to @[1], @[2], env
    AddUpdate: updater "add"
    SubUpdate: updater "sub"
    MulUpdate: updater "mul"
    DivUpdate: updater "div"
    OrUpdate: updater "or"
    XorUpdate: updater "xor"
    AndUpdate: updater "and"
    AppendUpdate: (env)=>
        lhs_type = get_type @[1]
        rhs_type = get_type @[2]
        if lhs_type == Types.String
            make_rhs = (lhs_reg)->
                fn_name = env\get_concat_fn rhs_type
                appended = env\fresh_local "str.appended"
                rhs_reg,code = env\to_reg @[2]
                code ..= "#{appended} =l call #{fn_name}(l #{lhs_reg}, #{rhs_type.base_type} #{rhs_reg})\n"
                return rhs_type,appended,code
            return store_to @[1], make_rhs, env
        elseif lhs_type.__class == Types.ListType
            assert_node rhs_type == lhs_type.item_type, @[2], "You can't append a #{rhs_type} to a list of #{lhs_type.item_type}s"
            make_rhs = (lhs_reg)->
                fn_name = env\get_concat_fn rhs_type
                appended = env\fresh_local "str.appended"
                rhs_reg,code = env\to_reg @[2]
                if rhs_type.base_type == "d"
                    tmp = env\fresh_local "interp.int"
                    code ..= "#{tmp} =l cast #{rhs_reg}\n"
                    rhs_reg = tmp
                code ..= "#{appended} =l call $bl_list_append(l #{lhs_reg}, l #{rhs_reg})\n"
                return rhs_type,appended,code
            return store_to @[1], make_rhs, env
        else
            assert_node false, @[1], "Only Lists and Strings can be appended to, not #{lhs_type}"
    FnDecl: (env)=> ""
    Pass: (env)=> ""
    TypeDeclaration: (env)=> ""
    FnCall: (env)=>
        _, code = env\to_reg @, true
        code = code\gsub("[^\n]- (call [^\n]*\n)$", "%1")
        return code
    Return: (env)=>
        if @[1]
            reg, code = env\to_reg @[1]
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
            code ..= "jnz #{r}, #{true_label}, #{false_label}\n#{true_label}\n"
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
        t = get_type @what[1]
        what_reg,code = env\to_reg @what[1]
        end_label = env\fresh_label "when.end"
        next_case = env\fresh_label "when.case"
        next_body = env\fresh_label "when.body"
        match_reg = env\fresh_local "when.matches"
        code ..= "jmp #{next_case}\n"
        for branch in *@branches
            for case in *branch.cases
                assert_node get_type(case)\is_a(t), case, "'when' value is not a #{t}"
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

        cond_reg,cond_code = env\to_reg @condition[1]
        code = "jmp #{cond_label}\n#{cond_label}\n"
        code ..= cond_code
        code ..= "jnz #{cond_reg}, #{body_label}, #{end_label}\n"
        code ..= "#{body_label}\n#{env\compile_stmt @body[1]}"
        if @between
            code ..= cond_code
            unless has_jump\match(code)
                code ..= "jnz #{cond_reg}, #{between_label}, #{end_label}\n"
            code ..= "#{between_label}\n#{env\compile_stmt @between[1]}"
            unless has_jump\match(code)
                code ..= "jmp #{body_label}\n"
        else
            unless has_jump\match(code)
                code ..= "jmp #{cond_label}\n"
        code ..= "#{end_label}\n"
        return code
    For: (env)=>
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

        body_label = env\fresh_label "for.body"
        between_label = env\fresh_label "for.between"
        noskip_label = env\fresh_label "for.noskip"
        skip_label = env\fresh_label "for.skip"
        end_label = env\fresh_label "for.end"

        for skip in coroutine.wrap(-> each_tag(@, "Skip"))
            if not skip.target or skip.target[0] == "for" or (@var and skip.target[0] == @var[0]) or (@index and skip.target[0] == @index[0])
                skip.jump_label = skip_label

        for stop in coroutine.wrap(-> each_tag(@, "Stop"))
            if not stop.target or stop.target[0] == "for" or (@var and stop.target[0] == @var[0]) or (@index and stop.target[0] == @index[0])
                stop.jump_label = end_label

        i = env\fresh_local "i"
        len = env\fresh_local "len"

        list_reg,code = env\to_reg @iterable[1]
        code ..= "#{i} =l copy 1\n"
        if list_type == Types.Range
            code ..= "#{len} =l call $range_len(l #{list_reg})\n"
        else
            code ..= "#{len} =l loadl #{list_reg}\n"
        finished = env\fresh_local "for.finished"
        code ..= "#{finished} =l csgtl #{i}, #{len}\n"
        code ..= "jnz #{finished}, #{end_label}, #{body_label}\n"
        code ..= "#{body_label}\n"
        if @index
            index_reg = @index[1].__register
            env.used_names[index_reg] = true
            code ..= "#{index_reg} =l copy #{i}\n"
        if @var
            var_reg = @var[1].__register
            env.used_names[var_reg] = true
            if list_type == Types.Range
                code ..= "#{var_reg} =l call $range_nth(l #{list_reg}, l #{i})\n"
            else
                if list_type.item_type.base_type == "d"
                    tmp = env\fresh_local "item.int"
                    code ..= "#{tmp} =l call $bl_list_nth(l #{list_reg}, l #{i})\n"
                    code ..= "#{var_reg} =#{list_type.item_type.abi_type} cast #{tmp}\n"
                else
                    code ..= "#{var_reg} =#{list_type.item_type.abi_type} call $bl_list_nth(l #{list_reg}, l #{i})\n"
        code ..= "#{env\compile_stmt @body[1]}"
        unless has_jump\match(code)
            code ..= "jmp #{noskip_label}\n"
        code ..= "#{noskip_label}\n"
        code ..= "#{i} =l add #{i}, 1\n"
        code ..= "#{finished} =l csgtl #{i}, #{len}\n"
        if @between
            code ..= "jnz #{finished}, #{end_label}, #{between_label}\n"
            code ..= "#{between_label}\n#{env\compile_stmt @between[1]}"
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
        
store_to = (val, env, ...)=>
    switch @__tag
        when "Var"
            assert_node @__register, @, "Undefined variable"
            val_type, reg, code = if type(val) == 'function'
                val(@__register)
            else
                get_type(val), env\to_reg(val, ...)
            return "#{code}#{@__register} =#{val_type.base_type} copy #{reg}\n"
        when "IndexedTerm"
            t = get_type @[1]
            if t.__class == Types.ListType
                assert_node false, @, "Lists are immutable"
                -- assert_node get_type(@[2]) == Types.Int, @[2], "Index is: #{get_type @[2]} instead of Int"
                -- list_reg,list_code = env\to_reg @[1]
                -- index_reg,index_code = env\to_reg @[2]
                -- val_type,val_reg,val_code = if type(val) == 'function'
                --     val(list_reg)
                -- else
                --     get_type(val), env\to_reg(val)
                -- code = list_code..index_code..val_code
                -- code ..= "call $bl_list_set_nth#{t.item_type.base_type}(l #{list_reg}, l #{index_reg}, #{t.item_type.base_type} #{val_reg})\n"
                -- return code
            elseif t.__class == Types.StructType
                assert_node @[2].__tag == "Var", @[2], "Structs can only be indexed by member"
                member_name = @[2][0]
                assert_node t.members_by_name[member_name], @[2], "Not a valid struct member of #{t}"
                struct_reg,struct_code = env\to_reg @[1]
                i = t.members_by_name[member_name].index
                member_type = t.members_by_name[member_name].type
                code = struct_code
                dest = env\fresh_local "member.loc"
                code ..= "#{dest} =l add #{struct_reg}, #{8*(i-1)}\n"
                val_type,val_reg,val_code = if type(val) == 'function'
                    val(list_reg)
                else
                    get_type(val), env\to_reg(val)
                code ..= val_code
                code ..= "store#{member_type.item_type.base_type} #{val_reg}, #{dest}\n"
                return code
            else
                assert_node false, @[1], "Indexing is only valid on a list or struct, but this is a #{t}"
        else
            error "Not implemented: store to #{@__tag}"

compile_prog = (ast, filename)->
    env = Environment!
    return env\compile_program(ast, filename)

return {:compile_prog}
