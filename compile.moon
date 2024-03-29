Types = require 'types'
bp = require 'bp'
import assign_all_types, get_type, parse_type, bind_var, bind_type from require('typecheck')
import log, viz, id, node_assert, node_error, context_err, each_tag from require 'util'
import Measure, register_unit_alias from require 'units'
ListMethods = require 'list_methods'
concat = table.concat

has_jump = bp.compile('^_("jmp"/"jnz"/"ret")\\b ..$ $$')

local stmt_compilers, expr_compilers, CodeBuilder

nonnil_eq = (t1, t2)-> (t1.nonnil or t1) == (t2.nonnil or t2)

class Environment
    new: (@filename)=>
        @strings = {}
        @used_names = {}
        @dups = setmetatable({}, {__index:->0})
        @type_code = @new_code!
        @string_code = @new_code!
        @fn_code = @new_code!
        @main_code = @new_code!
        @tostring_funcs = {}

    new_code: (...)=> CodeBuilder(@, ...)

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

    get_string_reg: (str, suggestion="str")=>
        unless @strings[str]
            name = @fresh_global suggestion
            @strings[str] = name
            @string_code\add "data #{name} = #{@string_as_data str}\n"
        return @strings[str]

    string_as_data: (str)=>
        chunks = tostring(str)\gsub('[^ !#-[^-~%]]', (c)->"\",b #{c\byte(1)},b\"")\gsub("\n", "\\n")
        return "{b\"#{chunks}\",b 0}\n"

    declare_function: (fndec)=>
        @fn_code\declare_function(fndec)

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

        key = tostring(t)
        if @tostring_funcs[key]
            return @tostring_funcs[key],false

        typename = t\id_str!
        fn_name = @fresh_global "tostring.#{typename}"
        @tostring_funcs["#{t}"] = fn_name

        reg = @fresh_local typename\lower()
        -- To avoid stack overflow on self-referencing structs, pass a callstack
        -- as a stack-allocated linked list and check before recursing
        callstack = "%callstack"
        code = @new_code!
        code\add "function l #{fn_name}(#{t.base_type} #{reg}, l #{callstack}) {\n"
        code\add "@start\n"

        -- TODO: Check for recursive lists/tables? It probably doesn't matter,
        -- since the type system currently only allows recursive types for
        -- structs, not lists/tables, so cycles can only be achieved with structs.

        dest = @fresh_local "string"
        if t\works_like_a(Types.NilType)
            code\add "#{dest} =l call $bl_string(l #{@get_string_reg("nil", "nil")})\n"
        elseif t\works_like_a(Types.Abort)
            code\add "#{dest} =l call $bl_string(l #{@get_string_reg("Abort", "Abort")})\n"
        elseif t\works_like_a(Types.OptionalType)
            nil_label,nonnil_label,end_label = @fresh_labels "optional.nil", "optional.nonnil", "optional.end"
            code\check_nil t, reg, nonnil_label, nil_label

            code\add_label nil_label
            code\add "#{dest} =l call $bl_string(l #{@get_string_reg("nil", "nil")})\n"
            code\add "jmp #{end_label}\n"

            code\add_label nonnil_label
            fn = @get_tostring_fn t.nonnil, scope
            code\add "#{dest} =l call #{fn}(#{t.nonnil.base_type} #{reg}, l #{callstack})\n"
            code\add "jmp #{end_label}\n"

            code\add "#{end_label}\n"
        elseif t == Types.Value or t == Types.Value32 or t == Types.Value16 or t == Types.Value8
            code\add "#{dest} =l call $bl_string(l #{@get_string_reg("<#{t.name}>", t.name)})\n"
        elseif t\works_like_a(Types.EnumType)
            init_fields,fields_exist = @fresh_labels "make_fields", "fields_exist"
            tmp = @fresh_local "fieldname"
            code\add "#{tmp} =l loadl $#{t\id_str!}.fields\n"
            code\add "jnz #{tmp}, #{fields_exist}, #{init_fields}\n"
            code\add_label init_fields
            for field in *t.fields
                -- str = @fresh_local "str"
                -- code\add "#{str} =l call $bl_string(l #{@get_string_reg "#{t.name}.#{field}", "#{t.name}.#{field}"})\n"
                code\add "#{tmp} =l add $#{t\id_str!}.fields, #{8*t.field_values[field]}\n"
                code\add "storel #{@get_string_reg "#{t.name}.#{field}", "#{t.name}.#{field}"}, #{tmp}\n"
            code\add "jmp #{fields_exist}\n"

            code\add "#{fields_exist}\n"
            code\add "#{reg} =l mul #{reg}, 8\n"
            code\add "#{tmp} =l add $#{t\id_str!}.fields, #{reg}\n"
            code\add "#{dest} =l loadl #{tmp}\n"
        elseif t\works_like_a(Types.ListType)
            buf = @fresh_local "buf"
            code\add "#{buf} =l call $CORD_from_char_star(l #{@get_string_reg "[", "lsq"})\n"
            item_reg = @fresh_local "item"
            code\add_for_loop {
                type:t, iter_reg:reg, val_reg:item_reg,
                make_body: ->
                    item_str = @fresh_local "item.string"
                    fn = @get_tostring_fn t.item_type, scope
                    return @new_code "#{item_str} =l call #{fn}(#{t.item_type.base_type} #{item_reg}, l #{callstack})\n",
                        "#{buf} =l call $CORD_cat(l #{buf}, l #{item_str})\n"
                make_between: ->
                    return @new_code "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg ", ", "comma.space"})\n"
            }

            code\add "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg "]", "rsq"})\n"
            code\add "#{buf} =l call $CORD_to_const_char_star(l #{buf})\n"
            code\add "#{dest} =l call $bl_string(l #{buf})\n"

        elseif t\works_like_a(Types.TableType)
            buf = @fresh_local "buf"
            code\add "#{buf} =l call $CORD_from_char_star(l #{@get_string_reg "{", "lbracket"})\n"

            key_reg,value_reg = @fresh_locals "key","value"
            code\add_for_loop {
                type: t, iter_reg:reg, :key_reg, :value_reg,
                make_body: ->
                    key_str = @fresh_local "key.string"
                    fn = @get_tostring_fn t.key_type, scope
                    local code
                    code = @new_code "#{key_str} =l call #{fn}(#{t.key_type.base_type} #{key_reg}, l #{callstack})\n"
                    code\add "#{buf} =l call $CORD_cat(l #{buf}, l #{key_str})\n"
                    code\add "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg "=", "equals"})\n"
                    value_str = @fresh_local "value.string"
                    fn = @get_tostring_fn t.value_type, scope
                    code\add "#{value_str} =l call #{fn}(#{t.value_type.base_type} #{value_reg}, l #{callstack})\n"
                    code\add "#{buf} =l call $CORD_cat(l #{buf}, l #{value_str})\n"
                    return code
                make_between: ->
                    return "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg ", ", "comma"})\n"
            }

            code\add "#{buf} =l call $CORD_cat(l #{buf}, l #{@get_string_reg "}", "rbracket"})\n"
            code\add "#{buf} =l call $CORD_to_const_char_star(l #{buf})\n"
            code\add "#{dest} =l call $bl_string(l #{buf})\n"

        elseif t\works_like_a(Types.StructType)
            if t.name\match "^Tuple%.[0-9]+$"
                code\add "#{dest} =l call $CORD_from_char_star(l #{@get_string_reg("{", "curly")})\n"
            else
                code\add "#{dest} =l call $CORD_from_char_star(l #{@get_string_reg("#{t.name}{", "#{t\id_str!}.name")})\n"

            -- Check callstack for cyclical references
            cycle_next,cycle_check,cycle_found,cycle_notfound,conclusion = @fresh_labels(
                "cycle.check.next", "cycle.check", "cycle.found", "cycle.notfound", "tostring.conclusion")

            walker = @fresh_local "cycle.walker"
            code\add "#{walker} =l copy #{callstack}\n"
            code\add "jmp #{cycle_next}\n"

            code\add_label cycle_next
            code\add "jnz #{walker}, #{cycle_check}, #{cycle_notfound}\n"

            code\add_label cycle_check
            cycle_parent = @fresh_local "cycle.parent"
            code\add "#{cycle_parent} =l add #{walker}, 8\n"
            code\add "#{cycle_parent} =l loadl #{cycle_parent}\n"
            code\add "#{walker} =l loadl #{walker}\n"
            wasfound = @fresh_local "cycle.wasfound"
            code\add "#{wasfound} =l ceql #{cycle_parent}, #{reg}\n"
            code\add "jnz #{wasfound}, #{cycle_found}, #{cycle_next}\n"

            code\add_label cycle_found
            code\add "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg "...", "ellipsis"})\n"
            code\add "jmp #{conclusion}\n"

            code\add_label cycle_notfound
            new_callstack = @fresh_local "new.callstack"
            code\add "#{new_callstack} =l alloc8 #{2*8}\n"
            code\add "storel #{callstack}, #{new_callstack}\n"
            p = @fresh_local "p"
            code\add "#{p} =l add #{new_callstack}, 8\n"
            code\add "storel #{reg}, #{p}\n"
            for i,mem in ipairs t.sorted_members
                if i > 1
                    code\add "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg ", ", "comma.space"})\n"

                member_loc = @fresh_local "#{t\id_str!\lower!}.#{mem.name}.loc"
                code\add "#{member_loc} =l add #{reg}, #{mem.offset}\n"
                member_reg = @fresh_local "#{t\id_str!\lower!}.#{mem.name}"
                if mem.inline
                    code\add "#{member_reg} =#{mem.type.base_type} copy #{member_loc}\n"
                else
                    code\add "#{member_reg} =#{mem.type.base_type} #{mem.type.load} #{member_loc}\n"

                if mem.name
                    code\add "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg("#{mem.name}=")})\n"

                member_str = @fresh_local "#{t\id_str!\lower!}.#{mem.name}.string"
                fn = @get_tostring_fn mem.type, scope
                code\add "#{member_str} =l call #{fn}(#{mem.type.base_type} #{member_reg}, l #{new_callstack})\n"

                code\add "#{dest} =l call $CORD_cat(l #{dest}, l #{member_str})\n"
            code\add "jmp #{conclusion}\n"

            code\add_label conclusion
            code\add "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg "}", "close.curly"})\n"
            code\add "#{dest} =l call $CORD_to_const_char_star(l #{dest})\n"
            code\add "#{dest} =l call $bl_string(l #{dest})\n"

        elseif t\works_like_a(Types.UnionType)
            init_fields,fields_exist = @fresh_labels "make_fields", "fields_exist"
            tmp = @fresh_local "fieldname"
            code\add "#{tmp} =l loadl $#{t\id_str!}.member_names\n"
            code\add "jnz #{tmp}, #{fields_exist}, #{init_fields}\n"
            code\add_label init_fields
            for name,info in pairs t.members
                code\add "#{tmp} =l add $#{t\id_str!}.member_names, #{(info.index-1)*8}\n"
                code\add "storel #{@get_string_reg "#{t.name}.#{name}", "#{t.name}.#{name}"}, #{tmp}\n"
            code\add "jmp #{fields_exist}\n"

            code\add "#{fields_exist}\n"

            tag,offset,tmp,name,is_tag = @fresh_locals "tag","offset","tmp","name","is_tag"
            val_loc = @fresh_local "val.loc"
            code\add "#{tag} =l loadl #{reg}\n"
            code\add "#{offset} =l sub #{tag}, 1\n"
            code\add "#{offset} =l mul #{offset}, 8\n"
            code\add "#{name} =l add $#{t\id_str!}.member_names, #{offset}\n"
            code\add "#{dest} =l loadl #{name}\n"
            code\add "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg '(', "lparen"})\n"
            code\add "#{val_loc} =l add #{reg}, 8\n"
            next_check,done_label = @fresh_labels "check.member","done"
            for name,info in pairs t.members
                check,next_check = next_check, @fresh_label "check.member"
                found_member = @fresh_label "found.member"
                code\add_label check
                code\add "#{is_tag} =w ceql #{tag}, #{info.index}\n"
                code\add "jnz #{is_tag}, #{found_member}, #{next(t.members, name) and next_check or done_label}\n"

                code\add_label found_member
                val = @fresh_local "val"
                code\add "#{val} =#{info.type.base_type} #{info.type.load} #{val_loc}\n"
                code\add "#{tmp} =l call #{@get_tostring_fn info.type, scope}(#{info.type.base_type} #{val}, l #{callstack})\n"
                code\add "#{dest} =l call $CORD_cat(l #{dest}, l #{tmp})\n"
                code\add "jmp #{done_label}\n"

            code\add "#{done_label}\n"
            code\add "#{dest} =l call $CORD_cat(l #{dest}, l #{@get_string_reg ')', "rparen"})\n"
            code\add "#{dest} =l call $CORD_to_const_char_star(l #{dest})\n"
            code\add "#{dest} =l call $bl_string(l #{dest})\n"

        elseif t\works_like_a(Types.FnType)
            code\add "#{dest} =l call $bl_string(l #{@get_string_reg("#{t}")})\n"
        elseif t\works_like_a(Types.MeasureType)
            code\add "#{dest} =l call $bl_tostring_float(d #{reg})\n"
            code\add "#{dest} =l call $bl_string_append_string(l #{dest}, l #{@get_string_reg("<"..t.units..">", "units")})\n"
        elseif t\works_like_a(Types.Pointer)
            code\add "#{dest} =l call $bl_tostring_hex(l #{reg})\n"
        else
            error "Unsupported tostring type: #{t\verbose_type!}"

        code\add "ret #{dest}\n"
        code\add "}\n"
        indented_code = tostring(code)\gsub("[^\n]+", =>((@\match("^[@}]") or @\match("^function")) and @ or "  "..@))
        @fn_code\add indented_code
        return fn_name

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

        @type_code = @new_code "type :Range = {l,l,l}\n"

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
            @type_code\add "data #{type_name} = #{@string_as_data tostring(t.type)}\n"
            typedecl.name.__register = type_name

        -- Enum field names
        for e in coroutine.wrap(-> each_tag(ast, "EnumDeclaration"))
            t = get_type(e)
            enum_t = t.type
            fieldnames = "$#{enum_t\id_str!}.fields"
            @type_code\add "data #{fieldnames} = {#{("l 0,")\rep(enum_t.next_value)}}\n"

        -- Union field names
        for u in coroutine.wrap(-> each_tag(ast, "UnionDeclaration", "UnionType"))
            t = get_type(u, true).type
            assert t\is_a(Types.UnionType), "#{t}"
            fieldnames = "$#{t\id_str!}.member_names"
            @type_code\add "data #{fieldnames} = {#{concat ["l 0" for _ in pairs t.members], ", "}}\n"

        is_file_scope = (scope)->
            while scope
                return true if scope == ast
                switch scope.__tag
                    when "FnDecl","Lambda","Macro","For","ConvertDecl"
                        return false
                scope = scope.__parent
            error("Unexpectedly reached a node not parented to top-level AST")

        file_scope_vars = {}

        -- Struct/union static variables
        for decl in coroutine.wrap(-> each_tag(ast, "UnionDeclaration", "StructDeclaration"))
            t = get_type(decl, true).type
            for staticvar in *decl
                continue unless staticvar.__tag == "Declaration"
                staticvar.var.__location = @fresh_global "#{t\id_str!}.#{staticvar.var[0]}"
                table.insert file_scope_vars, staticvar.var

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

        body_code = @new_code!
        body_code\add_stmt ast

        code = @new_code "# Source file: #{filename}\n\n"
        code\add @type_code if #@type_code.chunks > 0
        code\add @string_code if #@string_code.chunks > 0
        code\add "data $args = {l 0}\n"
        code\add "data $exports = {#{concat [get_type(e).base_type.." 0" for e in *exports], ","}}\n"
        for var in *naked_imports
            code\add "data #{var.__location} = {#{get_type(var).base_type} 0}\n"
        for var in *file_scope_vars
            code\add "data #{var.__location} = {#{get_type(var).base_type} 0}\n"
        code\add "#{@fn_code}\n" if #@fn_code.chunks > 0

        code\add "export function l $load() {\n"
        code\add "@start\n"

        -- TODO: check for top-level returns and error if they exist
        indented_code = tostring(body_code)\gsub("[^\n]+", =>((@\match("^[@}]") or @\match("^function")) and @ or "  "..@))
        code\add indented_code

        for fndec in coroutine.wrap(-> each_tag(ast, "FnDecl"))
            if fndec.name[0] == "main" and #fndec.args == 0
                code\add "  call #{fndec.name.__register}()\n"
                break

        for i,e in ipairs exports
            var_reg,var_code = @to_reg e
            code\add var_code
            dest = @fresh_local "export.loc"
            code\add "  #{dest} =l add $exports, #{(i-1)*8}\n"
            code\add "  storel #{var_reg}, #{dest}\n"
        code\add "  ret $exports\n"
        code\add "}\n"

        code\add "export function w $main(w %argc, l %argv) {\n"
        code\add "@start\n"
        code\add "  %argc2 =l extsw %argc\n"
        code\add "  %args.size =l mul %argc2, 8\n"
        code\add "  %args.items =l call $gc_alloc(l %args.size)\n"
        code\add "  call $memcpy(l %args.items, l %argv, l %args.size)\n"
        code\add "  %args =l call $gc_alloc(l 16)\n"
        code\add "  storel %argc2, %args\n"
        code\add "  storel %args, $args\n"
        code\add "  %args =l add %args, 8\n"
        code\add "  storel %args.items, %args\n"
        code\add "  call $load()\n"
        code\add "  ret 0\n"
        code\add "}\n"
        source_chunks = ast[0]\gsub('[^ !#-[^-~]', (c)->"\",b #{c\byte(1)},b\"")\gsub("\n", "\\n")
        code\add "\nexport data $source = {b\"#{source_chunks}\",b 0}\n"
        return code


class CodeBuilder
    new: (@env, ...)=>
        @chunks = {}
        @add ...

    add: (...)=>
        for i=1,select("#",...)
            table.insert(@chunks, (select(i, ...)))
        return @

    new_code: (...)=> @env\new_code(...)

    __tostring: => table.concat([tostring(chunk) for chunk in *@chunks])

    ends_with_jump: =>
        last = @chunks[#@chunks]
        if type(last) == 'table'
            return last\ends_with_jump!
        elseif type(last) == 'string'
            return has_jump\match(last)

    get_string_reg: (...)=> @env\get_string_reg(...)
    get_tostring_fn: (...)=> @env\get_tostring_fn(...)
    fresh_name: (...)=> @env\fresh_name(...)
    fresh_local: (...)=> @env\fresh_local(...)
    fresh_locals: (...)=> @env\fresh_locals(...)
    fresh_global: (...)=> @env\fresh_global(...)
    fresh_label: (...)=> @env\fresh_label(...)
    fresh_labels: (...)=> @env\fresh_labels(...)

    add_values: (...)=>
        nodes = {...}
        regs = {}
        for node in *nodes
            assert expr_compilers[node.__tag], "Expression compiler not implemented for #{node.__tag}"
            reg = expr_compilers[node.__tag](@, node)
            table.insert(regs, reg)
        return table.unpack(regs)

    add_value: (...)=> @add_values(...)

    add_label: (label)=> @add label, "\n"

    declare_function: (fndec)=>
        args = ["#{parse_type(arg.type).base_type} #{arg.name.__register}" for arg in *fndec.args]
        if fndec.selfVar
            t = get_type fndec.selfVar, true
            table.insert args, 1, "#{t.base_type} #{fndec.selfVar.__register}"

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

        fn_name = fndec.__register or node_assert fndec.name.__register, fndec, "Function has no name"
        fn_code = @new_code!
        fn_code\add "\nfunction #{ret_type\is_a(Types.Abort) and "" or ret_type.base_type.." "}"
        fn_code\add "#{fn_name}(#{concat args, ", "}) {\n"
        fn_code\add "@start\n"

        body_code = @new_code!

        if fndec.__tag == "Lambda" or fndec.body.__tag != "Block"
            ret_reg = body_code\add_values fndec.body
            body_code\add "ret #{ret_reg}\n"
        else
            body_code\add_stmt fndec.body
        body_code = tostring(body_code)\gsub("[^\n]+", =>(@\match("^%@") and @ or "  "..@))
        fn_code\add body_code
        unless fn_code\ends_with_jump!
            if ret_type\is_a(Types.Abort)
                fn_code\add "  ret\n"
            else
                fn_code\add "  ret 0\n"

        fn_code\add "}\n"
        @add fn_code

    add_stmt: (node)=>
        assert node.__tag, "Not a node: #{viz node}"

        if stmt_compilers[node.__tag]
            stmt_compilers[node.__tag](@, node)
        elseif expr_compilers[node.__tag]
            expr_compilers[node.__tag](@, node)
        else
            node_error node, "Not implemented: #{node.__tag}"

    check_nil: (t, reg, nonnil_label, nil_label)=>
        if t == Types.NilType
            @add "jmp #{nil_label}\n"
        elseif not t\is_a(Types.OptionalType)
            @add "jmp #{nonnil_label}\n"
        elseif t.nil_value == 0
            @add "jnz #{reg}, #{nonnil_label}, #{nil_label}\n"
        elseif t.nonnil.base_type == "d" or t.nonnil.base_type == "s"
            int_val,is_nan = @fresh_locals "int_val","is_nan"
            @add "#{int_val} =l cast #{reg}\n"
            @add "#{is_nan} =w ceql #{int_val}, #{t.nonnil.nil_value} # Check for nil\n"
            @add "jnz #{is_nan}, #{nil_label}, #{nonnil_label}\n"
        else
            tmp = @fresh_local "is.nonnil"
            @add "#{tmp} =w cne#{t.base_type} #{reg}, #{t.nil_value}\njnz #{tmp}, #{nonnil_label}, #{nil_label}\n"

    check_truthiness: (t, reg, truthy_label, falsey_label)=>
        if t\is_a(Types.Bool)
            @add "jnz #{reg}, #{truthy_label}, #{falsey_label}\n"
        elseif t\is_a(Types.NilType)
            @add "jmp #{falsey_label}\n"
        elseif t.base_type == "d"
            tmp = @fresh_local "is.nonnil"
            @add "#{tmp} =l cod #{reg}, d_0.0 # Test for NaN\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
        elseif t.base_type == "s"
            tmp = @fresh_local "is.nonnil"
            @add "#{tmp} =l cos #{reg}, d_0.0 # Test for NaN\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
        elseif t\is_a(Types.OptionalType)
            if t.nonnil\is_a(Types.Bool)
                tmp = @fresh_local "is.true"
                @add "#{tmp} =l ceq#{t.base_type} #{reg}, 1\njnz #{tmp}, #{truthy_label}, #{falsey_label}\n"
            else
                @check_nil t, reg, truthy_label, falsey_label
        else
            @add "jmp #{truthy_label}\n"

    add_for_loop: (args)=>
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

        @add "# For loop:\n"
        if iter_type\works_like_a(Types.TableType)
            @add "#{i} =l copy #{iter_type.key_type.nil_value}\n"
        else
            @add "#{i} =l copy 0\n"
        local list_item
        if iter_type\is_a(Types.Range)
            @add "#{len} =l call $range_len(l #{iter_reg})\n"
        elseif iter_type\is_a(Types.ListType)
            @add "#{len} =l loadl #{iter_reg}\n"
            list_item = @fresh_local "list.item"
            @add "#{list_item} =l add #{iter_reg}, 8\n"
            @add "#{list_item} =l loadl #{list_item}\n"
        elseif iter_type\is_a(Types.TableType)
            len = nil -- Len is not used for tables
        else
            error "Expected an iterable type, not #{iter_type}"
        @add "jmp #{next_label}\n"
        @add_label next_label
        if iter_type\is_a(Types.TableType)
            @add "#{i} =l call $bl_table_next(l #{iter_reg}, l #{i}, l #{iter_type.key_type.nil_value})\n"
            @add "#{is_done} =w ceql #{i}, #{iter_type.key_type.nil_value}\n"
            @add "jnz #{is_done}, #{end_label}, #{body_label}\n"
        else
            @add "#{i} =l add #{i}, 1\n"
            @add "#{is_done} =w csgtl #{i}, #{len}\n"
            @add "jnz #{is_done}, #{end_label}, #{body_label}\n"

        @add_label body_label
        TableMethods = require 'table_methods'
        if iter_type\is_a(Types.TableType)
            if key_reg
                if iter_type.key_type.base_type == "s" or iter_type.key_type.base_type == "d"
                    @add "#{key_reg} =#{iter_type.key_type.base_type} cast #{i}\n"
                else
                    @add "#{key_reg} =#{iter_type.key_type.base_type} copy #{i}\n"

            if value_reg
                value_bits = @fresh_local "value.bits"
                @add "#{value_bits} =l call $bl_table_get(l #{iter_reg}, l #{i}, l #{iter_type.key_type.nil_value}, l #{iter_type.value_type.nil_value})\n"
                if iter_type.value_type.base_type == "s" or iter_type.value_type.base_type == "d"
                    @add "#{value_reg} =#{iter_type.value_type.base_type} cast #{value_bits}\n"
                else
                    @add "#{value_reg} =#{iter_type.value_type.base_type} copy #{value_bits}\n"
        else
            if key_reg
                @add "#{key_reg} =l copy #{i}\n"

            assert value_reg
            if iter_type\is_a(Types.Range)
                -- TODO: optimize to not use function call and just do var=start ... var += step
                @add "#{value_reg} =l call $range_nth(l #{iter_reg}, l #{i})\n"
            else
                @add "#{value_reg} =#{iter_type.item_type.base_type} #{iter_type.item_type.load} #{list_item}\n"
                @add "#{list_item} =l add #{list_item}, #{iter_type.item_type.bytes}\n"

        if filter
            @add_stmt filter

        if make_body
            @add make_body(key_reg, value_reg)
        else
            error "No body"

        -- If we reached this point, no skips
        unless @ends_with_jump!
            if iter_type\is_a(Types.TableType)
                @add "#{i} =l call $bl_table_next(l #{iter_reg}, l #{i}, l #{iter_type.key_type.nil_value})\n"
                @add "#{is_done} =w ceql #{i}, #{iter_type.key_type.nil_value}\n"
                @add "jnz #{is_done}, #{end_label}, #{between_label}\n"
            else
                @add "#{i} =l add #{i}, 1\n"
                @add "#{is_done} =w csgtl #{i}, #{len}\n"
                @add "jnz #{is_done}, #{end_label}, #{between_label}\n"

        @add_label between_label
        if make_between
            @add make_between(key_reg, value_reg)

        unless @ends_with_jump!
            @add "jmp #{body_label}\n"

        @add_label end_label

    add_infix_op: (ast, op)=>
        assert ast.lhs and ast.rhs, "Infix node doesn't have lhs/rhs: #{viz ast}"
        t = get_type ast.lhs
        lhs_reg = @add_values ast.lhs
        ret_reg = @fresh_local "result"
        rhs = ast.rhs
        rhs_type = get_type rhs
        -- node_assert nonnil_eq(rhs_type, t), rhs, "Expected type: #{t} but got type #{rhs_type}"
        rhs_reg = @add_values rhs
        if type(op) == 'string'
            @add "#{ret_reg} =#{t.base_type} #{op} #{lhs_reg}, #{rhs_reg}\n"
        else
            @add op(ret_reg, lhs_reg, rhs_reg)
        return ret_reg

    add_comparison: (ast, cmp)=>
        t1 = get_type ast.lhs
        t2 = get_type ast.rhs
        node_assert t1 == t2, ast, "This comparison is between two different types: `#{t1}` and `#{t2}` which is not allowed"

        lhs_reg, rhs_reg = @add_values ast.lhs, ast.rhs

        result = @fresh_local "comparison"
        if t1\is_a(Types.String)
            tmp = @fresh_local "comparison.i32"
            @add "#{tmp} =w call $strcmp(l #{lhs_reg}, l #{rhs_reg})\n"
            @add "#{result} =w csltw #{tmp}, 0\n"
        else
            @add "#{result} =w #{cmp} #{lhs_reg}, #{rhs_reg}\n"

        return result

    add_repeat_loop: (ast, make_body)=>
        -- Rough breakdown:
        -- jmp @repeat
        -- @repeat
        -- // body code
        -- jmp @repeat.between
        -- // between code
        -- jmp @repeat
        -- @repeat.end
        repeat_label,between_label,end_label = @fresh_labels "repeat", "repeat.between", "repeat.end"

        for skip in coroutine.wrap(-> each_tag(ast, "Skip"))
            if not skip.target or skip.target[0] == "repeat"
                skip.jump_label = repeat_label

        for stop in coroutine.wrap(-> each_tag(ast, "Stop"))
            if not stop.target or stop.target[0] == "repeat"
                stop.jump_label = end_label

        @add "jmp #{repeat_label}\n"
        @add_label repeat_label
        @add_stmt ast.filter if ast.filter
        if make_body
            @add make_body!
        else
            @add_stmt(ast.body)

        if ast.between
            unless @ends_with_jump!
                @add "jmp #{between_label}\n"
            @add_label between_label
            @add_stmt(ast.between)
        unless @ends_with_jump!
            @add "jmp #{repeat_label}\n"
        @add_label end_label

    add_while_loop: (ast, make_body)=>
        -- Rough breakdown:
        -- jmp @while.condition
        -- jnz (condition), @while.body, @while.end
        -- @while.body
        -- // body code
        -- jmp @while.between
        -- // between code
        -- jnz (condition), @while.body, @while.end
        -- @while.end
        cond_label,body_label,between_label,end_label = @fresh_labels "while.condition", "while.body", "while.between", "while.end"

        for skip in coroutine.wrap(-> each_tag(ast, "Skip"))
            if not skip.target or skip.target[0] == "while"
                skip.jump_label = cond_label

        for stop in coroutine.wrap(-> each_tag(ast, "Stop"))
            if not stop.target or stop.target[0] == "while"
                stop.jump_label = end_label

        @add "jmp #{cond_label}\n"

        @add_label cond_label
        cond_reg = @add_values ast.condition
        @add "jnz #{cond_reg}, #{body_label}, #{end_label}\n"

        @add_label body_label
        @add_stmt ast.filter if ast.filter
        if make_body
            @add make_body!
        else
            @add_stmt(ast.body)

        if ast.between
            cond_reg2 = @add_values ast.condition
            unless @ends_with_jump!
                @add "jnz #{cond_reg2}, #{between_label}, #{end_label}\n"
            @add_label between_label
            @add_stmt ast.between
            unless @ends_with_jump!
                @add "jmp #{body_label}\n"
        else
            unless @ends_with_jump!
                @add "jmp #{cond_label}\n"

        @add_label end_label

    set_nil: (t, reg)=>
        if t.base_type == "s" or t.base_type == "d"
            @add "#{reg} =#{t.base_type} cast #{t.nil_value} # Set to nil\n"
        else
            @add "#{reg} =#{t.base_type} copy #{t.nil_value} # Set to nil\n"

expr_compilers =
    Var: (ast)=>
        return ast.__register if ast.__register
        t = get_type(ast)
        if ast.__location
            tmp = @fresh_local "#{ast[0]}.value"
            @add "#{tmp} =#{t.base_type} #{t.load} #{ast.__location}\n"
            return tmp
        elseif t\is_a(Types.TypeValue)
            return @get_string_reg(t.type\verbose_type!, ast[0])
        node_error ast, "This variable is not defined"

    Declaration: (ast)=>
        value_type = get_type ast.value, true
        val_reg = @add_value ast.value
        if ast.var.__register
            @add "#{ast.var.__register} =#{value_type.base_type} copy #{val_reg}\n"
        elseif ast.var.__location
            @add "#{value_type.store} #{val_reg}, #{ast.var.__location}\n"
        else
            node_error @var, "Undefined variable"
        return val_reg

    Int: (ast)=>
        t = get_type(ast, true)
        s = ast[0]\gsub("_","")
        n = if s\match("^0x")
            tonumber(s\sub(3), 16)
        else
            tonumber(s)

        if t\is_a(Types.Num)
            return "d_#{n}"
        elseif t\is_a(Types.Num32)
            return "s_#{n}"

        min,max = -(2^(t.bytes*8-1)), 2^(t.bytes*8-1)-2
        if n == t.nil_value
            node_error ast, "This value is reserved for represeting `nil` and can't be used as an integer. Consider using a larger integer type."
        elseif n > max
            node_error ast, "This value is too large to fit into a #{t.bytes}-byte signed integer (max value: #{math.floor(max)})"
        elseif n < min
            node_error ast, "This value is too small to fit into a #{t.bytes}-byte signed integer (min value: #{math.floor(min)})"
        return "#{n}"

    Float: (ast)=>
        s = ast[0]\gsub("_","")
        t = get_type(ast, true)
        prefix = t\is_a(Types.Num) and "d" or "s"
        return "#{prefix}_#{tonumber(s)}"

    Measure: (ast)=>
        n = tonumber((ast.amount[0]\gsub("_","")))
        m = Measure(n, ast.units[0]\gsub("[<>]",""))
        return "d_#{m.amount}"

    Percent: (ast)=>
        s = ast[0]\gsub("_","")\gsub("%%","")
        return "d_#{tonumber(s)/100.0}"

    Nil: (ast)=>
        child = ast
        parent = ast.__parent
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
                --     nil_reg = @fresh_local "nil"
                --     return nil_reg, "#{nil_reg} =#{t.base_type} cast #{t.nil_value}\n"
                -- else
                return "#{t.nil_value}"

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
                            field_type = node_assert(struct_type.members[i] or struct_type.sorted_members[i], ast, "Not a #{struct_type} field").type
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
                --     nil_reg = @fresh_local "nil"
                --     return nil_reg, "#{nil_reg} =#{t.base_type} cast #{t.nil_value}\n"
                -- else
                return "#{t.nil_value}"
            elseif parent.__tag == "Declaration"
                return "0"

            parent,child = parent.__parent,parent
        return "0"

    Bool: (ast)=> (ast[0] == "yes" and "1" or "0")

    Cast: (ast)=>
        reg = @add_value ast.expr
        cast_type = parse_type ast.type
        actual_type = get_type(ast.expr, true)
        if not actual_type or (actual_type and cast_type.base_type == actual_type.base_type)
            return reg
        c = @fresh_local "casted"
        abt = actual_type.base_type
        cbt = cast_type.base_type
        if actual_type\is_numeric! and cast_type\is_numeric!
            if (abt == "s" or abt == "d") and not (cbt == "s" or cbt == "d")
                @add "#{c} =#{cbt} #{abt}tosi #{reg}\n"
                return c
            elseif (cbt == "s" or cbt == "d") and not (abt == "s" or abt == "d")
                @add "#{c} =#{cbt} s#{abt}tof #{reg}\n"
                return c

        if abt == "l" and cbt == "w"
            @add "#{c} =w copy #{reg}\n"
        elseif abt == "w" and cbt == "l"
            @add "#{c} =l extsw #{reg}\n"
        elseif abt == "s" and cbt == "d"
            @add "#{c} =d exts #{reg}\n"
        elseif abt == "d" and cbt == "s"
            @add "#{c} =#{cast_type.base_type} truncd #{reg}\n"
        else
            @add "#{c} =#{cbt} cast #{reg}\n"
        return c

    As: (ast)=>
        src_type, dest_type = ast.expr.__type, ast.__type
        fndec = node_assert ast.__converter, ast, "Couldn't figure out how to convert #{src_type} into #{dest_type}"
        fn_reg = fndec.__register
        reg = @add_value ast.expr
        converted = @fresh_local "converted"
        @add "#{converted} =#{dest_type.base_type} call #{fn_reg}(#{src_type.base_type} #{reg})\n"
        return converted

    TypeOf: (ast)=>
        return @get_string_reg("#{get_type(ast.expression)\verbose_type!}", "typename")

    SizeOf: (ast)=>
        t = get_type(ast.expression, true)
        return "#{t.bytes}"

    String: (ast)=>
        str = @fresh_local "str"
        if (#ast.content == 0) or (#ast.content == 1 and type(ast.content[1]) == "string")
            @add "#{str} =l call $bl_string(l #{@get_string_reg(ast.content[0])})\n"
            return str

        chunks = {}
        i = ast.content.start
        for interp in *ast.content
            if interp.start > i
                chunk = ast.content[0]\sub(1+(i-ast.content.start), interp.start-ast.content.start)
                table.insert chunks, chunk unless chunk == ""
            table.insert chunks, interp
            i = interp.after

        if ast.content.after > i
            chunk = ast.content[0]\sub(1+(i-ast.content.start), ast.content.after-ast.content.start)
            table.insert chunks, chunk unless chunk == ""

        cord_reg = @fresh_local "cord.buf"
        @add "#{cord_reg} =l copy 0\n"
        chunk_reg = @fresh_local "string.chunk"
        for i,chunk in ipairs chunks
            if type(chunk) == 'string'
                @add "#{chunk_reg} =l copy #{@get_string_reg chunk, "str.literal"}\n"
            else
                t = get_type(chunk)
                node_assert t, chunk, "Couldn't get this type"
                val_reg = @add_value chunk
                if t == Types.String
                    @add "#{chunk_reg} =l copy #{val_reg}\n"
                elseif chunk.__converter
                    @add "#{chunk_reg} =l call #{chunk.__converter.__register}(#{t.base_type} #{val_reg})\n"
                else
                    fn = @get_tostring_fn t, ast
                    @add "#{chunk_reg} =l call #{fn}(#{t.base_type} #{val_reg}, l 0)\n"

            @add "#{cord_reg} =l call $CORD_cat(l #{cord_reg}, l #{chunk_reg})\n"
                
        @add "#{cord_reg} =l call $CORD_to_const_char_star(l #{cord_reg})\n"
        @add "#{str} =l call $bl_string(l #{cord_reg})\n"
        return str

    DSL: (ast)=>
        str = @fresh_local "str"
        if (#ast.content == 0) or (#ast.content == 1 and type(ast.content[1]) == "string")
            @add "#{str} =l call $bl_string(l #{@get_string_reg(ast.content[0])})\n"
            return str

        @add "#{str} =l call $bl_string(l #{@get_string_reg("", "emptystr")})\n"
        dsl_type = get_type(ast, true)

        stringify = (val)->
            t = get_type(val, true)
            val_reg = @add_value val
            safe = if t == dsl_type or val.__tag == "Escape" or val.__tag == "Newline"
                val_reg
            else
                converter = node_assert val.__converter, val, "Couldn't figure out how to convert #{val.value.__type} to #{dsl_type}"
                escaped = @fresh_local "escaped"
                @add "#{escaped} =l call #{converter.__register}(#{t.base_type} #{val_reg})\n"
                escaped
            @add "#{str} =l call $bl_string_append_string(l #{str}, l #{safe})\n"

        i = ast.content.start
        for interp in *ast.content
            if interp.start > i
                chunk = ast.content[0]\sub(1+(i-ast.content.start), interp.start-ast.content.start)
                @add "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg chunk})\n"

            stringify(interp)
            i = interp.after

        if ast.content.after > i
            chunk = ast.content[0]\sub(1+(i-ast.content.start), ast.content.after-ast.content.start)
            @add "#{str} =l call $bl_string_append_string(l #{str}, l #{@get_string_reg chunk})\n"

        return str
    
    FieldName: (ast)=>
        name = @fresh_local ast[0]
        @add "#{name} =l call $bl_string(l #{@get_string_reg ast[0], ast[0]})\n"
        return name

    Interp: (ast)=> @add_value ast.value

    Newline: (ast)=> @get_string_reg("\n", "newline")

    Escape: (ast)=>
        esc = {a:'\a',b:'\b',t:'\t',n:'\n',r:'\r',v:'\v'}
        text = ast[0]\sub(2)
        c = if esc[text]
            esc[text]\byte(1)
        elseif text\match('[0-8][0-8][0-8]')
            tonumber(text, 8)
        elseif text\match('x[0-9a-fA-F][0-9a-fA-F]')
            tonumber(text\sub(2), 16)
        else
            text\byte(1)
        return @get_string_reg(("%c")\format(c), "char")

    Negative: (ast)=>
        t = get_type ast.value
        if t\is_numeric!
            reg = @add_value ast.value
            ret = @fresh_local "neg"
            @add "#{ret} =#{t.base_type} neg #{reg}\n"
            return ret
        elseif t\is_a(Types.Range)
            orig = @add_value ast.value
            range = @fresh_local "neg.range"
            @add "#{range} =l call $range_backwards(l #{orig})\n"
            return range
        else
            node_error ast, "Invalid type to negate: #{t}"

    Len: (ast)=>
        t = get_type ast.value
        value = @add_value ast.value
        len = @fresh_local "len"
        if t\is_a(Types.Range)
            @add "#{len} =l call $range_len(l #{value})\n"
        elseif t\is_a(Types.ListType)
            @add "#{len} =l loadl #{value}\n"
        elseif t\is_a(Types.TableType)
            @add "#{len} =l call $hashmap_length(l #{value})\n"
        elseif t\is_a(Types.String)
            @add "#{len} =l call $strlen(l #{value})\n"
        else
            node_error ast, "Expected List or Range type, not #{t}"
        return len

    Not: (ast)=>
        t = get_type(ast.value)
        b = @add_value ast.value
        ret = @fresh_local "not"
        @add "#{ret} =w cne#{t.base_type} #{b}, 1\n"
        return ret

    IndexedTerm: (ast)=>
        t = get_type ast.value, true
        if t\is_a(Types.TypeValue) and t.type\is_a(Types.EnumType) and ast.index.__tag == "FieldName"
            value = node_assert t.type.field_values[ast.index[0]], ast, "Couldn't find enum field: .#{ast.index[0]} on type #{t.type}"
            return "#{value}"
        elseif t\is_a(Types.TypeValue) and (t.type\is_a(Types.StructType) or t.type\is_a(Types.UnionType)) and ast.index.__tag == "FieldName"
            if method = ast.__staticmethod
                node_assert method.__register, method, "No register found"
                return method.__register
            else
                loc = ast.__declaration.__location
                tmp = @fresh_local "#{ast[0]}.value"
                @add "#{tmp} =#{t.base_type} #{t.load} #{loc}\n"
                return tmp

        if t\is_a(Types.ListType)
            item_type = t.item_type
            index_type = get_type(ast.index)
            ListMethods = require 'list_methods'
            if index_type\is_a(Types.Int)
                return ListMethods.methods.get_or_fail(ast, @)
            elseif index_type\is_a(Types.Range)
                return ListMethods.methods.range(ast, @)
            elseif ast.index.__tag == "FieldName"
                node_error ast, "Field access on lists is not currently supported"
            else
                node_error ast.index, "Index is #{index_type} instead of Int or Range"
        elseif t\is_a(Types.TableType)
            TableMethods = require "table_methods"
            return TableMethods.methods.get_or_fail(ast, @)
        elseif t\is_a(Types.StructType)
            if ast.__method
                return assert(ast.__method.__register)

            member = if ast.index.__tag == "FieldName"
                member_name = ast.index[0]
                node_assert t.members[member_name], ast.index, "Not a valid struct member of #{t}"
                t.members[member_name]
            elseif ast.index.__tag == "Int"
                i = tonumber(ast.index[0])
                node_assert 1 <= i and i <= #t.members, ast.index, "#{t} only has members between 1 and #{#t.members}"
                t.members[i]
            else
                node_error ast.index, "Structs can only be indexed by a field name or Int literal"
            struct_reg = @add_value ast.value
            ret = @fresh_local "member"
            if member.inline
                @add "#{ret} =l add #{struct_reg}, #{member.offset}\n"
            else
                loc = @fresh_local "member.loc"
                @add "#{loc} =l add #{struct_reg}, #{member.offset}\n"
                @add "#{ret} =#{member.type.base_type} #{member.type.load} #{loc}\n"
            return ret
        elseif t\is_a(Types.UnionType)
            if ast.__method
                return assert(ast.__method.__register)

            node_assert ast.index.__tag == "FieldName", ast, "Not a valid union field name"
            member_name = ast.index[0]
            member = node_assert t.members[member_name], ast.index, "Not a valid union member of #{t\verbose_type!}"
            union_reg = @add_value ast.value
            is_member,tag,ret = @fresh_locals "is.member","tag","ret"
            @add "#{tag} =l loadl #{union_reg}\n"
            @add "#{is_member} =w ceql #{tag}, #{member.index}\n"
            if_tag,use_nil,done = @fresh_labels "if.tag","use.nil","done"
            @add "jnz #{is_member}, #{if_tag}, #{use_nil}\n"

            @add_label if_tag
            value_loc = @fresh_local "value.loc"
            @add "#{value_loc} =l add #{union_reg}, 8\n"
            @add "#{ret} =#{member.type.base_type} #{member.type.load} #{value_loc}\n"
            @add "jmp #{done}\n"

            @add_label use_nil
            @set_nil member.type, ret
            @add "jmp #{done}\n"

            @add_label done
            return ret
        elseif t\is_a(Types.Range)
            index_type = get_type(ast.index)
            -- TODO: Slice ranges
            node_assert index_type\is_a(Types.Int) or index_type == Types.OptionalType(Types.Int), ast.index, "Index is #{index_type} instead of Int"
            range_reg, index_reg = @add_values ast.value, ast.index
            ret = @fresh_local "range.nth"
            @add "#{ret} =l call $range_nth(l #{range_reg}, l #{index_reg})\n"
            return ret
        elseif t\is_a(Types.String)
            index_type = get_type(ast.index)
            str, index_reg = @add_values ast.value, ast.index
            if index_type\is_a(Types.Int) or index_type == Types.OptionalType(Types.Int) -- Get nth character as an Int
                char = @fresh_local "char"
                @add "#{char} =l call $bl_string_nth_char(l #{str}, l #{index_reg})\n"
                return char
            elseif index_type\is_a(Types.Range) -- Get a slice of the string
                slice = @fresh_local "slice"
                @add "#{slice} =l call $bl_string_slice(l #{str}, l #{index_reg})\n"
                return slice
            else
                node_error ast.index, "Index is #{index_type} instead of Int or Range"
        else
            node_error ast.value, "Indexing is not valid on type #{t\verbose_type!}"

    List: (ast)=>
        list,list_items,size,p = @fresh_locals "list", "list.items", "list.size", "p"
        @add "#{list} =l call $gc_alloc(l 17)\n" -- size of list struct: {size, items, slack}
        if #ast == 0
            return list

        @add "#{size} =l copy 0\n"
        @add "#{list_items} =l copy 0\n"

        item_type = get_type(ast).item_type

        get_add_item_code = (item)->
            code = @new_code!
            item_reg = code\add_value item
            code\add "#{size} =l add #{size}, #{item_type.bytes}\n"
            code\add "#{list_items} =l call $gc_realloc(l #{list_items}, l #{size})\n"
            code\add "#{p} =l add #{list_items}, #{size}\n"
            code\add "#{p} =l sub #{p}, #{item_type.bytes}\n"
            code\add "#{item_type.store} #{item_reg}, #{p}\n"
            return code

        next_label = nil
        for i,val in ipairs ast
            if next_label
                @add "jmp #{next_label}\n" unless @ends_with_jump!
                @add_label next_label
                next_label = nil

            switch val.__tag
                when "If"
                    true_label = @fresh_label "if.true"
                    cond, expr = assert(val[1].condition), assert(val[1].body[1])
                    cond_reg = @add_value cond
                    next_label = @fresh_label "list.next"
                    @check_truthiness get_type(cond), cond_reg, true_label, next_label
                    @add_label true_label
                    @add get_add_item_code(expr)
                when "For"
                    iter_reg = @add_value val.iterable
                    key_reg, value_reg = if val.index and val.val
                        val.index.__register, val.val.__register
                    elseif val.val and val.iterable.__type\works_like_a(Types.TableType)
                        val.val.__register, nil
                    elseif val.val
                        nil, val.val.__register
                    else
                        nil, nil
                    @add_for_loop {
                        type: val.iterable.__type, :iter_reg, :key_reg, :value_reg, scope:{val.body, val.filter},
                        make_body: (-> get_add_item_code(val.body[1])), filter: val.filter,
                    }
                when "While"
                    @add_while_loop val, (-> get_add_item_code(val.body[1]))
                when "Repeat"
                    @add_repeat_loop val, (-> get_add_item_code(val.body[1]))
                else
                    @add get_add_item_code(val)

        if next_label
            @add "jmp #{next_label}\n" unless @ends_with_jump!
            @add_label next_label

        @add "#{size} =l div #{size}, #{item_type.bytes}\n"
        @add "storel #{size}, #{list}\n"
        items_loc = @fresh_local "items.loc"
        @add "#{items_loc} =l add #{list}, 8\n"
        @add "storel #{list_items}, #{items_loc}\n"
        -- List slack is zero, no need to set
        return list

    Table: (ast)=>
        t = get_type ast
        node_assert not t.key_type\is_a(Types.OptionalType) and not t.value_type\is_a(Types.OptionalType), ast,
            "Nil cannot be stored in a table, but this table is #{t}"

        tab = @fresh_local "table"
        @add "#{tab} =l call $hashmap_new(l 0)\n"
        if #ast == 0
            return tab

        TableMethods = require "table_methods"
        add_entry = (entry)->
            code = @new_code!
            TableMethods.methods.set({tab,entry.key,entry.value}, code)
            return code

        next_label = nil
        for i,val in ipairs ast
            if next_label
                @add "jmp #{next_label}\n" unless @ends_with_jump!
                @add "#{next_label}\n"
                next_label = nil

            switch val.__tag
                when "If"
                    true_label = @fresh_label "if.true"
                    cond, expr = assert(val[1].condition), assert(val[1].body[1])
                    cond_reg = @add_value cond
                    next_label = @fresh_label "list.next"
                    @check_truthiness get_type(cond), cond_reg, true_label, next_label
                    @add_label true_label
                    @add add_entry expr
                when "For"
                    iter_reg = @add_value val.iterable
                    key_reg, value_reg = if val.index and val.val
                        val.index.__register, val.val.__register
                    elseif val.val and val.iterable.__type\works_like_a(Types.TableType)
                        val.val.__register, nil
                    elseif val.val
                        nil, val.val.__register
                    else
                        nil, nil
                    @add_for_loop {
                        type: val.iterable.__type, :iter_reg, :key_reg, :value_reg, scope:{val.body, val.filter},
                        make_body: (-> add_entry(val.body[1])), filter: val.filter,
                    }

                when "While"
                    @add_while_loop val, (-> add_entry(val.body[1]))
                when "Repeat"
                    @add_repeat_loop val, (-> add_entry(val.body[1]))
                else
                    @add add_entry(val)

        if next_label
            @add "jmp #{next_label}\n" unless @ends_with_jump!
            @add_label next_label
        return tab

    Range: (ast)=>
        range = @fresh_local "range"
        if ast.first and ast.next and ast.last
            first_reg,next_reg,last_reg = @add_values ast.first, ast.next, ast.last
            @add "#{range} =l call $range_new(l #{first_reg}, l #{next_reg}, l #{last_reg})\n"
        elseif ast.first and ast.next and not ast.last
            first_reg,next_reg = @add_values ast.first, ast.next
            @add "#{range} =l call $range_new_first_next(l #{first_reg}, l #{next_reg})\n"
        elseif ast.first and not ast.next and ast.last
            first_reg,last_reg = @add_values ast.first, ast.last
            @add "#{range} =l call $range_new_first_last(l #{first_reg}, l #{last_reg})\n"
        elseif ast.first and not ast.next and not ast.last
            first_reg = @add_values ast.first
            @add "#{range} =l call $range_new_first_last(l #{first_reg}, l 999999999999999999)\n"
        elseif not ast.first and not ast.next and ast.last
            last_reg = @add_values ast.last
            @add "#{range} =l call $range_new_first_last(l -999999999999999999, l #{last_reg})\n"
        elseif not ast.first and not ast.next and not ast.last
            @add "#{range} =l call $range_new_first_last(l -999999999999999999, l 999999999999999999)\n"
        else
            node_error ast, "WTF"
        return range

    Or: (ast)=>
        done_label = @fresh_label "or.end"
        code = ""
        t = get_type(ast)
        ret_reg = @fresh_local "any.true"
        for i,val in ipairs ast
            val_reg = @add_value val
            false_label = @fresh_label "or.falsey"
            @add "#{ret_reg} =#{t.base_type} copy #{val_reg}\n"
            if i < #ast
                @check_truthiness get_type(val), val_reg, done_label, false_label
                @add_label false_label
        @add "#{done_label}\n"
        return ret_reg

    And: (ast)=>
        done_label = @fresh_label "and.end"
        t = get_type(ast)
        ret_reg = @fresh_local "all.true"
        for i,val in ipairs ast
            val_reg = @add_value val
            true_label = @fresh_label "and.truthy"
            @add "#{ret_reg} =#{t.base_type} copy #{val_reg}\n"
            if i < #ast
                @check_truthiness get_type(val), val_reg, true_label, done_label
                @add_label true_label
        @add_label done_label
        return ret_reg

    Xor: (ast)=>
        for val in *ast
            node_assert get_type(val)\is_a(Types.Bool), val, "Expected Bool here, but got #{get_type val}"
        return @add_infix_op ast, "xor"

    AddSub: (ast)=>
        t_lhs,t_rhs = get_type(ast.lhs),get_type(ast.rhs)
        tl_nn, tr_nn = (t_lhs.nonnil or t_lhs), (t_rhs.nonnil or t_rhs)
        if ast.op[0] == "+"
            if tl_nn == tr_nn and (tl_nn\is_numeric! or tl_nn\is_a(Types.MeasureType))
                return @add_infix_op ast, "add"
            elseif t_lhs == t_rhs and t_lhs\works_like_a(Types.String)
                return @add_infix_op ast, (ret,lhs,rhs)->
                    "#{ret} =l call $bl_string_append_string(l #{lhs}, l #{rhs})\n"
            elseif t_lhs\works_like_a(Types.ListType) and t_rhs\is_a(t_lhs.item_type)
                return @add_infix_op ast, (ret,lhs,rhs)->
                    list_reg,item_reg,item_type = lhs,rhs,t_rhs
                    new_len,len,new_items,items,new_size,size,tmp = @fresh_locals "new.len","len","new.items","items","new.size","size","tmp"
                    code = @new_code "\n# Append\n"
                    code\add "#{len} =l loadl #{list_reg}\n"
                    code\add "#{size} =l mul #{len}, #{item_type.bytes}\n"
                    code\add "#{new_len} =l add #{len}, 1\n"
                    code\add "#{tmp} =l add #{list_reg}, 8\n"
                    code\add "#{items} =l loadl #{tmp}\n"
                    code\add "#{new_size} =l mul #{new_len}, #{item_type.bytes}\n"
                    code\add "#{new_items} =l call $gc_alloc(l #{new_size})\n"
                    code\add "#{tmp} =l call $mempcpy(l #{new_items}, l #{items}, l #{size})\n"
                    code\add "#{item_type.store} #{item_reg}, #{tmp}\n"
                    code\add "#{ret} =l call $gc_alloc(l 16)\n"
                    code\add "storel #{new_len}, #{ret}\n"
                    code\add "#{tmp} =l add #{ret}, 8\n"
                    code\add "storel #{new_items}, #{tmp}\n"
                    code\add "\n"
                    return code
            elseif t_rhs\works_like_a(Types.ListType) and t_lhs\is_a(t_rhs.item_type)
                return @add_infix_op ast, (ret,lhs,rhs)->
                    list_reg,item_reg,item_type = rhs,lhs,t_lhs
                    new_len,len,new_items,items,new_size,size,tmp = @fresh_locals "new.len","len","new.items","items","new.size","size","tmp"
                    code = @new_code "\n# Prepend\n"
                    code\add "#{len} =l loadl #{list_reg}\n"
                    code\add "#{size} =l mul #{len}, #{item_type.bytes}\n"
                    code\add "#{new_len} =l add #{len}, 1\n"
                    code\add "#{tmp} =l add #{list_reg}, 8\n"
                    code\add "#{items} =l loadl #{tmp}\n"
                    code\add "#{new_size} =l mul #{new_len}, #{item_type.bytes}\n"
                    code\add "#{new_items} =l call $gc_alloc(l #{new_size})\n"
                    code\add "#{item_type.store} #{item_reg}, #{new_items}\n"
                    code\add "#{tmp} =l add #{new_items}, #{item_type.bytes}\n"
                    code\add "call $memcpy(l #{tmp}, l #{items}, l #{size})\n"
                    code\add "#{ret} =l call $gc_alloc(l 16)\n"
                    code\add "storel #{new_len}, #{ret}\n"
                    code\add "#{tmp} =l add #{ret}, 8\n"
                    code\add "storel #{new_items}, #{tmp}\n"
                    code\add "\n"
                    return code
            elseif t_lhs == t_rhs and t_lhs\works_like_a(Types.ListType)
                return @add_infix_op ast, (ret,lhs,rhs)->
                    len1,len2,len3,items1,items2,items3,size,tmp = @fresh_locals "len1","len2","len3","items1","items2","items3","size","tmp"
                    code = @new_code "#{len1} =l loadl #{lhs}\n"
                    code\add "#{len2} =l loadl #{rhs}\n"
                    code\add "#{lhs} =l add #{lhs}, 8\n"
                    code\add "#{items1} =l loadl #{lhs}\n"
                    code\add "#{rhs} =l add #{rhs}, 8\n"
                    code\add "#{items2} =l loadl #{rhs}\n"
                    code\add "#{len3} =l add #{len1}, #{len2}\n"
                    code\add "#{size} =l mul #{len3}, #{t_lhs.item_type.bytes}\n"
                    code\add "#{ret} =l call $gc_alloc(l 16)\n"
                    code\add "storel #{len3}, #{ret}\n"
                    code\add "#{items3} =l call $gc_alloc(l #{size})\n"
                    code\add "#{tmp} =l add #{ret}, 8\n"
                    code\add "storel #{items3}, #{tmp}\n"
                    code\add "#{size} =l mul #{len1}, #{t_lhs.item_type.bytes}\n"
                    code\add "#{items3} =l call $mempcpy(l #{items3}, l #{items1}, l #{size})\n"
                    code\add "#{size} =l mul #{len2}, #{t_lhs.item_type.bytes}\n"
                    code\add "call $memcpy(l #{items3}, l #{items2}, l #{size})\n"
                    return code
            else
                node_error ast, "Addition is not supported for #{t_lhs} and #{t_rhs}"
        else -- "-"
            if tl_nn == tr_nn and (tl_nn\is_numeric! or tl_nn\is_a(Types.MeasureType))
                return @add_infix_op ast, "sub"
            else
                node_error ast, "Subtraction is not supported for #{t_lhs} and #{t_rhs}"

    MulDiv: (ast)=>
        t_lhs,t_rhs = get_type(ast.lhs),get_type(ast.rhs)
        tl_nn, tr_nn = (t_lhs.nonnil or t_lhs), (t_rhs.nonnil or t_rhs)
        if ast.op[0] == "*"
            if tl_nn == tr_nn and tl_nn\is_numeric!
                return @add_infix_op ast, "mul"
            elseif (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.Num)) or (tl_nn\is_a(Types.Num) and tr_nn\is_a(Types.MeasureType)) or (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.MeasureType))
                return @add_infix_op ast, "mul"
            else
                node_error ast, "Multiplication is not supported for #{t_lhs} and #{t_rhs}"
        else -- "/"
            if tl_nn == tr_nn and tl_nn\is_numeric!
                return @add_infix_op ast, "div"
            elseif (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.Num)) or (tl_nn\is_a(Types.Num) and tr_nn\is_a(Types.MeasureType)) or (tl_nn\is_a(Types.MeasureType) and tr_nn\is_a(Types.MeasureType))
                return @add_infix_op ast, "div"
            else
                node_error ast, "Division is not supported for #{t_lhs} and #{t_rhs}"

    AddUpdate: (ast)=>
        lhs_type,rhs_type = get_type(ast.lhs),get_type(ast.rhs)
        lhs_reg,rhs_reg = @add_values ast.lhs, ast.rhs
        if nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            @add "#{lhs_reg} =#{lhs_type.base_type} add #{lhs_reg}, #{rhs_reg}\n"
        elseif lhs_type == rhs_type and lhs_type\works_like_a(Types.String)
            @add "#{lhs_reg} =l call $bl_string_append_string(l #{lhs_reg}, l #{rhs_reg})\n"
        elseif lhs_type\works_like_a(Types.ListType) and rhs_type\is_a(lhs_type.item_type)
            node_error ast, "Cannot use += with Lists, use list.append(other) or list = list+other instead"
        elseif lhs_type == rhs_type and lhs_type\works_like_a(Types.ListType)
            node_error ast, "Cannot use += with Lists, use list.append_all(other) or list = list+other instead"
        else
            node_error ast, "Addition is not supported for #{lhs_type} and #{rhs_type}"

        if ast.lhs.__location
            @add "#{lhs_type.store} #{lhs_reg}, #{ast.lhs.__location}\n"
        return lhs_reg

    SubUpdate: (ast)=>
        lhs_type,rhs_type = get_type(ast.lhs),get_type(ast.rhs)
        unless nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            node_error ast, "Subtraction is not supported for #{lhs_type} and #{rhs_type}"
        lhs_reg,rhs_reg = @add_values ast.lhs, ast.rhs
        @add "#{lhs_reg} =#{lhs_type.base_type} sub #{lhs_reg}, #{rhs_reg}\n"
        if ast.lhs.__location
            @add "#{lhs_type.store} #{lhs_reg}, #{ast.lhs.__location}\n"
        return lhs_reg

    MulUpdate: (ast)=>
        lhs_type,rhs_type = get_type(ast.lhs),get_type(ast.rhs)
        unless nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            node_error ast, "Multiplication is not supported for #{lhs_type} and #{rhs_type}"
        lhs_reg,rhs_reg = @add_values ast.lhs, ast.rhs
        @add "#{lhs_reg} =#{lhs_type.base_type} mul #{lhs_reg}, #{rhs_reg}\n"
        if ast.lhs.__location
            @add "#{lhs_type.store} #{lhs_reg}, #{ast.lhs.__location}\n"
        return lhs_reg

    DivUpdate: (ast)=>
        lhs_type,rhs_type = get_type(ast.lhs),get_type(ast.rhs)
        unless nonnil_eq(lhs_type, rhs_type) and lhs_type\is_numeric!
            node_error ast, "Division is not supported for #{lhs_type} and #{rhs_type}"
        lhs_reg,rhs_reg = @add_values ast.lhs, ast.rhs
        @add "#{lhs_reg} =#{lhs_type.base_type} div #{lhs_reg}, #{rhs_reg}\n"
        if ast.lhs.__location
            @add "#{lhs_type.store} #{lhs_reg}, #{ast.lhs.__location}\n"
        return lhs_reg

    OrUpdate: (ast)=>
        t_lhs, t_rhs = get_type(ast.lhs), get_type(ast.rhs)
        true_label,false_label = @fresh_labels "or.lhs.true", "or.lhs.false"
        lhs_reg = @add_value ast.lhs
        @check_truthiness t_lhs, lhs_reg, true_label, false_label
        @add_label false_label
        rhs_reg = @add_value ast.rhs
        @add "#{lhs_reg} =#{t_lhs.base_type} copy #{rhs_reg}\n"
        @add "#{t_lhs.store} #{lhs_reg}, #{ast.lhs.__location}\n" if ast.lhs.__location
        @add "jmp #{true_label}\n"
        @add_label true_label
        return lhs_reg

    AndUpdate: (ast)=>
        t_lhs, t_rhs = get_type(ast.lhs), get_type(ast.rhs)
        true_label,false_label = @fresh_labels "and.lhs.true", "and.lhs.false"
        lhs_reg = @add_value ast.lhs
        @check_truthiness t_lhs, lhs_reg, true_label, false_label
        @add_label true_label
        rhs_reg = @add_value ast.rhs
        @add "#{lhs_reg} =#{t_lhs.base_type} copy #{rhs_reg}\n"
        @add "#{t_lhs.store} #{lhs_reg}, #{ast.lhs.__location}\n" if ast.lhs.__location
        @add "jmp #{false_label}\n"
        @add_label false_label
        return lhs_reg

    ButWithUpdate: (ast)=>
        t = get_type ast.base
        node_assert t\is_a(Types.StructType), ast, "| operator is only supported for Struct types"

        base_reg = @add_value ast.base
        ret = @fresh_local "#{t.name\lower!}.butwith"
        @add "#{ret} =l call $gc_alloc(l #{t.memory_size})\n"
        @add "call $memcpy(l #{ret}, l #{base_reg}, l #{t.memory_size})\n"
        p = @fresh_local "#{t.name\lower!}.butwith.member.loc"
        for override in *ast
            memb = if override.index
                t.members[tonumber(override.index[0])]
            elseif override.field
                t.members[override.field[0]]
            else
                node_error override, "I don't know what this is"

            node_assert memb, override, "Not a valid member of #{t}"
            node_assert get_type(override.value)\is_a(memb.type), override.value, "Not a #{memb}"
            val_reg = @add_value override.value
            @add "#{p} =l add #{ret}, #{memb.offset}\n"
            @add "#{memb.type.store} #{val_reg}, #{p}\n"

        @add "#{t.store} #{base_reg}, #{ast.base.__location}\n" if ast.base.__location
        return "#{base_reg}"

    MethodCallUpdate: (ast)=>
        dest = ast[1]
        node_assert dest and dest.__tag == "Var", dest, "Method call updates expect a variable"
        update_sig = "(#{concat [tostring(get_type(a)) for a in *ast], ","})=>#{get_type(dest)}"
        fn_type = get_type ast.fn
        fn_reg = @add_value ast.fn

        if fn_type
            node_assert fn_type\is_a(Types.FnType), ast.fn, "This is not a function, it's a #{fn_type or "???"}"
            node_assert "#{fn_type}" == update_sig, ast, "For this to work, #{ast.fn[0]} should be #{update_sig}, not #{fn_type}"

        args = {}
        for arg in *ast
            arg_reg = @add_value arg
            table.insert args, "#{get_type(arg).base_type} #{arg_reg}"

        ret_type = fn_type and fn_type.return_type or get_type(dest)

        if dest.__register
            @add "#{dest.__register} =#{ret_type.base_type} call #{fn_reg}(#{concat args, ", "})\n"
            return dest.__register
        elseif dest.__location
            ret = @fresh_local "return"
            @add "#{ret} =#{ret_type.base_type} call #{fn_reg}(#{concat args, ", "})\n"
            @add "#{ret_type.store} #{ret}, #{dest.__location}\n"
            return ret

    Mod: (ast)=>
        t = get_type(ast)
        if (t.nonnil or t)\is_a(Types.Int) or (t.nonnil or t)\is_a(Types.Num)
            lhs_reg, rhs_reg = @add_values ast.lhs, ast.rhs
            ret = @fresh_local "remainder"
            if t\is_a(Types.Int)
                @add "#{ret} =l call $sane_lmod(l #{lhs_reg}, l #{rhs_reg})\n"
            else
                @add "#{ret} =d call $sane_fmod(d #{lhs_reg}, d #{rhs_reg})\n"
            return ret
        else
            node_error ast, "Modulus is not supported for #{get_type(ast.lhs)} and #{get_type(ast.rhs)}"

    Pow: (ast)=>
        base_type = get_type ast.base
        exponent_type = get_type ast.exponent
        base_reg, exponent_reg = @add_values ast.base, ast.exponent
        ret_reg = @fresh_local "result"
        if base_type == exponent_type and base_type\is_a(Types.Int)
            @add "#{ret_reg} =l call $ipow(l #{base_reg}, l #{exponent_reg})\n"
        elseif base_type == exponent_type and base_type\is_a(Types.Num)
            @add "#{ret_reg} =d call $pow(d #{base_reg}, d #{exponent_reg})\n"
        else
            node_error ast, "Exponentiation is not supported for #{base_type} and #{exponent_type}"
        return ret_reg

    ButWith: (ast)=>
        t = get_type ast.base
        if t\is_a(Types.ListType)
            error "Not impl"
        elseif t\is_a(Types.String)
            error "Not impl"
        elseif t\is_a(Types.StructType)
            lhs_reg = @add_value ast.base
            ret = @fresh_local "#{t.name\lower!}.butwith"
            struct_size = 8*#t.sorted_members
            @add "#{ret} =l call $gc_alloc(l #{struct_size})\n"
            @add "call $memcpy(l #{ret}, l #{lhs_reg}, l #{struct_size})\n"
            p = @fresh_local "#{t.name\lower!}.butwith.member.loc"
            for override in *ast
                member = if override.index
                    t.members[tonumber(override.index[0])]
                elseif override.field
                    t.members[override.field[0]]
                else
                    node_error override, "I don't know what this is"

                override_type = get_type(override.value, true)
                node_assert override_type\is_a(member.type), override.value, "Not a #{member.type}"
                val_reg = @add_value override.value
                @add "#{p} =l add #{ret}, #{member.offset}\n"
                @add "#{member.type.store} #{val_reg}, #{p}\n"

            return ret
        else
            node_error ast, "| operator is only supported for List and Struct types"

    In: (ast)=>
        haystack_type = get_type(ast.haystack, true)
        needle_type = get_type(ast.needle, true)
        if haystack_type\is_a(Types.ListType) and needle_type\is_a(haystack_type.item_type)
            found = @fresh_locals "found"
            done = @fresh_label "in.done"
            haystack_reg,needle_reg = @add_values ast.haystack, ast.needle
            @add "#{found} =w copy 0\n"
            item_reg = @fresh_local("item")
            @add_for_loop {
                type: haystack_type, iter_reg: haystack_reg, value_reg:item_reg
                make_body: ->
                    base_type = haystack_type.item_type.base_type
                    code = if needle_type == Types.NilType and (base_type == 's' or base_type == 'd')
                        @new_code "#{found} =w cuo#{base_type} #{item_reg}, #{base_type}_0.0\n"
                    else
                        @new_code "#{found} =w ceq#{base_type} #{item_reg}, #{needle_reg}\n"
                    keep_going = @fresh_label "keep_going"
                    @add "jnz #{found}, #{done}, #{keep_going}\n"
                    @add "#{keep_going}\n"
                    return code
            }
            @add "#{done}\n"
            return found
        elseif haystack_type\is_a(Types.TableType) and needle_type\is_a(haystack_type.key_type)
            needle_reg,haystack_reg = @add_values ast.needle, ast.haystack
            key_getter = @fresh_local "key.getter"
            TableMethods = require 'table_methods'
            @add TableMethods.to_table_format @, haystack_type.key_type, needle_reg, key_getter
            found = @fresh_local "found"
            @add "#{found} =l call $hashmap_get(l #{haystack_reg}, l #{key_getter})\n"
            @add "#{found} =l cnel #{found}, 0\n"
            return found
        elseif haystack_type == needle_type and haystack_type\is_a(Types.String)
            needle_reg,haystack_reg = @add_values ast.needle, ast.haystack
            found = @fresh_local "found"
            @add "#{found} =l call $strstr(l #{haystack_reg}, l #{needle_reg})\n"
            @add "#{found} =l cnel #{found}, 0\n"
            return found
        else
            -- TODO: support `Int in Range`, `[Foo] in [Foo]`, `Range in Range` etc.
            node_error ast, "Checking if #{needle_type} is in #{haystack_type} is not supported"

    Less: (ast)=>
        t = get_type(ast.lhs)
        sign = (t.base_type == 's' or t.base_type == 'd') and "" or "s"
        return @add_comparison ast, "c#{sign}lt#{t.base_type}"

    LessEq: (ast)=>
        t = get_type(ast.lhs)
        sign = (t.base_type == 's' or t.base_type == 'd') and "" or "s"
        return @add_comparison ast, "c#{sign}le#{t.base_type}"

    Greater: (ast)=>
        t = get_type(ast.lhs)
        sign = (t.base_type == 's' or t.base_type == 'd') and "" or "s"
        return @add_comparison ast, "c#{sign}gt#{t.base_type}"

    GreaterEq: (ast)=>
        t = get_type(ast.lhs)
        sign = (t.base_type == 's' or t.base_type == 'd') and "" or "s"
        return @add_comparison ast, "c#{sign}ge#{t.base_type}"

    Equal: (ast)=>
        lhs_type, rhs_type = get_type(ast.lhs), get_type(ast.rhs)
        if lhs_type\is_a(rhs_type) or rhs_type\is_a(lhs_type)
            lhs_reg,rhs_reg = @add_values ast.lhs, ast.rhs
            result = @fresh_local "comparison"
            if rhs_type == Types.NilType and (lhs_type.base_type == 's' or lhs_type.base_type == 'd')
                @add "#{result} =w cuo#{lhs_type.base_type} #{lhs_reg}, #{lhs_type.base_type}_0.0\n"
            elseif lhs_type == Types.NilType and (rhs_type.base_type == 's' or rhs_type.base_type == 'd')
                @add "#{result} =w cuo#{rhs_type.base_type} #{rhs_reg}, #{rhs_type.base_type}_0.0\n"
            else
                @add "#{result} =w ceq#{lhs_type.base_type} #{lhs_reg}, #{rhs_reg}\n"
            return result
        else
            return @add_comparison ast, "ceq#{lhs_type.base_type}"

    NotEqual: (ast)=>
        lhs_type, rhs_type = get_type(ast.lhs), get_type(ast.rhs)
        if lhs_type\is_a(rhs_type) or rhs_type\is_a(lhs_type)
            lhs_reg,rhs_reg = @add_values ast.lhs, ast.rhs
            result = @fresh_local "comparison"
            if rhs_type == Types.NilType and (lhs_type.base_type == 's' or lhs_type.base_type == 'd')
                @add "#{result} =w co#{lhs_type.base_type} #{lhs_reg}, #{lhs_type.base_type}_0.0\n"
            elseif lhs_type == Types.NilType and (rhs_type.base_type == 's' or rhs_type.base_type == 'd')
                @add "#{result} =w co#{rhs_type.base_type} #{rhs_reg}, #{rhs_type.base_type}_0.0\n"
            else
                @add "#{result} =w cne#{lhs_type.base_type} #{lhs_reg}, #{rhs_reg}\n"
            return result
        else
            return @add_comparison ast, "cnel"

    FnCall: (ast, skip_ret=false)=>
        if ast.fn.__inline_method
            arg_types = {ast.fn.value.__type}
            for arg in *ast
                if arg.__tag == "KeywordArg"
                    arg_types[arg.name[0]] = arg.value.__type
                else
                    table.insert arg_types, arg.__type
            matches, err = ast.fn.__type\matches(arg_types)
            node_assert matches, ast, err
            return ast.fn.__inline_method(ast, @, skip_ret)

        fn_type = get_type ast.fn, true
        fn_reg = @add_values ast.fn

        node_assert fn_type\is_a(Types.FnType), ast.fn, "This is not a function, it's a #{fn_type or "???"}"
        arg_types,arg_text = {},{}
        for arg in *ast
            if arg.__tag == "KeywordArg"
                arg_types[arg.name[0]] = get_type(arg.value)
                table.insert arg_text, "#{arg.name[0]}=#{get_type(arg.value)\verbose_type!}"
            else
                table.insert arg_types, get_type(arg)
                table.insert arg_text, "#{get_type(arg)\verbose_type!}"
        if ast.fn.__method
            table.insert arg_types, 1, (get_type(ast.fn.value, true))
            table.insert arg_text, 1, "#{get_type(ast.fn.value, true)}"

        node_assert fn_type\matches(arg_types), ast,
            "This function is being called with #{ast.fn[0]}(#{concat arg_text, ", "}) but is defined as #{fn_type}"

        kw_args = {}
        pos_args = {}
        if ast.fn.__method
            arg_reg = @add_value ast.fn.value
            table.insert pos_args, {reg: arg_reg, type: get_type(ast.fn.value), node: ast.fn.value}
        for arg in *ast
            if arg.__tag == "KeywordArg"
                arg_reg = @add_value arg.value
                kw_args[arg.name[0]] = arg_reg
            else
                arg_reg = @add_value arg
                table.insert pos_args, {reg: arg_reg, type: get_type(arg), node:arg}

        local arg_list
        if fn_type.arg_names
            arg_list = {}
            assert fn_type.arg_names, "No arg names: #{fn_type}"
            for i,name in ipairs fn_type.arg_names
                arg_reg = kw_args[name] or (table.remove(pos_args, 1) or {}).reg
                if not arg_reg
                    arg_reg = @fresh_local name
                    @set_nil fn_type.arg_types[i], arg_reg
                table.insert arg_list, "#{fn_type.arg_types[i].base_type} #{arg_reg}"
        else
            node_assert not next(kw_args), ast, "Keyword arguments supplied to a function that doesn't have names for its arguments"
            for _ in *fn_type.arg_types
                table.remove(pos_args, 1)

        if #pos_args > 0
            node_assert fn_type.varargs, pos_args[1].node, "The arguments from here onwards are not defined in the function signature: #{fn_type}"
            table.insert(arg_list, #fn_type.arg_types+1, "...")
            for arg in *pos_args
                table.insert arg_list, "#{arg.type.base_type} #{arg.reg}"

        if not arg_list
            arg_list = {}
            for arg in *ast
                node_assert arg.__tag != "KeywordArg", arg, "Keyword arguments are not allowed here"
                arg_reg, arg_code = @add_value arg
                table.insert arg_list, "#{get_type(arg).base_type} #{arg_reg}"

        if skip_ret
            @add "call #{fn_reg}(#{concat arg_list, ", "})\n"
            return

        ret_reg = @fresh_local "return"
        ret_type = fn_type and fn_type.return_type or get_type(ast)
        @add "#{ret_reg} =#{ret_type.base_type} call #{fn_reg}(#{concat arg_list, ", "}) # Ret type: #{ret_type} base: #{ret_type.base_type}\n"
        return ret_reg

    Lambda: (ast)=>
        node_assert ast.__register, ast, "Unreferenceable lambda"
        return ast.__register

    Struct: (ast)=>
        t = get_type ast, true
        ret = @fresh_local "#{t.name\lower!}"
        @add "#{ret} =l call $gc_alloc(l #{t.memory_size})\n"
        i = 0
        unpopulated = {n,memb for n,memb in pairs t.members}
        for field in *ast
            memb = if field.name
                t.members[field.name[0]]
            else
                i += 1
                t.members[i] or t.sorted_members[i]

            node_assert memb, field, "Not a valid struct member of #{t\verbose_type!}"
            m_t = get_type field.value
            node_assert m_t\is_a(memb.type), field, "Expected this value to have type #{memb.type\verbose_type!}, but got #{m_t\verbose_type!}"

            loc = @fresh_local "#{t\id_str!\lower!}.#{memb.name}.loc"
            @add "#{loc} =l add #{ret}, #{memb.offset}\n"
            val_reg = @add_value field.value
            if memb.inline
                @add "call $memcpy(l #{loc}, l #{val_reg}, l #{memb.type.memory_size})\n"
            else
                @add "#{m_t.store} #{val_reg}, #{loc}\n"
            unpopulated[memb.name] = nil

        for name,memb in pairs unpopulated
            continue unless memb.type\is_a(Types.OptionalType)
            unpopulated[name] = nil
            continue if memb.type.nil_value == 0
            loc = @fresh_local "#{t\id_str!\lower!}.#{memb.name}.loc"
            @add "#{loc} =l add #{ret}, #{memb.offset}\n"
            @add "#{memb.type.store} #{memb.type.nil_value}, #{loc}\n"

        for name,memb in pairs unpopulated
            node_error ast, "#{name} is a required field for #{t.name}, but was not specified"
            
        return ret

    Union: (ast)=>
        t = get_type ast
        ret = @fresh_local "#{t.name\lower!}"
        @add "#{ret} =l call $gc_alloc(l #{t.memory_size})\n"
        member = node_assert t.members[ast.member[0]], ast, "Not a valid union member name: #{ast.member[0]} in #{t\verbose_type!}"
        @add "storel #{member.index}, #{ret}\n"
        val_reg = @add_value value
        val_loc = @fresh_local "val.loc"
        @add "#{val_loc} =l add #{ret}, 8\n"
        @add "storel #{val_reg}, #{val_loc}\n"
        return ret

    If: (ast)=>
        t = get_type(ast)
        ret = t != Types.Abort and @fresh_local("if.value") or nil
        end_label,false_label = @fresh_labels "if.end", "if.else"
        for cond in *ast
            r = @add_value cond.condition
            true_label = @fresh_label "if.true"
            @check_truthiness get_type(cond.condition), r, true_label, false_label
            @add_label true_label
            block_type = get_type(cond.body)
            if block_type == Types.Abort
                @add_stmt cond.body
            elseif block_type == Types.NilType
                @add_stmt cond.body
                @set_nil t, ret unless @ends_with_jump!
            else
                block_reg = @add_value cond.body
                @add "#{ret} =#{block_type.base_type} copy #{block_reg}\n" unless @ends_with_jump!

            @add "jmp #{end_label}\n" unless @ends_with_jump!
            @add_label false_label
            false_label = @fresh_label "if.else"

        if ast.elseBody
            else_type = get_type(ast.elseBody)
            if else_type == Types.Abort
                @add_stmt ast.elseBody
            elseif else_type == Types.NilType
                @add_stmt ast.elseBody
                @set_nil(t, ret) unless t == Types.Abort or @ends_with_jump!
            else
                block_reg = @add_value ast.elseBody
                @add "#{ret} =#{else_type.base_type} copy #{block_reg}\n" unless @ends_with_jump!
                
            @add "jmp #{end_label}\n" unless @ends_with_jump!
        else
            @set_nil(t, ret) unless t == Types.Abort or @ends_with_jump!

        @add_label end_label
        return ret

    Do: (ast)=>
        end_label,next_label = @fresh_labels "do.end", "do.else"
        t = get_type(ast)
        ret = t != Types.Abort and @fresh_local("do.value") or nil
        @add "\n# Do block : #{t}\n"
        @set_nil(t, ret) if t != Types.Abort and t\is_a(Types.OptionalType)
        for i,block in ipairs ast
            @add "# Do block: #{block[0]\gsub("^[ \n]*","")\gsub("\n[ ]*", "; ")}\n"
            for jmp in coroutine.wrap(-> each_tag(block, "Stop"))
                if not jmp.target or jmp.target[0] == "do"
                    jmp.jump_label = end_label
            for jmp in coroutine.wrap(-> each_tag(block, "Skip"))
                if not jmp.target or jmp.target[0] == "do"
                    jmp.jump_label = next_label

            block_type = get_type(block)
            if block_type == Types.Abort
                @add_stmt block
            elseif block_type == Types.NilType
                @add_stmt block
                @set_nil t, ret
            else
                block_reg = @add_value block
                @add "#{ret} =#{block_type.base_type} copy #{block_reg}\n"

            @add "jmp #{end_label}\n" unless @ends_with_jump!
            @add "# End do-block\n"

            if i < #ast
                @add_label next_label
                next_label = @fresh_label "do.else"

        @add_label next_label
        @add "jmp #{end_label}\n"
        @add_label end_label
        return ret

    When: (ast)=>
        t = get_type(ast)
        what_type = get_type ast.what
        ret = t != Types.Abort and @fresh_local("when.value") or nil
        what_reg = @add_value ast.what
        end_label,next_case,next_body = @fresh_labels "when.end","when.case","when.body"
        match_reg = @fresh_local "when.matches"
        @add "jmp #{next_case}\n"
        for branch in *ast
            for case in *branch.cases
                node_assert get_type(case)\is_a(what_type), case, "'when' value is not a #{what_type}"
                @add "#{next_case}\n"
                next_case = @fresh_label "when.case"
                case_reg = @add_value case
                @add "#{match_reg} =l ceql #{what_reg}, #{case_reg}\n"
                @add "jnz #{match_reg}, #{next_body}, #{next_case}\n"

            @add_label next_body
            next_body = @fresh_label "when.body"

            block_type = get_type(branch.body)
            if block_type == Types.Abort
                @add_stmt branch.body
            elseif block_type == Types.NilType
                @add_stmt branch.body
                @set_nil t, ret
            else
                block_reg = @add_value branch.body
                @add "#{ret} =#{block_type.base_type} copy #{block_reg}\n" unless t == Types.Abort

            @add "jmp #{end_label}\n" unless @ends_with_jump!

        if ast.elseBody
            @add_label next_case

            else_type = get_type(ast.elseBody)
            if else_type == Types.Abort
                @add_stmt ast.elseBody
            elseif else_type == Types.NilType
                @add_stmt ast.elseBody
                @set_nil(t, ret) unless t == Types.Abort
            else
                block_reg = @add_value ast.elseBody
                @add "#{ret} =#{else_type.base_type} copy #{block_reg}\n"

            @add "jmp #{end_label}\n" unless @ends_with_jump!
        else
            @add_label next_case
            @set_nil(t, ret)
            @add "jmp #{end_label}\n"

        @add_label end_label
        return ret

    Block: (ast)=>
        for i=1,#ast-1
            @add_stmt(ast[i])
        last_reg = @add_value ast[#ast]
        return last_reg

    Fail: (ast)=>
        @add_stmt ast
        return 0

    Return: (ast)=>
        @add_stmt ast
        return 0

    Skip: (ast)=>
        @add_stmt ast
        return 0

    Stop: (ast)=>
        @add_stmt ast
        return 0

    Use: (ast)=>
        name = ast.name[0]
        mod = @fresh_local name
        @add "#{mod} =l call $bl_use(l #{@get_string_reg @env.filename, "current_file"}, l #{@get_string_reg name, name})\n"
        return mod

stmt_compilers =
    Block: (ast)=>
        for stmt in *ast
            @add_stmt stmt

    Use: (ast)=>
        assert ast.__imports
        name = ast.name[0]
        mod = @fresh_local name
        @add "#{mod} =l call $bl_use(l #{@get_string_reg @env.filename, "current_file"}, l #{@get_string_reg name, name})\n"
        success_label,fail_label,done_label = @fresh_labels "use.success","use.fail","use.done"

        for i,mem in ipairs ast.__imports
            loc = @fresh_local "#{name}.#{mem[0]}.loc"
            @add "#{loc} =l add #{mod}, #{8*(i-1)}\n"
            tmp = @fresh_local "#{name}.#{mem[0]}"
            @add "#{tmp} =#{mem.__type.base_type} #{mem.__type.load} #{loc}\n"
            @add "storel #{tmp}, #{mem.__location}\n"

    Declaration: (ast)=>
        value_type = get_type ast.value, true
        val_reg = @add_value ast.value
        if ast.var.__register
            @add "#{ast.var.__register} =#{value_type.base_type} copy #{val_reg}\n"
        elseif ast.var.__location
            @add "#{value_type.store} #{val_reg}, #{ast.var.__location}\n"
        else
            node_error ast.var, "Undefined variable"

    Assignment: (ast)=>
        node_assert #ast.lhs == #ast.rhs, ast.rhs, "Incorrect number of values on right hand side of assignment. Expected #{#ast.lhs}, but got #{#ast.rhs}"
        lhs_stores = {}

        for i,lhs in ipairs ast.lhs
            rhs = ast.rhs[i]

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
                list_reg,index_reg = @add_values lhs.value, lhs.index
                if index_type\is_a(Types.Int) or index_type == Types.OptionalType(Types.Int)
                    table.insert lhs_stores, (rhs_reg)->
                        code = @new_code!
                        nonnil_label, end_label = @fresh_labels "if.nonnil", "if.nonnil.done"
                        code\check_nil get_type(lhs.value), list_reg, nonnil_label, end_label
                        code\add_label nonnil_label
                        not_too_low,not_too_high = @fresh_labels "not.too.low", "not.too.high"
                        len, bounds_check = @fresh_locals "len", "bounds.check"
                        unless index_reg\match("^%d+$")
                            code\add "#{bounds_check} =w csgel #{index_reg}, 1\n"
                            code\add "jnz #{bounds_check}, #{not_too_low}, #{end_label}\n"
                            code\add "#{not_too_low}\n"

                        code\add "#{len} =l loadl #{list_reg}\n"
                        code\add "#{bounds_check} =w cslel #{index_reg}, #{len}\n"
                        code\add "jnz #{bounds_check}, #{not_too_high}, #{end_label}\n"

                        code\add_label not_too_high
                        p = @fresh_local "p"
                        code\add "#{p} =l add #{list_reg}, 8\n"
                        code\add "#{p} =l loadl #{p}\n"
                        offset = @fresh_local "offset"
                        code\add "#{offset} =l sub #{index_reg}, 1\n"
                        code\add "#{offset} =l mul #{offset}, #{t.item_type.bytes}\n"
                        code\add "#{p} =l add #{p}, #{offset}\n"
                        if rhs_type.base_type == "d"
                            rhs_casted = @fresh_local "list.item.float"
                            code\add "#{rhs_casted} =d cast #{rhs_reg}\n"
                            rhs_reg = rhs_casted
                        code\add "#{t.item_type.store} #{rhs_reg}, #{p}\n"
                        code\add "jmp #{end_label}\n"

                        code\add "#{end_label}\n"
                        return code
                elseif index_type\is_a(Types.Range)
                    node_error lhs.index, "Assigning to list slices is not supported."
                else
                    node_error lhs.index, "Index is #{index_type} instead of Int or Range"
            elseif t\is_a(Types.TableType)
                key_type = get_type(lhs.index)
                tab_reg,key_reg = @add_values lhs.value, lhs.index

                TableMethods = require 'table_methods'
                table.insert lhs_stores, (rhs_reg)->
                    _,code2 = TableMethods.methods.set {tab_reg, key_reg, rhs_reg}, @, true, t
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
                struct_reg = @add_value lhs.value

                table.insert lhs_stores, (rhs_reg)->
                    nonnil_label, end_label = @fresh_labels "if.nonnil", "if.nonnil.done"
                    code = @new_code!
                    code\check_nil get_type(lhs.value), struct_reg, nonnil_label, end_label
                    code\add_label nonnil_label
                    loc = @fresh_local "member.loc"
                    code\add "#{loc} =l add #{struct_reg}, #{memb.offset}\n"
                    if memb.inline
                        code\add "call $memcpy(l #{loc}, l #{rhs_reg}, l #{assert memb.type.memory_size})\n"
                    else
                        code\add "#{rhs_type.store} #{rhs_reg}, #{loc}\n"
                    code\add "jmp #{end_label}\n"
                    code\add_label end_label
                    return code
            else
                node_error lhs.value, "Only Lists and Structs are mutable, not #{t}"

        assignments = @new_code!
        for i=1,#ast.rhs
            rhs_reg = @add_value ast.rhs[i]
            if #ast.rhs > 1
                rhs_copy = @fresh_local "rhs.#{i}.copy"
                @add "#{rhs_copy} =#{get_type(ast.rhs[i]).base_type} copy #{rhs_reg}\n"
                assignments\add lhs_stores[i](rhs_copy)
            else
                assignments\add lhs_stores[i](rhs_reg)

        @add assignments

    AddUpdate: (ast)=> @add_value ast
    SubUpdate: (ast)=> @add_value ast
    MulUpdate: (ast)=> @add_value ast
    DivUpdate: (ast)=> @add_value ast
    OrUpdate: (ast)=> @add_value ast
    AndUpdate: (ast)=> @add_value ast
    ButWithUpdate: (ast)=> @add_value ast
    MethodCallUpdate: (ast)=> @add_value ast
    FnDecl: (ast)=>
    ConvertDecl: (ast)=>
    Extern: (ast)=>
    Macro: (ast)=>
    Pass: (ast)=>

    Fail: (ast)=>
        if ast.message
            t = get_type(ast.message)
            node_assert t\is_a(Types.OptionalType(Types.String)), ast.message,
                "Failure messages must be a String or nil, not #{get_type ast.message}"
            msg = @add_value ast.message
            fail_label,empty_label = @fresh_labels "failure", "empty.message"
            @add "jnz #{msg}, #{fail_label}, #{empty_label}\n"
            @add "#{empty_label}\n"
            @add "#{msg} =l copy #{@get_string_reg("Unexpected failure!", "default.failure")}\n"
            @add "jmp #{fail_label}\n#{fail_label}\n"
            @add "call $dprintf(l 2, l #{@get_string_reg(context_err(ast, "%s", 2).."\n", "failure.message")}, l #{msg})\n"
            @add "call $_exit(l 1)\n"
        else
            @add "call $dprintf(l 2, l #{@get_string_reg(context_err(ast, "A failure occurred!", 2).."\n", "failure.message")})\n"
            @add "call $_exit(l 1)\n"

    TypeDeclaration: (ast)=> ""

    StructDeclaration: (ast)=>
        for staticvar in *ast
            if staticvar.__tag == "Declaration"
                @add_stmt staticvar

    UnionDeclaration: (ast)=>
        for staticvar in *ast
            if staticvar.__tag == "Declaration"
                @add_stmt staticvar

    EnumDeclaration: (ast)=> ""

    UnitDeclaration: (ast)=> ""

    Export: (ast)=> ""

    FnCall: (ast)=>
        ret_type = get_type(ast)
        if ret_type
            node_assert ret_type == Types.Abort or ret_type == Types.NilType, ast, "Return value (#{ret_type}) is not being used"
        code = @new_code!
        code\add_value ast
        @add (tostring(code)\gsub("[^\n]- (call [^\n]*\n)$", "%1"))

    Return: (ast)=>
        if ast.value
            reg = @add_value ast.value
            if get_type(ast.value)\is_a(Types.Abort)
                @add "ret\n"
            else
                @add "ret #{reg}\n"
        else
            @add "ret\n"
        @add_label @fresh_label("unreachable")

    Stop: (ast)=>
        node_assert ast.jump_label, ast, "'stop' statement should only be used inside a loop"
        @add "jmp #{ast.jump_label}\n"
        @add_label @fresh_label("unreachable")

    Skip: (ast)=>
        node_assert ast.jump_label, ast, "'skip' statement should only be used inside a loop"
        @add "jmp #{ast.jump_label}\n"
        @add_label @fresh_label("unreachable")

    Do: (ast)=> @add_value ast

    If: (ast)=> @add_value ast

    When: (ast)=> @add_value ast

    Repeat: (ast)=> @add_repeat_loop ast

    While: (ast)=> @add_while_loop ast

    For: (ast)=>
        iter_reg = @add_value ast.iterable
        key_reg, value_reg = if ast.index and ast.val
            ast.index.__register, ast.val.__register
        elseif ast.val and ast.iterable.__type\works_like_a(Types.TableType)
            ast.val.__register, nil
        elseif ast.val
            nil, ast.val.__register
        else
            nil, nil

        @add_for_loop {
            type: ast.iterable.__type, :iter_reg, :key_reg, :value_reg, scope:{ast.body, ast.between},
            make_body: ->
                if ast.body then
                    code = @new_code!
                    code\add_stmt ast.body
                    code
                else
                    ""
            make_between: ->
                if ast.between then
                    code = @new_code!
                    code\add_stmt ast.between
                    code
                else
                    ""
        }
        return code
        
compile_prog = (ast, filename)->
    env = Environment(filename)
    return tostring(env\compile_program(ast, filename))

return {:compile_prog}
