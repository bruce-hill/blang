Types = require 'types'
import log, viz, id, node_assert, node_error, get_node_pos, print_err, each_tag from require 'util'
import Measure, register_unit_alias from require 'units'
concat = table.concat
local assign_types

parse_type = =>
    return @__parsed_type if @__parsed_type
    switch @__tag
        when "Var","TypeVar"
            if @__declaration
                assign_types @__declaration.__parent unless @__declaration.__type
                @__parsed_type = node_assert @__declaration.__type.type, @, "Couldn't figure out this type"
            else
                error "This type variable wasn't figured out in time"
                node_error @, "This type variable wasn't figured out in time"
                -- @__parsed_type = Types.NamedType(@[0])
        when "OptionalType"
            nonnil = node_assert parse_type(@nonnil), @nonnil, "Couldn't parse this type"
            @__parsed_type = Types.OptionalType(nonnil)
        when "MeasureType"
            m = Measure(1, @[0]\gsub("[<>]",""))
            @__parsed_type = Types.MeasureType(m.str)\normalized!
        when "TupleType"
            t = Types.StructType("")
            @__parsed_type = t
            for memgroup in *@members
                member_type = parse_type memgroup.type
                return unless member_type
                for name in *memgroup.names
                    t\add_member name[0], member_type, (name.inline and true or false)
        when "TableType"
            key = node_assert parse_type(@keyType), @keyType, "Couldn't parse this type"
            val = node_assert parse_type(@valueType), @valueType, "Couldn't parse this type"
            @__parsed_type = Types.TableType(key, val)
        when "ListType"
            item = node_assert parse_type(@itemType), @itemType, "Couldn't parse this type"
            @__parsed_type = Types.ListType(item)
        when "FnType"
            ret_type = if @returnType
                node_assert parse_type(@returnType), @returnType, "Couldn't parse this type"
            else
                Types.NilType
            arg_types = {}
            arg_names = {}
            for arg in *@args
                table.insert arg_names, arg.name[0] if arg.name
                arg_t = node_assert parse_type(arg.type), arg, "Couldn't parse this type"
                table.insert arg_types, arg_t

            if #arg_names == 0 and #arg_types > 0
                arg_names = nil
            @__parsed_type = Types.FnType(arg_types, ret_type, arg_names)
        else
            error "Not implemented: #{@__tag}"
    return @__parsed_type

get_fn_type = (fndec)->
    ret_type = node.returnType and parse_type(node.returnType) or Types.NilType
    return Types.FnType([parse_type a.type for a in *node.args], ret_type, [a.name[0] for a in *node.args])

bind_var = (scope, var)->
    assert var.__tag == "Var" or var.__tag == "TypeVar", "Not a Var: #{var.__tag}"
    switch scope.__tag
        when "Var"
            if scope[0] == var[0]
                scope.__declaration = var
        when "FnDecl","Lambda","ConvertDecl"
            if scope.selfVar and scope.selfVar[0] == var[0]
                return
            for arg in *scope.args
                if arg.name[0] == var[0]
                    -- Don't hook up shadowed args
                    return
            bind_var scope.body, var
        when "FnType"
            return
        else
            for k,child in pairs scope
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                bind_var child, var

bind_type = (scope, typevar)->
    switch scope.__tag
        when "TypeVar"
            if scope[0] == typevar[0]
                scope.__declaration = typevar
        when "TypeDeclaration","StructDeclaration","UnionDeclaration","EnumDeclaration","UnitDeclaration"
            return if scope.name[0] == typevar[0] -- Shadowing
            for k,child in pairs scope
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                bind_type child, typevar
        else
            for k,child in pairs scope
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                bind_type child, typevar

bind_all_types = =>
    switch @__tag
        when "TypeDeclaration","StructDeclaration","UnionDeclaration","EnumDeclaration","UnitDeclaration"
            @name.__declaration = @name
            bind_var @__parent, @name
            bind_type @__parent, @name
            for k,child in pairs @
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                bind_var child, @name
                bind_type child, @name
        else
            for k,child in pairs @
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                bind_all_types child

table.find = (t, obj)->
    for k,v in pairs t
        if v == obj
            return k

bind_variables = =>
    switch @__tag
        when "Declaration"
            @var.__declaration = @var
            switch @__parent.__tag
                when "Block"
                    pos = table.find(@__parent, @)
                    for i=pos+1,#@__parent
                        bind_var @__parent[i], @var
                    if @__parent.__parent
                        switch @__parent.__parent.__tag
                            when "For","While","Repeat"
                                if @__parent == @__parent.__parent.body and @__parent.__parent.between
                                    bind_var @__parent.__parent.between, @var
                when "Clause"
                    bind_var @__parent.body, @var
            bind_variables @var
            bind_variables @value
        when "FnDecl","Lambda","ConvertDecl"
            @name.__declaration = @name if @name
            if @selfVar
                @selfVar.__declaration = @selfVar
                bind_var @body, @selfVar
            for arg in *@args
                arg.name.__declaration = arg.name
                bind_var @body, arg.name
            bind_var @body, @name if @name
            bind_var @__parent, @name if @name
            bind_variables @body
            if @__parent.__parent
                switch @__parent.__parent.__tag
                    when "For","While","Repeat"
                        if @__parent == @__parent.__parent.body and @__parent.__parent.between
                            bind_var @__parent.__parent.between, @name
        when "TypeDeclaration","StructDeclaration","UnionDeclaration","EnumDeclaration","UnitDeclaration"
            for k,child in pairs @
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                bind_variables child
        when "Extern"
            @name.__declaration = @name
            @name.__register = "$"..@name[0]
            bind_var @__parent, @name
            if @__parent.__parent
                switch @__parent.__parent.__tag
                    when "For","While","Repeat"
                        if @__parent == @__parent.__parent.body and @__parent.__parent.between
                            bind_var @__parent.__parent.between, @name
        when "Use"
            error "Not implemented"
        when "For"
            if @index
                @index.__declaration = @index
                bind_var @body, @index
                bind_var @between, @index if @between
                bind_var @filter, @index if @filter
            if @val
                @val.__declaration = @val
                bind_var @body, @val
                bind_var @between, @val if @between
                bind_var @filter, @val if @filter

            bind_variables @body
            bind_variables @between if @between
            bind_variables @filter if @filter
        else
            for k,child in pairs @
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                bind_variables child

assign_types = =>
    return unless type(@) == "table"
    switch @__tag
        when "Nil"
            @__type = Types.NilType
        when "Bool"
            @__type = Types.Bool
        when "String","Escape","Newline","FieldName"
            for interp in *(@content or {})
                assign_types interp
            @__type = Types.String
        when "Interp"
            assign_types @value
            @__type = @value.__type
        when "DSL"
            assign_types @content
            if not @name or @name[0] == ""
                @__type = Types.String
            else
                @__type = Types.DerivedType(@name[0], Types.String)
        when "TypeOf"
            assign_types @expression
            @__type = Types.TypeValue(@expression.__type) if @expression.__type
        when "SizeOf"
            assign_types @expression
            @__type = Types.Int
        when "Range"
            assign_types @first if @first
            assign_types @next if @next
            assign_types @last if @last
            @__type = Types.Range
        when "Pass"
            @__type = Types.NilType
        when "Stop","Skip","Fail"
            for k,child in pairs @
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                assign_types child
            @__type = Types.Abort
        when "Return"
            assign_types @value if @value
            @__type = Types.Abort
        when "Float"
            -- TODO: support 0.5:Num32 without casting
            @__type = Types.Num
        when "Percent"
            @__type = Types.Percent
        when "Measure"
            m = Measure(1, @units[0]\gsub("[<>]",""))
            @__type = Types.MeasureType(m.str)\normalized!

        when "Int"
            -- TODO: support 0.5:Int8 without casting
            @__type = Types.Int

        when "Declaration"
            assign_types @value
            @__type = @value.__type
            @var.__type = @value.__type

        when "Extern"
            @name.__type = parse_type @type

        when "Cast","As"
            assign_types @expr
            @__type = parse_type(@type)

        when "Var"
            if @__declaration
                @__type = @__declaration.__type

        when "Lambda"
            for arg in *@args
                arg.__type = parse_type(arg.type)
                arg.name.__type = arg.__type
            assign_types @body
            if @body and @body.__type
                @__type = Types.FnType([a.__type for a in *@args], @body.__type, [a.name[0] for a in *@args])

        when "FnDecl"
            if @selfVar
                node_assert @__parent.__tag == "StructDeclaration", @, "Method definition is not inside a struct"
                @selfVar.__type = @__parent.__type
                return unless @selfVar.__type
            for arg in *@args
                arg.__type = parse_type(arg.type)
                arg.name.__type = arg.__type
            ret = @returnType and parse_type(@returnType) or Types.NilType
            arg_types = [a.__type for a in *@args]
            arg_names = [a.name[0] for a in *@args]
            if @selfVar
                table.insert arg_types, 1, @selfVar.__type
                table.insert arg_names, 1, @selfVar[0]
            @__type = Types.FnType(arg_types, ret, arg_names)
            @name.__type = @__type
            assign_types @body

        when "ConvertDecl"
            for arg in *@args
                arg.__type = parse_type(arg.type)
                arg.name.__type = arg.__type
            ret = @returnType and parse_type(@returnType) or Types.NilType
            arg_types = [a.__type for a in *@args]
            arg_names = [a.name[0] for a in *@args]
            if @selfVar
                table.insert arg_types, 1, @selfVar.__type
                table.insert arg_names, 1, @selfVar[0]
            @__type = Types.FnType(arg_types, ret, arg_names)
            assign_types @body

        when "FnCall"
            assign_types @fn
            for arg in *@
                assign_types arg
            if not @__type and @fn.__type
                node_assert @fn.__type\is_a(Types.FnType), @fn, "Not a function"
                @__type = @fn.__type.return_type

        when "StructDeclaration"
            t = Types.StructType(@name[0])
            @__type = Types.TypeValue(t)
            @name.__type = @__type if @name
            for member in *@
                if member.__tag == "StructField"
                    member_type = node_assert parse_type(member.type), member.type, "Couldn't parse this type"
                    for name in *member.names
                        name.__type = member_type
                        t\add_member name[0], member_type, (name.inline and true or false)
            @__methods = {}
            for member in *@
                if member.__tag == "FnDecl"
                    if member.selfVar
                        member.selfVar.__type = t
                        @__methods[member.name[0]] = member
                    assign_types member
                elseif member.__tag == "Declaration"
                    assign_types member

        when "EnumDeclaration"
            t = Types.EnumType(@name[0])
            @__type = Types.TypeValue(t)
            @name.__type = @__type if @name
            for member in *@
                if member.__tag == "EnumField"
                    value = member.value and tonumber(member.value[0])
                    t\add_field member.name[0], value

        when "Struct"
            for member in *@
                assign_types member
            if @name
                if @name.__declaration
                    struct_dec = @name.__declaration.__parent
                    node_assert struct_dec.__tag == "StructDeclaration", @name, "This isn't a struct name, it's a #{struct_dec.__tag}"
                    @__type = struct_dec.__type.type
            else
                t = Types.StructType("")
                i = 1
                for member in *@
                    return unless member.value.__type
                    if member.name
                        t\add_member member.name[0], member.value.__type
                    else
                        t\add_member i, member.value.__type
                        i += 1
                @__type = t

        when "UnionDeclaration"
            t = Types.StructType(@name[0])
            @__type = Types.TypeValue(t)
            for member in *@
                member_type = parse_type member.type
                for name in *member.names
                    name.__type = member_type
                    t\add_member name[0], member_type, (name.inline and true or false)
            @name.__type = @__type if @name

        when "TypeDeclaration"
            derived = parse_type(@derivesFrom)
            if derived
                @__type = Types.TypeValue(Types.DerivedType(@name[0], derived))
                @name.__type = @__type

        when "List"
            if @type
                @__type = parse_type(@type)

            item_type = (item)->
                if item.__tag == "For" or item.__tag == "While"
                    return item.body[1].__type
                elseif item.__tag == "If"
                    return item[1].body[1].__type
                else
                    return item.__type

            for item in *@
                assign_types item
                -- node_assert item_type(item), item, "Couldn't get the type here #{item.__tag}"

            t = @__type and @__type.item_type or nil
            for item in *@
                t2 = item_type(item)
                return unless t2
                t = node_assert t2\orelse(t), item, "This list item has type #{t2}, but earlier items have type #{t}"

            @__type = Types.ListType(t)

        when "Table"
            if @type
                @__type = Types.TableType(parse_type(@type.keyType), parse_type(@type.valueType))
            
            for entry in *@
                assign_types entry

            kv_types = (item)->
                if item.__tag == "For" or item.__tag == "While"
                    node_assert item.body[1].__tag == "TableEntry", item.body, "Not a valid table comprehension value (expected `[k]=v`)"
                    return item.body[1].key.__type, item.body[1].value.__type
                elseif item.__tag == "If"
                    node_assert item[1].body[1].__tag == "TableEntry", item[1].body, "Not a valid table comprehension value (expected `[k]=v`)"
                    return item[1].body[1].key.__type, item[1].body[1].value.__type
                else
                    node_assert item.__tag == "TableEntry", "Not a valid table entry, expected [k]=v or k=v"
                    return item.key.__type, item.value.__type

            kt,vt = if @__type
                @__type.key_type, @__type.value_type
            else
                nil, nil
            for entry in *@
                kt2,vt2 = kv_types(entry)
                return unless kt2 and vt2
                kt = node_assert kt2\orelse(kt), entry.key, "This table key has type #{kt2}, but earlier keys have type #{kt}"
                vt = node_assert vt2\orelse(vt), entry.value, "This table value has type #{vt2}, but earlier values have type #{vt}"

            @__type = Types.TableType(kt, vt)
                
        when "IndexedTerm"
            assign_types @value
            assign_types @index
            return unless @value.__type

            t = @value.__type
            index_type = @index.__type

            if t\works_like_a(Types.ListType)
                return unless index_type
                if index_type == Types.Int
                    @__type = t.item_type
                elseif index_type == Types.Range
                    @__type = t
                elseif @index.__tag == "FieldName"
                    ListMethods = require 'list_methods'
                    -- List methods:
                    if t_fn = ListMethods.types[@index[0]]
                        @__type = t_fn(t)
                        @__method = ListMethods.methods[@index[0]]
                        @__inline_method = ListMethods.methods[@index[0]]
                    else
                        node_error @index, "#{@index[0]} is not a valid List method"
                else
                    node_error @index, "Index has type #{index_type}, but expected Int or Range"
            elseif t\works_like_a(Types.TableType)
                return unless index_type
                node_assert index_type == t.key_type, @index, "This table has type #{t}, but is being indexed with #{index_type}"
                @__type = t.value_type
            elseif t\works_like_a(Types.StructType)
                if @index.__tag == "FieldName"
                    member_name = @index[0]
                    member_type = if t.members[member_name]
                        t.members[member_name].type
                    else
                        root = @
                        while root.__parent
                            root = root.__parent

                        method_type = nil
                        for dec in coroutine.wrap(-> each_tag(root, "StructDeclaration"))
                            assign_types dec
                            -- node_assert dec.__type, dec, "WTF no type: #{viz dec}"
                            if dec.__type == t
                                method = dec.__methods[member_name]
                                if method
                                    method_type = method.name.__type
                                    @__method = method.name
                                    @__declaration = method.name
                                    break
                        method_type

                    -- node_assert member_type, @index, "Not a valid struct member of #{t}{#{concat ["#{memb.name}=#{memb.type}" for memb in *t.sorted_members], ", "}}"
                    if member_type
                        @__type = member_type
                elseif @index.__tag == "Int"
                    i = tonumber(@index[0])
                    member_type = node_assert(t.members[i], @, "Not a valid #{t} field: #{i}").type
                    node_assert member_type, @index, "#{t} doesn't have a member #{i}"
                    @__type = member_type
                else
                    node_error @index, "Structs can only be indexed by a field name or Int literal"
            elseif t\works_like_a(Types.String)
                return unless index_type
                if index_type == Types.Int
                    @__type = Types.Int
                elseif index_type == Types.Range
                    @__type = t
                else
                    node_error @index, "Strings can only be indexed by Ints or Ranges"
            elseif t\is_a(Types.TypeValue)
                if t.type\is_a(Types.EnumType)
                    node_assert @index.__tag == "FieldName", @index, "The Enum class #{t} can only be indexed by a valid field name"
                    node_assert t.type.field_values[@index[0]], "#{t.type}.#{@index[0]} is not a valid field in the Enum #{t.type}"
                    @__type = t.type
                else
                    node_error @, "Only Enum types can be indexed, not #{t.type}"
            elseif t\is_a(Types.Percent)
                node_assert @index.__tag == "FieldName", @index, "Percents cannot be indexed"
                PercentMethods = require 'percent_methods'
                if t_fn = PercentMethods.types[@index[0]]
                    @__type = t_fn(t)
                    @__method = PercentMethods.methods[@index[0]]
                    @__inline_method = PercentMethods.methods[@index[0]]
                else
                    node_error @index, "#{@index[0]} is not a valid Percent method"
            elseif t\is_a(Types.Num)
                node_assert @index.__tag == "FieldName", @index, "Nums cannot be indexed"
                NumberMethods = require 'number_methods'
                if t_fn = NumberMethods.types[@index[0]]
                    @__type = t_fn(t)
                    @__method = NumberMethods.methods[@index[0]]
                    @__inline_method = NumberMethods.methods[@index[0]]
                else
                    node_error @index, "#{@index[0]} is not a valid Number method"
            else
                node_error @value, "Indexing is not valid on type #{t}"

        when "Declaration"
            assign_types @value
            @__type = @value.__type
            @key.__type = @__type

        when "Or"
            for item in *@
                assign_types item

            t = nil
            for i, item in ipairs @
                return unless item.__type
                node_assert not t or t\is_a(Types.Bool) or t\is_a(Types.OptionalType), item,
                    "This code is unreachable because the previous value is a #{t}, which is guaranteed to be truthy"
                if not t or t == Types.NilType
                    t = item.__type
                elseif t\is_a(Types.OptionalType)
                    if item.__type == t.nonnil
                        t = t.nonnil
                    elseif item.__type == Types.Abort
                        t = t.nonnil
                        node_assert i == #@, @[i+1], "This code is unreachable"
                    else
                        node_assert item.__type\is_a(t), item, "Expected a value of type `#{t}`, but got `#{item.__type}`"
                elseif item.__type\is_a(Types.Abort)
                    node_assert i == #@, @[i+1], "This code is unreachable"
                elseif item.__type == Types.NilType
                    t = if t
                        Types.OptionalType(t)
                    else
                        Types.NilType
                else
                    node_assert item.__type\is_a(t), item, "Expected a value of type `#{t}`, but got `#{item.__type}`"

            @__type = t

        when "And","Xor"
            items = if @__tag == "Xor"
                {@lhs, @rhs}
            else
                @
            assign_types items[1]
            t = items[1].__type
            return unless t
            for i,item in ipairs items
                assign_types item
                if item.__type == Types.Abort
                    t = Types.Abort
                elseif item.__type\is_a(Types.OptionalType)
                    node_assert item.__type.nonnil\is_a(t), item, "Type mismatch with #{t}"
                    t = Types.OptionalType(t)
                elseif t\is_a(Types.OptionalType)
                    node_assert item.__type\is_a(t), item, "Type mismatch with #{t}"
                else
                    node_assert item.__type == t, item, "Type mismatch with #{t}"
            @__type = t

        when "Equal","NotEqual","Less","LessEq","Greater","GreaterEq"
            assign_types @lhs
            assign_types @rhs
            @__type = Types.Bool

        when "In"
            assign_types @haystack
            assign_types @needle
            @__type = Types.Bool

        when "If"
            for clause in *@
                assign_types clause.condition
                assign_types clause.body
            if @elseBody
                assign_types @elseBody
            t = nil
            for clause in *@
                continue if clause.body.__type == Types.Abort
                return unless clause.body.__type
                t = node_assert clause.body.__type\orelse(t), item, "Type mismatch with #{t}"
            if @elseBody and @elseBody.__type != Types.Abort
                t = node_assert @elseBody.__type\orelse(t), item, "Type mismatch with #{t}"
            elseif not @elseBody
                t = Types.NilType\orelse(t)
            @__type = t

        when "When"
            assign_types @what
            for clause in *@
                for case in *clause.cases
                    assign_types case
                assign_types clause.body
            if @elseBody
                assign_types @elseBody
            t = nil
            for clause in *@
                continue if clause.body.__type == Types.Abort
                return unless clause.body.__type
                t = node_assert clause.body.__type\orelse(t), item, "Type mismatch with #{t}"
            if @elseBody and @elseBody.__type != Types.Abort
                t = node_assert @elseBody.__type\orelse(t), item, "Type mismatch with #{t}"
            elseif not @elseBody
                t = Types.NilType\orelse(t)
            @__type = t

        when "For"
            assign_types @iterable
            iter_type = @iterable.__type
            if iter_type
                if iter_type\works_like_a(Types.TableType)
                    if @index and @val
                        @index.__type = iter_type.key_type
                        @val.__type = iter_type.value_type
                    else
                        @val.__type = iter_type.key_type
                elseif iter_type\works_like_a(Types.ListType)
                    @index.__type = Types.Int if @index
                    @val.__type = iter_type.item_type
                elseif iter_type == Types.Range
                    @index.__type = Types.Int if @index
                    @val.__type = Types.Int
            assign_types @body
            assign_types @between if @between
            assign_types @filter if @filter

        when "Block"
            for stmt in *@
                assign_types stmt
            @__type = @[#@].__type

        when "Do"
            for block in *@
                assign_types block

            t = nil
            for block in *@
                return unless block.__type
                t = block.__type\orelse(t)

            -- TODO: some `do` blocks have no `stop` and thus
            -- may not be optional
            @__type = t == Types.NilType and t or Types.OptionalType(t)

        when "Negative"
            assign_types @value
            return unless @value.__type
            node_assert @value.__type\is_numeric!, @value, "Not a valid type to negate: #{@value.__type}"
            @__type = @value.__type

        when "Not"
            assign_types @value
            @__type = Types.Bool

        when "Len"
            assign_types @value
            @__type = Types.Int

        when "Mod","AddSub","MulDiv","Pow"
            assign_types @lhs or @base
            assign_types @rhs or @exponent
            lhs_t, rhs_t = (@lhs or @base).__type, (@rhs or @exponent).__type
            return unless lhs_t and rhs_t
            if lhs_t == rhs_t and lhs_t\is_numeric!
                @__type = lhs_t
                return

            if @__tag == "AddSub" and @op[0] == "+"
                if lhs_t\works_like_a(Types.String) and rhs_t == lhs_t
                    @__type = lhs_t
                    return
                elseif lhs_t\works_like_a(Types.ListType)
                    if rhs_t == lhs_t
                        @__type = lhs_t
                        return
                    elseif rhs_t\is_a(lhs_t.item_type)
                        @__type = lhs_t
                        return
                elseif rhs_t\works_like_a(Types.ListType) and lhs_t\is_a(rhs_t.item_type)
                    @__type = rhs_t
                    return

            node_error @, "Operands are not compatible: `#{lhs_t}` vs `#{rhs_t}`"

        when "ButWith","ButWithUpdate"
            assign_types @base
            for override in *@
                assign_types override
            @__type = @base.__type

        else
            for k,child in pairs @
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                assign_types child
            @__type = Types.NilType

assign_all_types = (ast)->
    get_all = (field)->
        vals = {}
        recurse = =>
            vals[@] = @[field]
            for k,child in pairs @
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                recurse child
        recurse ast
        return vals

    for extern in coroutine.wrap(-> each_tag(ast, "Extern"))
        bind_var extern.__parent, extern.name
        extern.name.__register = "$"..extern.name[0]

    while true
        progress = false

        pre_decls = get_all("__declaration")
        bind_all_types ast
        post_decls = get_all("__declaration")
        for k,v in pairs post_decls
            if pre_decls[k] != post_decls[k]
                progress = true
                break

        pre_decls = get_all("__declaration")
        bind_variables ast
        post_decls = get_all("__declaration")
        for k,v in pairs post_decls
            if pre_decls[k] != post_decls[k]
                progress = true
                break

        pre_types = get_all("__type")
        assign_types ast
        post_types = get_all("__type")
        for k,v in pairs post_types
            if pre_types[k] != post_types[k]
                progress = true
                break

        break if not progress

    -- for var in coroutine.wrap(-> each_tag(ast, "Var","TypeVar"))
    --     node_assert var.__declaration, var, "Couldn't determine what this variable refers to"

get_type = (ast, force)->
    if force
        node_assert ast.__type, ast, "Couldn't get type"
    else
        ast.__type

return {
    :assign_all_types,
    :get_type,
    :parse_type,
    :bind_var,
    :bind_type,
}
