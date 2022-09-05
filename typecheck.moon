Types = require 'types'
import log, viz, node_assert, node_error, get_node_pos, print_err, each_tag from require 'util'
import Measure, register_unit_alias from require 'units'
concat = table.concat

parse_type = =>
    return @__parsed_type if @__parsed_type
    switch @__tag
        when "Var","TypeVar"
            if @__declaration
                return parse_type @__declaration
            elseif Types[@[0]]
                return Types[@[0]]
        when "OptionalType"
            nonnil = parse_type(@nonnil)
            return unless nonnil
            return Types.OptionalType(nonnil)
        when "MeasureType"
            m = Measure(1, @[0]\gsub("[<>]",""))
            return Types.MeasureType(m.str)\normalized!
        when "TupleType"
            t = Types.StructType("")
            for memgroup in *@members
                member_type = parse_type memgroup.type
                return unless member_type
                for name in *memgroup.names
                    t\add_member name[0], member_type, (name.inline and true or false)
            return t
        when "TableType"
            key = parse_type @keyType
            return unless key
            val = parse_type @valueType
            return unless val
            return Types.TableType(key, val)
        when "TableType"
            item = parse_type @itemtype
            return unless item
            return Types.ListType(item)
        when "FnType"
            ret_type = parse_type @returnType
            arg_types = {}
            for arg in *@args
                arg_t = parse_type arg
                return unless arg_t
                table.insert arg_types, arg_t
            return Types.FnType(arg_types, ret_type)

get_fn_type = (fndec)->
    ret_type = node.returnType and parse_type(node.returnType) or Types.NilType
    return Types.FnType([parse_type a.type for a in *node.args], ret_type, [a.arg[0] for a in *node.args])

bind_var = (scope, var)->
    assert var.__tag == "Var", "Not a Var: #{var.__tag}"
    switch scope.__tag
        when "Var"
            if scope[0] == var[0]
                print "Bound: #{var[0]}"
                scope.__declaration = var
        when "FnDecl","Lambda"
            for arg in *scope.args
                if arg.arg[0] == var[0]
                    -- Don't hook up shadowed args
                    return
            bind_var scope.body, var
        else
            for k,child in pairs scope
                continue if type(child) != "table" or (type(k) == "string" and k\match("^__"))
                bind_var child, var

bind_type = (scope, typevar)->
    switch scope.__tag
        when "TypeVar"
            if scope[0] == typevar[0]
                scope.__declaration = typevar
        when "Var"
            if scope[0] == typevar[0]
                scope.__declaration = typevar
        when "TypeDeclaration","StructDeclaration","UnionDeclaration","EnumDeclaration","UnitDeclaration"
            if scope.name[0] == typevar[0]
                scope.__declaration = typevar
        else
            for k,v in pairs scope
                continue if type(v) != "table" or (type(k) == "string" and k\match("^__"))
                bind_var v, typevar

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
                when "Clause"
                    bind_var @__parent.body, @var
            bind_variables @var
            bind_variables @value
        when "FnDecl"
            @name.__declaration = @name
            for arg in *@
                arg.name.__declaration = arg.name
                bind_var @body, arg.name
            bind_var @body, @name
            bind_var @__parent, @name
            bind_variables @body
        when "Lambda"
            for arg in *@
                arg.name.__declaration = arg.name
                bind_var @body, arg.name
            bind_variables @body
        when "TypeDeclaration","StructDeclaration","UnionDeclaration","EnumDeclaration","UnitDeclaration"
            @name.__declaration = @name
            bind_type @__parent, @name
            bind_variables @
        when "Extern"
            @name.__declaration = @name
            bind_var @__parent, @name
        when "Use"
            error "Not implemented"
        when "For"
            if @index
                @index.__declaration = @index
                bind_var @body, @index
                bind_var @between, @index if @between
            if @val
                @val.__declaration = @val
                bind_var @body, @val
                bind_var @between, @val if @between

            bind_variables @body
            bind_variables @between if @between
        else
            for k,v in pairs @
                continue if type(v) != "table" or (type(k) == "string" and k\match("^__"))
                bind_variables v

type_or = (t1, t2)->
    if t1 == nil or t2 == nil
        return t1 or t2
    elseif t1\is_a(t2)
        return t2
    elseif t2\is_a(t1)
        return t1
    elseif t1 == Types.Nil
        return Types.OptionalType(t2)
    elseif t2 == Types.Nil
        return Types.OptionalType(t1)
    else
        return nil

assign_types = =>
    return unless type(@) == "table" and @__tag
    switch @__tag
        when "Nil"
            @__type = Types.NilType
        when "Bool"
            @__type = Types.BoolType
        when "String","Escape","Newline","FieldName"
            for interp in *@content
                assign_types interp
            @__type = Types.String
        when "Interp"
            assign_types @value
            @__type = @value.__type
        when "DSL"
            for interp in *@content
                assign_types interp
            if @name and @name[0] != ""
                @__type = Types.String
            else
                @__type = Types.DerivedType(@name[0], Types.String)
        when "TypeOf"
            @__type = Types.TypeString
        when "SizeOf"
            @__type = Types.Int
        when "Range"
            @__type = Types.Range
        when "Pass"
            @__type = Types.NilType
        when "Stop","Skip","Fail"
            @__type = Types.Abort
        when "Return"
            assign_types @value if @value
            @__type = Types.Abort
        when "Float"
            if @__parent.__tag == "Cast"
                @__type = @__parent.__type
            else
                @__type = Types.Num
        when "Percent"
            @__type = Types.Percent
        when "Measure"
            m = Measure(1, @units[0]\gsub("[<>]",""))
            return Types.MeasureType(m.str)\normalized!

        when "Int"
            if @__parent.__tag == "Cast"
                @__type = @__parent.__type
            else
                @__type = Types.Int

        when "Declaration"
            assign_types @value
            @__type = @value.__type
            @var.__type = @value.__type

        when "Cast"
            assign_types @value
            @__type = parse_type(@type)

        when "Var"
            if @__declaration
                @__type = @__declaration.__type

        when "Lambda"
            for arg in *@args
                arg.__type = parse_type(arg.type)
                arg.arg.__type = arg.__type
            assign_types @body
            if @body and @body.__type
                @__type = Types.FnType([a.__type for a in *@args], @body.__type, [a.arg[0] for a in *@args])

        when "FnDecl"
            for arg in *@args
                arg.__type = parse_type(arg.type)
                arg.arg.__type = arg.__type
            ret = @returnType and parse_type(@returnType) or Types.NilType
            @__type = Types.FnType([a.__type for a in *@args], @body.__type, [a.arg[0] for a in *@args])
            @name.__type = @__type
            assign_types @body

        when "FnCall"
            assign_types @fn
            for arg in *@
                assign_types arg
            if @fn.__type
                node_assert @fn.__type\is_a(Types.FnType), @fn, "Not a function"
                @__type = @fn.__type.return_type

        when "StructDeclaration"
            t = Types.StructType(@name[0])
            for member in *@
                if member.__tag == "StructField"
                    member_type = parse_type member.type
                    for name in *member.names
                        name.__type = member_type
                        t\add_member name[0], member_type, (name.inline and true or false)
                elseif member.__tag == "FnDecl"
                    assign_types member

        when "UnionDeclaration"
            t = Types.StructType(@name[0])
            for member in *@
                if member.__tag == "StructField"
                    member_type = parse_type member.type
                    for name in *member.names
                        name.__type = member_type
                        t\add_member name[0], member_type, (name.inline and true or false)
                elseif member.__tag == "FnDecl"
                    assign_types member

        when "List"
            if @type
                return Types.ListType(parse_type(@type))
            else
                for item in *@
                    assign_types item
                    if not item.__type
                        node_error item, "Couldn't get the type here #{item.__tag}"
                switch @[1].__tag
                    when "For","While","If"
                        item_type = @[1].body[1].__type
                        return unless item_type
                        @__type = Types.ListType(item_type)
                    else
                        item_type = @[1].__type
                        return unless item_type
                        @__type = Types.ListType(item_type)

        when "Table"
            if @type
                return Types.TableType(parse_type(@type.keyType), parse_type(@type.valueType))
            else
                for entry in *@
                    assign_types entry
                switch @[1].__tag
                    when "TableEntry"
                        key_type, value_type = @[1].key.__type, @[1].value.__type
                        return unless key_type and value_type
                        @__type = Types.TableType(key_type, value_type)
                    when "For","While","If"
                        assert_node @[1].body[1].__tag == "TableEntry", @[1].body[1], "Table comprehension should have a [key]=value pair"
                        key_type, value_type = @[1].body[1].key.__type, @[1].body[1].value.__type
                        return unless key_type and value_type
                        @__type = Types.TableType(key_type, value_type)
                        

        when "IndexedTerm"
            assign_types @value
            assign_types @index
            return unless @value.__type and @index.__type

            value_type = @value.__type
            is_optional = value_type\is_a(Types.OptionalType) and value_type != Types.NilType
            t = is_optional and value_type.nonnil or value_type
            index_type = @index.__type

            if t\is_a(Types.ListType)
                if index_type == Types.Int or index_type == Types.OptionalType(Types.Int)
                    @__type = Types.OptionalType(t.item_type)
                elseif index_type == Types.Range
                    @__type = is_optional and Types.OptionalType(t) or t
                else
                    node_error node.index, "Index has type #{index_type}, but expected Int or Range"
            elseif t\is_a(Types.TableType)
                node_assert index_type == t.key_type, node.index, "This table has type #{t}, but is being indexed with #{index_type}"
                @__type = Types.OptionalType(t.value_type)
            elseif t\is_a(Types.StructType)
                if @index.__tag == "FieldName"
                    member_name = @index[1][0]
                    node_assert t.members[member_name], @index, "Not a valid struct member of #{t}{#{concat ["#{memb.name}=#{memb.type}" for memb in *t.sorted_members], ", "}}"
                    member_type = t.members[member_name].type
                    @__type = is_optional and Types.OptionalType(member_type) or member_type
                elseif node.index.__tag == "Int"
                    i = tonumber(node.index[0])
                    member_type = node_assert(t.members[i], node, "Not a valid #{t} field: #{i}").type
                    node_assert member_type, @index, "#{t} doesn't have a member #{i}"
                    @__type = is_optional and Types.OptionalType(member_type) or member_type
                else
                    node_error @index, "Structs can only be indexed by a field name or Int literal"
            elseif t\is_a(String)
                if index_type == Types.Int
                    @__type = Types.OptionalType(Types.Int)
                elseif index_type == Types.Range
                    @__type = t
                else
                    node_error node.index, "Strings can only be indexed by Ints or Ranges"
            else
                node_error node.value, "Indexing is not valid on type #{t}"

        when "Declaration"
            assign_types @value
            @__type = @value.__type
            @key.__type = @__type

        when "Or"
            for item in *@
                assign_types item

            t = nil
            for item in *@
                return unless item.__type
                if item.__type == Types.Abort
                    if t and t\is_a(Types.OptionalType)
                        t = t.nonnil
                    break
                t = node_assert type_or(t, item.__type), item, "Type mismatch with #{t}"
            @__type = t

        when "And","Or","Xor"
            t = items[1].__type
            return unless t
            for i,item in ipairs @
                assign_types item
                if item.__type == Types.Abort
                    if @__tag == "Or"
                        if t\is_a(Types.OptionalType)
                            t = t.nonnil
                    else
                        t = Types.Abort
                elseif item.__type\is_a(Types.OptionalType)
                    node_assert item.__type.nonnil\is_a(t), item, "Type mismatch with #{t}"
                    t = Types.OptionalType(t)
                elseif t\is_a(Types.OptionalType)
                    node_assert item.__type\is_a(t), item, "Type mismatch with #{t}"
                else
                    node_assert item.__type == t, item, "Type mismatch with #{t}"
            @__type = t

        when "Equal","NotEqual","Less","LessEq","Greater","GreaterEq","In"
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
                t = node_assert type_or(t, clause.body.__type), item, "Type mismatch with #{t}"
            if @elseBody and @elseBody.__type != Types.Abort
                t = node_assert type_or(t, @elseBody.__type), item, "Type mismatch with #{t}"
            elseif not @elseBody
                t = type_or(t, Types.NilType)
            @__type = t
        
        when "For"
            assign_types @iterable
            iter_type = @iterable.__type
            if iter_type
                if iter_type\is_a(Types.TableType)
                    if @index and @val
                        @index.__type = iter_type.key_type
                        @val.__type = iter_type.value_type
                    else
                        @val.__type = iter_type.key_type
                elseif iter_type\is_a(Types.ListType)
                    @index.__type = Types.Int if @index
                    @val.__type = iter_type.item_type
                elseif iter_type == Types.Range
                    @index.__type = Types.Int if @index
                    @val.__type = Types.Int
            assign_types @body
            assign_types @between if @between

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
                t = node_assert type_or(t, clause.body.__type), item, "Type mismatch with #{t}"
            if @elseBody and @elseBody.__type != Types.Abort
                t = node_assert type_or(t, @elseBody.__type), item, "Type mismatch with #{t}"
            elseif not @elseBody
                t = type_or(t, Types.NilType)
            @__type = t

        when "Do"
            for block in *@
                assign_types block
            @__type = Types.NilType

        when "Negative"
            assign_types @value
            return unless @value.__type
            node_assert @value.__type\is_numeric!, "Not a valid type to negate: #{@value.__type}"
            @__type = @value.__type

        when "Not"
            assign_types @value
            @__type = Types.Bool

        when "Len"
            assign_types @value
            @__type = Types.Int

        when "Mod","AddSub","MulDiv","Pow"
            assign_types @lhs
            assign_types @rhs
            return unless @lhs.__type and @rhs.__type
            if @lhs.__type == @rhs.__type and @lhs.__type\is_numeric!
                @__type = @lhs.__type

        when "ButWith"
            assign_types @base
            for override in *@
                assign_types @override
            @__type = @base.__type

        else
            for k,v in pairs @
                continue if type(k) == "string" and k\match("^__")
                assign_types v
            @__type = Types.NilType

assign_all_types = (ast)->
    get_all = (field)->
        vals = {}
        recurse = =>
            vals[@] = @[field]
            for k,v in pairs @
                continue if type(v) != "table" or (type(k) == "string" and k\match("^__"))
                recurse v
        recurse ast
        return vals

    while true
        progress = false

        print "Binding variables..."
        pre_decls = get_all("__declaration")
        bind_variables ast
        post_decls = get_all("__declaration")
        for k,v in pairs post_decls
            if pre_decls[k] != post_decls[k]
                progress = true
                break
        
        print "Assigning types..."
        pre_types = get_all("__type")
        assign_types ast
        post_types = get_all("__type")
        for k,v in pairs post_types
            if pre_types[k] != post_types[k]
                progress = true
                break

        break if not progress

    print "Finished assigning types!"
    print viz(ast)

    for var in coroutine.wrap(-> each_tag("Var","TypeVar"))
        assert_node var.__declaration, var, "Couldn't determine what this variable refers to"

get_type = (ast)-> ast.__type

return {
    :assign_all_types,
    :get_type,
    :parse_type,
}
