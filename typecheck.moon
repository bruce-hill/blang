-- Type checking/inference logic
concat = table.concat
import log, viz, print_err, node_assert, node_error, each_tag from require 'util'
import Measure, register_unit_alias from require 'units'
parse = require 'parse'

local get_type, parse_type, get_module_type

class Type
    is_a: (cls)=> @ == cls or @.__class == cls or cls\contains @
    contains: (other)=> @ == other
    base_type: 'l'
    abi_type: 'l'
    bytes: 8
    nil_value: 0x7FFFFFFFFFFFFFFF
    id_str: => tostring(@)\gsub('[^%w%d.]','')
    __eq: (other)=> type(other) == type(@) and other.__class == @__class and tostring(other) == tostring(@)
    verbose_type: => "#{@}"

class NamedType extends Type
    new: (@name)=>
    __tostring: => @name
    __eq: Type.__eq

Value = NamedType("Value")
Value.contains = (other)=> other.bytes == @bytes
Value.is_a = (other)=> other == @ or other == @__class
Value.nil_value = 0x7FFFFFFFFFFFFFFF

Value32 = NamedType("Value32")
Value32.contains = (other)=> other.bytes == @bytes
Value32.is_a = (other)=> other == @ or other == @__class
Value32.base_type = 'w'
Value32.abi_type = 'w'
Value32.bytes = 4
Value32.nil_value = 0x7FFFFFFF

Value16 = NamedType("Value16")
Value16.contains = (other)=> other.bytes == @bytes
Value16.is_a = (other)=> other == @ or other == @__class
Value16.base_type = 'w'
Value16.abi_type = 'h'
Value16.bytes = 2
Value16.nil_value = 0x7FFF

Value8 = NamedType("Value8")
Value8.contains = (other)=> other.bytes == @bytes
Value8.is_a = (other)=> other == @ or other == @__class
Value8.base_type = 'w'
Value8.abi_type = 'b'
Value8.bytes = 1
Value8.nil_value = 0x7F

class DerivedType extends Type
    new: (@name, @derived_from)=>
        @base_type = @derived_from.base_type
        @abi_type = @derived_from.abi_type
        @bytes = @derived_from.bytes
        @nil_value = @derived_from.nil_value
    __tostring: => @name
    __eq: Type.__eq
    is_a: (cls)=> @ == cls or @derived_from\is_a(cls) or @.__class == cls or cls\contains(@)

local Num
class MeasureType extends Type
    new: (@units)=>
    normalized: => @units == "" and assert(Num) or @
    base_type: 'd'
    abi_type: 'd'
    __tostring: => "<#{@units}>"
    __eq: Type.__eq
    is_a: (cls)=> @ == cls or @.__class == cls or cls\contains @

class ListType extends Type
    new: (@item_type)=>
    __tostring: => "[#{@item_type}]"
    id_str: => "#{@item_type\id_str!}.List"
    __eq: Type.__eq
    is_a: (cls)=> cls == @ or cls == @__class or (cls.__class == ListType and @item_type\is_a(cls.item_type)) or cls\contains(@) or cls\contains(@)
    nil_value: 0

class TableType extends Type
    new: (@key_type, @value_type)=>
        assert @key_type and @value_type
    __tostring: => "{#{@key_type}=#{@value_type}}"
    id_str: => "#{@key_type\id_str!}.#{@value_type\id_str!}.Table"
    is_a: (cls)=> cls == @ or cls == @__class or (cls.__class == TableType and @key_type\is_a(cls.key_type) and @value_type\is_a(cls.value_type)) or cls\contains(@)
    __eq: Type.__eq
    nil_value: 0

dbg = (t)->
    if type(t) == 'table'
        "{#{concat [dbg(k).."="..dbg(v) for k,v in pairs(t)], ", "}}"
    else
        tostring(t)

local OptionalType
class FnType extends Type
    new: (@arg_types, @return_type, @arg_names=nil)=>
    __tostring: => "#{@arg_signature!}=>#{@return_type}"
    __eq: Type.__eq
    nil_value: 0
    id_str: => "Fn"
    arg_signature: => "(#{concat ["#{a}" for a in *@arg_types], ","})"
    matches: (arg_types, return_type=nil)=>
        if @arg_names
            unmatched = {name,@arg_types[i] for i,name in ipairs @arg_names}
            for name,t in pairs arg_types
                continue unless type(name) == 'string'
                return false unless unmatched[name] and t\is_a(unmatched[name])
                unmatched[name] = nil

            i,j = 1,1
            while i <= #arg_types and j <= #@arg_names
                t = unmatched[@arg_names[j]]
                if t
                    return false unless arg_types[i]\is_a(t)
                    unmatched[@arg_names[j]] = nil
                    i += 1
                j += 1
                
            for _,t in pairs unmatched
                return false unless t\is_a(OptionalType)
        else
            return false unless #arg_types == #@arg_types
            for i=1,#arg_types
                return false unless arg_types[i]\is_a(@arg_types[i])

        if return_type
            return false unless @return_type\is_a(return_type)
        return true

class StructType extends Type
    new: (@name, members)=> -- Members: {{type=t, name="Foo"}, {type=t2, name="Baz"}, ...}
        @members = {}
        @sorted_members = {}
        @memory_size = 0
        if members
            for memb in *members
                @add_member memb.name, memb.type
    add_member: (name, memtype)=>
        offset = @memory_size
        -- Align memory:
        if offset % memtype.bytes != 0
            offset = offset - (offset % memtype.bytes) + memtype.bytes
        @members[name] = {name: name, type: memtype, offset: offset}
        table.insert @sorted_members, @members[name]
        @memory_size = offset + memtype.bytes
    __tostring: => "#{@name}"
    nil_value: 0
    verbose_type: =>
        mem_strs = {}
        for m in *@sorted_members
            t_str = if m.type.__class == StructType
                m.type.name
            else
                "#{m.type}"
            table.insert mem_strs, "#{m.name and m.name..':' or ''}#{m.type}"
        "#{@name}{#{concat mem_strs, ","}}"
    id_str: => "#{@name}"
    __eq: Type.__eq

local EnumType
class UnionType extends Type
    new: (@name, @members)=> -- Members: {{type=t, name="Foo"}, {type=t2, name="Baz"}, ...}
        @abi_type = "l"
        @base_type = "l"
        @memory_size = 16
        @members = {}
        @num_members = 0
        @enum = EnumType(@name)
        if members
            for memb in *members
                @add_member memb.name, memb.type
                @enum\add_field memb.name
    add_member: (name, type)=>
        @num_members += 1
        @members[name] = {type: type, index: @num_members}
    __tostring: => "#{@name}"
    nil_value: 0
    verbose_type: =>
        mem_strs = {}
        for name,info in pairs @members
            t_str = if info.type.__class == UnionType
                info.type.name
            else
                "#{info.type}"
            table.insert mem_strs, "#{name and name..':' or ''}#{info.type}"
        "union #{@name}{#{concat mem_strs, ","}}"
    id_str: => "#{@name}"
    __eq: Type.__eq

Nil = NamedType("Nil")

class OptionalType extends Type
    new: (@nonnil)=>
        assert @nonnil and @nonnil != Nil
        if @nonnil.__class == OptionalType
            @nonnil = assert(@nonnil.nonnil)
        @base_type = @nonnil.base_type
        @abi_type = @nonnil.abi_type
        @nil_value = @nonnil.nil_value
    contains: (other)=> other == @ or other == Nil or (@nonnil and other\is_a(@nonnil))
    __tostring: => @nonnil\is_a(FnType) and "(#{@nonnil})?" or "#{@nonnil}?"
    verbose_type: => @nonnil\is_a(FnType) and "(#{@nonnil\verbose_type!})?" or "#{@nonnil\verbose_type!}?"
    id_str: => "Optional.#{@nonnil\id_str!}"
    __eq: Type.__eq

class EnumType extends Type
    new: (@name, @fields={})=>
    add_field: (name)=> table.insert @fields, name
    nil_value: 0
    __tostring: => @name
    id_str: => @name
    __eq: Type.__eq

-- Primitive Types:
Pointer = NamedType("Pointer")
Pointer.nil_value = 0

Num = NamedType("Num")
Num.base_type = 'd'
Num.abi_type = 'd'
Num32 = NamedType("Num32")
Num32.base_type = 's'
Num32.abi_type = 's'
Num32.bytes = 4
Num32.nil_value = 0x7FFFFFFF

Int = NamedType("Int")
Int.base_type = 'l'
Int.abi_type = 'l'

Int32 = NamedType("Int32")
Int32.base_type = 'w'
Int32.abi_type = 'w'
Int32.bytes = 4
Int32.nil_value = 0x7FFFFFFF

Int16 = NamedType("Int16")
Int16.base_type = 'w'
Int16.abi_type = 'h'
Int16.bytes = 2
Int16.nil_value = 0x7FFF

Int8 = NamedType("Int8")
Int8.base_type = 'w'
Int8.abi_type = 'b'
Int8.bytes = 1
Int8.nil_value = 0xFF

Percent = DerivedType("Percent", Num)

Void = NamedType("Void")

Bool = NamedType("Bool")
Bool.base_type = 'w'
Bool.abi_type = 'b'
Bool.bytes = 1
Bool.nil_value = 0x7F

String = NamedType("String")
String.nil_value = 0
TypeString = DerivedType("TypeString", String)
Range = StructType("Range", {{name:"first",type:Int},{name:"next",type:Int},{name:"last",type:Int}})
Range.item_type = Int
Range.nil_value = 0

primitive_types = {:Value, :Value32, :Value16, :Value8, :Pointer, :Int, :Int32, :Int16, :Int8, :Num, :Num32,
    :Void, :Nil, :Bool, :String, :Range, :OptionalType, :Percent, :TypeString}

tuples = {}
tuple_index = 1

memoize = (fn)->
    cache = setmetatable {}, __mode:'k'
    return (x)->
        unless cache[x]
            cache[x] = fn(x)
        return cache[x]

find_returns = (node)->
    switch node.__tag
        when "Return"
            coroutine.yield(node)
        when "Lambda","FnDecl","Macro"
            return
        else
            for k,child in pairs node
                find_returns(child) if type(child) == 'table' and not (type(k) == 'string' and k\match("^__"))

enclosing_scope = (scope)->
    if scope.__parent and scope.__parent.__tag == "Block"
        i = 1
        while scope.__parent[i] != (scope.__original or scope)
            i += 1
        t = {k,v for k,v in pairs scope.__parent when type(k) != 'number' or k <= i}
        t.__original = scope.__parent
        return t
    else
        return scope.__parent

find_declared_type = (scope, name, arg_types=nil, return_type=nil)->
    return nil unless scope
    switch scope.__tag
        when "Block"
            for i=#scope,1,-1
                stmt = scope[i]
                if stmt.__tag == "FnDecl" and stmt.name[0] == name and (not arg_types or get_type(stmt)\matches(arg_types,return_type))
                    return get_type(stmt)
                elseif stmt.__tag == "Declaration" and stmt.var[0] == name
                    return get_type stmt.value
                elseif stmt.__tag == "Use"
                    -- Naked "use"
                    t = get_module_type(stmt.name[0])
                    mem = t.members[name]
                    if mem and not arg_types
                        return mem.type
                    elseif mem and mem.type\is_a(FnType) and mem.type\matches(arg_types,return_type)
                        return mem.type
        when "Macro"
            return nil
        when "FnDecl","Lambda"
            for a in *scope.args
                if a.arg[0] == name
                    return parse_type(a.type)
        when "FnCall"
            if arg_types == nil and scope.fn.__tag == "Var" and scope.fn[0] == name
                arg_types = {}
                for arg in *scope
                    if arg.__tag == "KeywordArg"
                        arg_types[arg.name[0]] = get_type(arg.value)
                    else
                        table.insert arg_types, get_type(arg)
        when "Clause"
            if scope.condition.__tag == "Declaration" and scope.condition.var[0] == name
                t = get_type(scope.condition.value)
                if t\is_a(OptionalType)
                    return t.nonnil
                else
                    return t
        when "For"
            get_iter_type = ->
                iter_type = if scope.iterable.__tag == "Var"
                    find_declared_type(scope.__parent, scope.iterable[0], arg_types, return_type)
                else get_type(scope.iterable)

                node_assert iter_type, scope.iterable, "Can't determine the type of this variable"
                return iter_type

            if scope.index and scope.index[0] == name
                iter_type = get_iter_type!
                if iter_type\is_a(TableType)
                    return iter_type.key_type
                else
                    return Int
            elseif scope.val and scope.val[0] == name
                iter_type = get_iter_type!
                if iter_type\is_a(TableType)
                    return scope.index and iter_type.value_type or iter_type.key_type
                elseif iter_type\is_a(Range)
                    return Int
                elseif iter_type\is_a(ListType)
                    return iter_type.item_type
                else
                    node_error scope.iterable, "Not an iterable value"

    if scope.__parent and (scope.__parent.__tag == "For" or scope.__parent.__tag == "While" or scope.__parent.__tag == "Repeat")
        loop = scope.__parent
        if (scope.__original or scope) == loop.between
            t = find_declared_type(loop.body, name, arg_types, return_type)
            return t if t

    parent_scope = enclosing_scope scope
    if parent_scope
        return find_declared_type(parent_scope, name, arg_types, return_type)

find_type_alias = (scope, name)->
    while scope
        switch scope.__tag
            when "Block"
                for i=#scope,1,-1
                    stmt = scope[i]
                    if stmt.__tag == "TypeDeclaration" and stmt.name[0] == name
                        return DerivedType(stmt.name[0], parse_type(stmt.derivesFrom))
                    elseif stmt.__tag == "StructDeclaration" and stmt[1].name[0] == name
                        return parse_type stmt[1]
                    elseif stmt.__tag == "UnionDeclaration" and stmt.type.name[0] == name
                        return parse_type stmt.type
                    elseif stmt.__tag == "EnumDeclaration" and stmt.name[0] == name
                        return parse_type stmt
        scope = scope.__parent

derived_types = {}

parse_type = memoize (type_node)->
    return type_node.__type if type_node.__type
    switch type_node.__tag
        when "NamedType","Var"
            if primitive_types[type_node[0]]
                return primitive_types[type_node[0]]
            tmp = type_node.__parent
            while tmp
                if tmp.__tag == "StructType" and tmp.name[0] == type_node[0] and tmp.__type
                    return tmp.__type
                tmp = tmp.__parent
            alias = find_type_alias type_node, type_node[0]
            node_assert alias, type_node, "Undefined type"
            return alias
        when "MeasureType"
            m = Measure(1, type_node[0]\gsub("[<>]",""))
            return MeasureType(m.str)\normalized!
        when "DerivedType"
            unless derived_types[type_node.name[0]]
                derived_types[type_node.name[0]] = DerivedType type_node.name[0], parse_type(type_node.derivesFrom)
            return derived_types[type_node.name[0]]
        when "ListType"
            node_assert type_node.itemtype, type_node, "List without item type"
            return ListType(parse_type(type_node.itemtype))
        when "TableType"
            return TableType(parse_type(type_node.keyType), parse_type(type_node.valueType))
        when "FnType"
            arg_types = [parse_type(a) for a in *type_node.args]
            return FnType(arg_types, parse_type(type_node.return))
        when "StructType"
            t = StructType(type_node.name[0])
            type_node.__type = t
            for m in *type_node.members
                continue unless m.names
                mt = parse_type(m.type)
                for name in *m.names
                    t\add_member name[0], mt
            return t
        when "UnionDeclaration"
            return parse_type(type_node.type)
        when "UnionType"
            t = UnionType(type_node.name[0])
            type_node.__type = t
            for m in *type_node.members
                continue unless m.names
                mt = parse_type(m.type)
                for name in *m.names
                    t\add_member name[0], mt
            return t
        when "EnumDeclaration"
            return EnumType(type_node.name[0], [f[0] for f in *type_node])
        when "OptionalType"
            t = parse_type(type_node.nonnil)
            return OptionalType(t)
        else
            error "Not a type node: #{viz type_node}"

get_op_type = (t1, op, t2)=>
    all_member_types = (t, pred)->
        for mem in *t.sorted_members
            return false unless pred(mem.type)
        return true

    if t1\is_a(MeasureType) and t2\is_a(Num)
        switch op
            when "Mul","Div"
                return t1
    elseif t1\is_a(Num) and t2\is_a(MeasureType)
        if op == "Mul"
            return t1
        elseif op == "Div"
            m2 = Measure(1,t1.units)\invert!
            return MeasureType(m2.str)\normalized!
    elseif t1\is_a(MeasureType) and t2\is_a(MeasureType)
        switch op
            when "Add","Sub"
                return t1 if t1 == t2
            when "Mul"
                m2 = Measure(1,t1.units)*Measure(1,t2.units)
                return MeasureType(m2.str)\normalized!
            when "Div"
                m2 = Measure(1,t1.units)/Measure(1,t2.units)
                return MeasureType(m2.str)\normalized!

    if (t1.nonnil or t1) == (t2.nonnil or t2) and (t1.nonnil or t1)\is_a(Num) and t1.base_type == "d"
        switch op
            when "Add","Sub","Mul","Div","Mod","Pow"
                return t1

    if op == "Add"
        if t1\is_a(ListType) and t2\is_a(t1.item_type)
            return t1
        elseif t2\is_a(ListType) and t1\is_a(t2.item_type)
            return t2

    if t1 == t2
        if t1\is_a(Int)
            switch op
                when "Add","Sub","Mul","Div","Mod","Pow"
                    return t1
        elseif t1\is_a(ListType) and op == "Add"
            return t1
        elseif t1\is_a(String) and op == "Add"
            return t1

    overload_names = Add:"add", Sub:"subtract", Mul:"multiply", Div:"divide", Mod:"modulus", Pow:"raise"
    return unless overload_names[op]
    overload = find_declared_type @, overload_names[op], {t1,t2}
    return overload.return_type if overload

load_module = memoize (path)->
    libpath = path\gsub("([^/]*)$","lib%1.so")
    cmd = io.popen("./getsym #{libpath} source")
    source = cmd\read("a")
    unless cmd\close!
        blpath = path\gsub("([^/]*)$","lib%1.so")
        src_file = io.open(blpath)
        return nil unless src_file
        source = src_file\read("*a")

    ast = parse source, filename
    exports = {}
    for exp in coroutine.wrap(-> each_tag(ast, "Export"))
        for var in *exp
            table.insert(exports, var)
    t = StructType("Module", [{type: get_type(e), name: e[0]} for e in *exports])
    log "Module type #{node.name[0]} = {#{concat ["#{m.name}=#{m.type}" for m in *t.sorted_members], ", "}}"
    return t

get_type = memoize (node)->
    switch node.__tag
        when "Int" then return Int
        when "Float" then return Num
        when "Percent" then return Percent
        when "Measure"
            m = Measure(1, node.units[0]\gsub("[<>]",""))
            return MeasureType(m.str)\normalized!
        when "Declaration" return get_type(node.value)
        when "EnumDeclaration" then return parse_type(node)
        when "Bool" then return Bool
        when "Nil" then return Nil
        when "String","Escape","Newline" then return String
        when "TypeOf" then return TypeString
        when "DSL"
            return String unless node.name
            name = node.name[0]
            unless derived_types[name]
                derived_types[name] = DerivedType name, String
            return derived_types[name]
        when "Range" then return Range
        when "Stop","Skip","Return","Fail"
            return Void
        when "Export"
            return Nil
        when "Use"
            tmp = node.__parent
            while tmp.__parent
                tmp = tmp.__parent
            filename = tmp.__filename

            module_dirname,module_basename = @name[0]\match("(.*/)([^/]*)$")
            if not module_dirname
                module_dirname,module_basename = "",modname

            for search_path in (os.getenv("BLANG_MODULE_PATHS") or ".")\gmatch("[^:]+")
                unless search_path\match("^/")
                    dirname = filename\match("^.*/") or ""
                    search_path = dirname..search_path
                path = "#{search_path}/#{module_dirname}/#{module_basename}"
                t = load_module(path)
                return t if t

            node_error node, "Cannot find module: #{modname}"

        when "Cast" then return parse_type(node.type)
        when "List"
            decl_type = node.type and parse_type(node.type)
            return decl_type if #node == 0
            item_type = (item)->
                switch item.__tag
                    when "If" then return get_type item[1].body[1]
                    when "For","While","Repeat" then return get_type item.body[1]
                    else return get_type item

            t = item_type(node[1])
            if decl_type
                node_assert t == decl_type.item_type, node[1],
                    "List is declared as having type #{decl_type}, but this item has type: #{t}"

            for i=2,#node
                t_i = item_type(node[i])
                node_assert t_i == t, node[i], "Earlier items have type #{t}, but this item is a #{t_i}"

            return ListType(t)
        when "Table"
            decl_type = node.type and parse_type(node.type)
            return decl_type if #node == 0

            entry_types = (entry)->
                e = switch entry.__tag
                    when "If" then entry[1].body[1]
                    when "For","While","Repeat" then entry.body[1]
                    else entry
                node_assert e.__tag == "TableEntry", e, "Expected a table entry here"
                return get_type(e.key), get_type(e.value)

            key_type, value_type = entry_types node[1]

            if decl_type
                node_assert key_type == decl_type.key_type and value_type == decl_type.value_type, node[1], "Not expected type: #{t}"

            for i=2,#node
                t_k, t_v = entry_types node[i]
                node_assert t_k == key_type, node[i].key, "Item is type #{t_k} but should be #{key_type}"
                node_assert t_v == value_type, node[i].value, "Item is type #{t_v} but should be #{value_type}"

            return TableType(key_type, value_type)
        when "IndexedTerm"
            if node.value.__tag == "Var"
                enum = find_type_alias node, node.value[0]
                if enum and enum\is_a(EnumType)
                    for f in *enum.fields
                        if f == node.index[0]
                            return enum
                    node_error node.index, "Not a valid enum field for #{enum.name}"

            t = get_type node.value
            is_optional = t\is_a(OptionalType) and t != Nil
            t = t.nonnil if is_optional
            if t\is_a(ListType)
                index_type = get_type(node.index, vars)
                if index_type == Int or index_type == OptionalType(Int)
                    return OptionalType(t.item_type)
                elseif index_type == Range
                    return is_optional and OptionalType(t) or t
                else
                    node_error node.index, "Index has type #{index_type}, but expected Int or Range"
            elseif t\is_a(TableType)
                index_type = get_type(node.index, vars)
                node_assert index_type == t.key_type, node.index, "This table has type #{t}, but is being indexed with #{index_type}"
                return OptionalType(t.value_type)
            elseif t\is_a(StructType)
                if node.index.__tag == "FieldName"
                    member_name = node.index[0]
                    node_assert t.members[member_name], node.index, "Not a valid struct member of #{t}{#{concat ["#{memb.name}=#{memb.type}" for memb in *t.sorted_members], ", "}}"
                    ret_type = t.members[member_name].type
                    return is_optional and OptionalType(ret_type) or ret_type
                elseif node.index.__tag == "Int"
                    i = tonumber(node.index[0])
                    ret_type = node_assert(t.members[i], node, "Not a valid #{t} field: #{i}").type
                    node_assert ret_type, node.index, "#{t} doesn't have a member #{i}"
                    return is_optional and OptionalType(ret_type) or ret_type
                else
                    node_error node.index, "Structs can only be indexed by a field name or Int literal"
            elseif t\is_a(UnionType)
                node_assert node.index.__tag == "FieldName", node, "Not a union field"
                member_name = node.index[0]
                node_assert t.members[member_name], node.index, "Not a valid union member of #{t}"
                member = t.members[member_name]
                return OptionalType(member.type)
            elseif t\is_a(String)
                index_type = get_type(node.index, vars)
                if index_type == Int
                    return OptionalType(Int)
                elseif index_type == Range
                    return t
                else
                    node_error node.index, "Strings can only be indexed by Ints or Ranges"
            else
                node_error node.value, "Indexing is not valid on type #{t}"
        when "And","Or","Xor"
            all_bools = true
            maybe_nil = false
            types = ["#{get_type val}" for val in *node]
            for val in *node
                t = get_type val
                maybe_nil or= t\is_a(OptionalType) or t == Void
                all_bools and= t == Bool or t == Void
            return Bool if all_bools
            node_assert maybe_nil, node, "Expected either Bool values or something that is possibly nil. Types here are: #{concat types, ", "}"
            optional = nil
            for i,val in ipairs node
                t = get_type val
                continue if t == Nil
                if t == Void
                    if node.__tag == "Or"
                        node_assert optional, node, "WTF: #{concat types, ","}"
                        return optional.nonnil
                    elseif node.__tag == "And"
                        return optional
                    else
                        node_error val, "Failure will always trigger"

                if node.__tag == "Or" and not t\is_a(OptionalType)
                    node_assert i == #node, node[i], "This value is never nil, so subsequent values are ignored"
                    node_assert t == optional.nonnil, val, "Mismatched type: #{t} doesn't match earlier type: '#{optional}'"
                    return t

                if optional
                    node_assert OptionalType(t) == optional, val, "Mismatched type: #{t} doesn't match earlier type: '#{optional}'"
                else
                    optional = OptionalType(t)
            return optional
        when "Equal","NotEqual","Less","LessEq","Greater","GreaterEq"
            return Bool
        when "TernaryOp"
            cond_type = get_type node.condition
            node_assert cond_type\is_a(Bool) or cond_type\is_a(OptionalType), node.condition, "Expected a Bool or optional value here"
            true_type = get_type node.ifTrue
            false_type = get_type node.ifFalse
            if true_type == false_type
                return true_type
            elseif true_type == Nil
                return OptionalType(false_type)
            elseif false_type == Nil
                return OptionalType(true_type)
            else
                node_error node, "Values for true/false branches are different: #{true_type} vs #{false_type}"
        when "AddSub","MulDiv","Mod"
            lhs_type = get_type node.lhs
            rhs_type = get_type node.rhs
            op = if node.__tag == "AddSub"
                node.op[0] == "+" and "Add" or "Sub"
            elseif node.__tag == "MulDiv"
                node.op[0] == "*" and "Mul" or "Div"
            else
                node.__tag
            ret_type = get_op_type(node, lhs_type, op, rhs_type)
            node_assert ret_type, node, "Invalid #{op} types: #{lhs_type} and #{rhs_type}"
            return ret_type
        when "ButWith"
            base_type = get_type node.base
            if base_type\is_a(ListType)
                for index in *node
                    node_assert index.index, index, "field names are not allowed for Lists"
                    i_type = get_type(index.index)
                    value_type = get_type(index.value)
                    if i_type\is_a(Int)
                        node_assert value_type == base_type.item_type, index.value, "Value is #{value_type} not #{base_type.item_type}"
                    elseif i_type\is_a(Range)
                        node_assert value_type == base_type, index.value, "Value is #{value_type} not #{base_type}"
                    else
                        node_error index.index, "Value is #{value_type} not Int or Range"
                return base_type
            elseif base_type\is_a(String)
                for range in *node
                    node_assert range.index, range, "range names are not allowed for Strings"
                    if get_type(range.index)\is_a(Range)
                        value_type = get_type(range.value)
                        node_assert value_type == base_type, range.value, "Value is #{value_type} not #{base_type}"
                    else
                        node_error range.index, "Value is #{value_type} not Range"
                return base_type
            elseif base_type\is_a(StructType)
                for field in *node
                    if field.field
                        node_assert base_type.members[field.field[0]], field.field, "Not a valid struct member of #{base_type}"
                    elseif field.index
                        node_assert field.index.__tag == "Int", field.index, "Only field names and integer literals are supported for using |[..]=.. on Structs"
                        n = tonumber(field.index[0])
                        node_assert base_type.members[n], field.index, "#{base_type} doesn't have a member #{n}"
                return base_type
            else
                node_error node, "| operator is only supported for List and Struct types"

            return base_type
        when "Negative"
            t = get_type node.value
            node_assert t\is_a(Int) or t\is_a(Num) or t\is_a(Range), node, "Invalid negation type: #{t}"
            return t
        when "Len"
            t = get_type node.value
            node_assert t\is_a(ListType) or t\is_a(Range) or t\is_a(String) or t\is_a(TableType), node, "Attempt to get length of non-iterable: #{t}"
            return Int
        when "Not"
            t = get_type node.value
            node_assert t == Bool or t\is_a(OptionalType), node, "Invalid type for 'not': #{t}"
            return Bool
        when "Pow"
            base_type = get_type node.base
            node_assert base_type\is_a(Num) or base_type\is_a(Int), node.base, "Expected Num or Int, not #{base_type}"
            exponent_type = get_type node.exponent
            node_assert exponent_type\is_a(Num) or base_type\is_a(Int), node.exponent, "Expected Num or Int, not #{exponent_type}"
            return base_type
        when "Lambda","FnDecl"
            decl_ret_type = node.return and parse_type(node.return)
            if node.__pending == true
                return nil unless decl_ret_type
                return FnType([parse_type a.type for a in *node.args], decl_ret_type, [a.arg[0] for a in *node.args])
            node.__pending = true
            node_assert node.body.__tag == "Block", node.body, "Expected function body to be a block, not #{node.body.__tag or '<untagged>'}"
            ret_type = nil
            for ret in coroutine.wrap ->find_returns(node.body)
                if ret_type == nil
                    ret_type = ret.value and get_type(ret.value) or Nil
                else
                    t2 = ret.value and get_type(ret.value) or Nil
                    continue if t2\is_a(ret_type)
                    if t2 == Nil
                        ret_type = OptionalType(ret_type)
                    elseif ret_type == Nil
                        ret_type = OptionalType(t2)
                    else
                        node_error ret, "Return type #{t2} doesn't match earlier return type #{ret_type}"
            -- Check for fallthrough case:
            has_fallthrough = (node)->
                last = node
                while last
                    switch last.__tag
                        when "Return" then return false
                        when "Block" then last = last[#last]
                        when "Do" then last = last.body[#last.body]
                        when "If","When"
                            for clause in *last
                                return true if has_fallthrough(clause.body)
                            return true if not last.elseBody or has_fallthrough(last.elseBody)
                            return false
                        when "While","For","Repeat"
                            return true
                        when nil then last = last[#last]
                        else return true
                    break if last.__tag == "Return"

            if ret_type
                node_assert ret_type == Nil or not has_fallthrough(node.body), node, "Function is not guaranteed to return a value"
            else
                ret_type = Nil
            -- ret_type = ret_type or Nil
            if decl_ret_type and decl_ret_type\is_a(OptionalType) and ret_type == Nil
                ret_type = decl_ret_type
            elseif decl_ret_type
                node_assert decl_ret_type == ret_type, node, "Conflicting return types: #{decl_ret_type} vs #{ret_type}"
            node.__pending = nil
            return FnType([parse_type a.type for a in *node.args], ret_type, [a.arg[0] for a in *node.args])
        when "Var"
            if find_type_alias node, node[0]
                return TypeString
            var_type = node.__type or find_declared_type(node, node[0])
            if not var_type and node[0] == "args"
                return ListType(String)
            if not var_type and node.__decl
                return get_type(node.__decl)
            node_assert var_type, node, "Cannot determine type for undefined variable"
            return var_type
        when "Global"
            return nil
        when "FnCall"
            return parse_type(node.type) if node.type
            fn_type = get_type node.fn
            node_assert fn_type or node.__parent.__tag == "Block", node, "This function's return type cannot be inferred. It must be specified manually using a type annotation"
            return Nil unless fn_type
            node_assert fn_type\is_a(FnType), node.fn, "This is not a function, it's a #{fn_type or "???"}"
            return fn_type.return_type
        when "Block"
            -- error "Blocks have no type"
            return Nil
            -- return get_type(node[#node])
        when "Struct"
            if node.name
                alias = find_type_alias node, node.name[0]
                -- node_assert alias, node, "Undefined struct"
                return alias if alias

            key = "{#{concat ["#{m.name and "#{m.name[0]}=" or ""}#{get_type m.value}" for m in *node], ","}}"
            unless tuples[key]
                name = node.name and node.name[0] or "Tuple.#{tuple_index}"
                tuple_type = StructType(name)
                i = 0
                for memb in *node
                    if memb.name
                        tuple_type\add_member memb.name[0], get_type(memb.value)
                    else
                        i += 1
                        tuple_type\add_member i, get_type(memb.value)

                tuple_index += 1
                tuples[key] = tuple_type
            return tuples[key]
        when "Union"
            union_type = find_type_alias node, node.name[0]
            member = node_assert union_type.members[node.member[0]], node.member, "Not a valid union field from #{union_type\verbose_type!}"
            value_type = get_type(node.value)
            node_assert value_type\is_a(member.type), node.value,
                "This value is a #{value_type}, but values for #{union_type.name}.#{node.member[0]} should be #{member.type}\n"
            return union_type
        when "Interp"
            return get_type(node.value)
        when "If"
            node_assert node.elseBody, node, "'if' statement can't be used as an expression without an 'else' block"
            t = get_type(node[1].body[#node[1].body])
            node_assert t != Void, node[1].body[#node[1].body]

            check_block = (block)->
                t2 = get_type(block[#block])
                if t == Void
                    t = t2
                elseif t2 == Void
                    return
                elseif t2\is_a(t)
                    return
                elseif t\is_a(t2)
                    t = t2
                else
                    node_error block[#block],
                        "This expression has type #{t2}, but the earlier values for this `if` block are all #{t}"

            for i=2,#node
                check_block node[i].body

            check_block node.elseBody
            return t
        else
            error("Cannot infer type for #{viz node}")
            -- node_error node, "Cannot infer type for: #{node.__tag}"

    if #node > 0
        error "Getting a node without a tag: #{viz node}"
        return get_type(node[#node])

    error("Cannot infer type for #{viz node}")
    -- assert(node.__tag, "Cannot infer type for #{viz node}")
    -- node_error node, "Cannot infer type for: #{node.__tag}"

return {
    :parse_type, :get_type, :Type, :NamedType, :ListType, :TableType, :FnType, :StructType,
    :Value, :Value32, :Value16, :Value8, :Pointer, :Int, :Int32, :Int16, :Int8, :Num, :Num32, :Percent, :String, :Bool, :Void, :Nil, :Range,
    :OptionalType, :MeasureType, :TypeString, :EnumType, :UnionType,
}
