-- Type checking/inference logic
concat = table.concat
import log, viz, print_err, node_assert, node_error from require 'util'

local get_type, parse_type

class Type
    is_a: (cls)=> @ == cls or @.__class == cls or cls\contains @
    contains: (other)=> @ == other
    base_type: 'l'
    abi_type: 'l'
    __eq: (other)=> type(other) == type(@) and other.__class == @__class and tostring(other) == tostring(@)

class NamedType extends Type
    new: (@name)=>
    __tostring: => @name
    __eq: Type.__eq

class DerivedType extends Type
    new: (@name, @derived_from)=>
    __tostring: => @name
    __eq: Type.__eq
    is_a: (cls)=> @ == cls or @derived_from\is_a(cls) or @.__class == cls or cls\contains @

class ListType extends Type
    new: (@item_type)=>
    __tostring: => "[#{@item_type}]"
    __eq: Type.__eq

class FnType extends Type
    new: (@arg_types, @return_type)=>
    __tostring: => "#{@arg_signature!}=>#{@return_type}"
    __eq: Type.__eq
    arg_signature: => "(#{concat ["#{a}" for a in *@arg_types], ","})"

class StructType extends Type
    new: (@name, @members)=> -- Members: {{type=t, name="Foo"}, {type=t2, name="Baz"}, ...}
        @members_by_name = {}
        for i,m in ipairs @members
            @members_by_name[m.name] = {index: i, type: m.type} if m.name
        @abi_type = ":#{@name}"
    __tostring: => "#{@name}{#{concat ["#{m.name and m.name..':' or ''}#{m.type}" for m in *@members], ","}}"
    __eq: Type.__eq

Nil = NamedType("Nil")

class OptionalType extends Type
    new: (@nonnil)=>
        assert @nonnil and @nonnil != Nil
        if @nonnil.__class == OptionalType
            @nonnil = assert(@nonnil.nonnil)
    contains: (other)=> other == @ or other == Nil or (@nonnil and other\is_a(@nonnil))
    __tostring: => @nonnil\is_a(FnType) and "(#{@nonnil})?" or "#{@nonnil}?"
    __eq: Type.__eq

-- Primitive Types:
Num = NamedType("Num")
Num.base_type = 'd'
Num.abi_type = 'd'
Int = DerivedType("Int", Num)
Int.base_type = 'l'
Int.abi_type = 'l'

Void = NamedType("Void")
Bool = NamedType("Bool")
String = NamedType("String")
Range = StructType("Range", {{name:"first",type:Int},{name:"next",type:Int},{name:"last",type:Int}})
primitive_types = {:Int, :Num, :Void, :Nil, :Bool, :String, :Range, :OptionalType}

tuples = {}
tuple_index = 1

memoize = (fn)->
    cache = setmetatable {}, __mode:'k'
    return (x)->
        unless cache[x]
            cache[x] = fn(x)
        return cache[x]

add_parenting = (ast)->
    for k,node in pairs ast
        if type(node) == 'table' and not (type(k) == 'string' and k\match("^__"))
            node.__parent = ast
            add_parenting node

find_returns = (node)->
    switch node.__tag
        when "Return"
            coroutine.yield(node)
        when "Lambda","FnDecl","Declaration"
            return
        else
            for k,child in pairs node
                find_returns(child) if type(child) == 'table' and not (type(k) == 'string' and k\match("^__"))

find_declared_type = (scope, name, arg_signature=nil)->
    return nil unless scope
    switch scope.__tag
        when "Block"
            for i=#scope,1,-1
                stmt = scope[i]
                if stmt.__tag == "FnDecl" and stmt.name[0] == name and (not arg_signature or arg_signature == get_type(stmt)\arg_signature!)
                    return get_type(stmt)
                elseif stmt.__tag == "Declaration" and stmt.var[0] == name
                    return parse_type(stmt.type[1]) if stmt.type
                    return get_type stmt.value[1]
        when "FnDecl","Lambda"
            for a in *scope.args
                if a.arg[0] == name
                    return parse_type(a.type[1])
        when "For"
            if scope.index and scope.index[0] == name
                return Int
            if scope.var and scope.var[0] == name
                iter_type = get_type(scope.iterable[1])
                log "ITER TYPE: #{name} #{iter_type}"
                return Int if iter_type\is_a(Range)
                node_assert iter_type\is_a(ListType) or iter_type\is_a(Range), scope.iterable[1], "Not an iterable"
                log "Var TYPE: #{name} #{iter_type.item_type}"
                return iter_type.item_type
    
    if scope.__parent and (scope.__parent.__tag == "For" or scope.__parent.__tag == "While" or scope.__parent.__tag == "Repeat")
        loop = scope.__parent
        if scope == loop.between
            t = find_declared_type(loop.body[1], name, arg_signature)
            return t if t
            
    return find_declared_type(scope.__parent, name, arg_signature)

find_type_alias = (scope, name)->
    while scope
        switch scope.__tag
            when "Block"
                for i=#scope,1,-1
                    stmt = scope[i]
                    if stmt.__tag == "TypeDeclaration" and stmt[1][0] == name
                        return parse_type stmt[2]
        scope = scope.__parent

derived_types = {}

parse_type = memoize (type_node)->
    switch type_node.__tag
        when "NamedType"
            if primitive_types[type_node[0]]
                return primitive_types[type_node[0]]
            alias = find_type_alias type_node, type_node[0]
            node_assert alias, type_node, "Undefined type"
            return alias
        when "DerivedType"
            unless derived_types[type_node.name[0]]
                derived_types[type_node.name[0]] = DerivedType type_node.name[0], parse_type(type_node.derivesFrom[1])
            return derived_types[type_node.name[0]]
        when "ListType"
            return ListType(parse_type(type_node[1]))
        when "FnType"
            arg_types = [parse_type(a) for a in *type_node.args]
            return FnType(arg_types, parse_type(type_node.return[1]))
        when "StructType"
            return StructType(type_node.name[0], [{name:m.name[0], type: parse_type(m.type[1])} for m in *type_node])
        when "OptionalType"
            t = parse_type(type_node[1])
            node_assert not t\is_a(Num), type_node, "Optional numbers are not currently supported"
            return OptionalType(t)
        else
            error "Not a type node: #{viz type_node}"

get_op_type = (t1, op, t2)=>
    all_member_types = (t, pred)->
        for mem in *t.members
            return false unless pred(mem.type)
        return true

    switch op
        when "Add"
            if t1 == t2 and (t1\is_a(Int) or t1\is_a(Num) or t1\is_a(ListType))
                return t1
        when "Sub"
            if t1 == t2 and (t1\is_a(Int) or t1\is_a(Num))
                return t1
        when "Mul","Div","Mod"
            if t1 == t2 and (t1\is_a(Int) or t1\is_a(Num))
                return t1

    overload_names = Add:"add", Sub:"subtract", Mul:"multiply", Div:"divide", Mod:"modulus", Pow:"raise", Append:"append"
    return unless overload_names[op]
    overload = find_declared_type @, overload_names[op], "(#{t1},#{t2})"
    return overload.return_type if overload

get_type = memoize (node)->
    switch node.__tag
        when "Int" then return Int
        when "Float" then return Num
        when "Bool" then return Bool
        when "Nil" then return Nil
        when "String" then return String
        when "Range" then return Range
        when "Stop","Skip","Return","Fail"
            return Void
        when "Cast" then return parse_type(node.type[1])
        when "List"
            decl_type = node.type and parse_type(node.type[1])
            return decl_type if #node == 0
            t = get_type node[1]
            node_assert t == decl_type, node[1], "Not expected type: #{t}" if decl_type
            for i=2,#node
                node_assert get_type(node[i]) == t, node[i], "Not expected type: #{t}"
            return ListType(t)
        when "IndexedTerm"
            t = get_type node[1]
            if t\is_a(ListType)
                index_type = get_type(node[2], vars)
                if index_type == Int
                    return t.item_type
                elseif index_type == Range
                    return t
                else
                    node_error node[2], "Index has type #{index_type}, but expected Int or Range"
            elseif t\is_a(StructType)
                if node[2].__tag == "FieldName"
                    member_name = node[2][0]
                    node_assert t.members_by_name[member_name], node[2], "Not a valid struct member of #{t}"
                    return t.members_by_name[member_name].type
                elseif node[2].__tag == "Int"
                    i = tonumber(node[2][0])
                    node_assert 1 <= i and i <= #t.members, node[2], "#{t} only has members between 1 and #{#t.members}"
                    return t.members[i].type
                else
                    node_error node[2], "Structs can only be indexed by a field name or Int literal"
            elseif t == String
                index_type = get_type(node[2], vars)
                if index_type == Int
                    return Int
                elseif index_type == Range
                    return String
                else
                    node_error node[2], "Strings can only be indexed by Ints or Ranges"
            else
                print_err node, "Indexing is only valid on structs and lists"
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
                    node_assert not t\is_a(Num), val, "Optional numbers are not yet supported"
                    optional = OptionalType(t)
            return optional
        when "Equal","NotEqual","Less","LessEq","Greater","GreaterEq"
            return Bool
        when "TernaryOp"
            cond_type = get_type node.condition[1]
            node_assert cond_type == Bool, node.condition, "Expected a Bool here"
            true_type = get_type node.ifTrue[1]
            false_type = get_type node.ifFalse[1]
            if true_type == false_type
                return true_type
            elseif true_type == Nil
                node_assert not false_type\is_a(Num), node.ifFalse[1], "Optional numbers are not currently supported"
                return OptionalType(false_type)
            elseif false_type == Nil
                node_assert not true_type\is_a(Num), node.ifTrue[1], "Optional numbers are not currently supported"
                return OptionalType(true_type)
            else
                node_error node, "Values for true/false branches are different: #{true_type} vs #{false_type}"
        when "Add","Sub","Mul","Div","Mod"
            lhs_type = get_type node[1]
            rhs_type = get_type node[2]
            ret_type = get_op_type(node, lhs_type, node.__tag, rhs_type)
            node_assert ret_type, node, "Invalid #{node.__tag} types: #{lhs_type} and #{rhs_type}"
            return ret_type
        when "Append"
            lhs_type = get_type node[1]
            node_assert lhs_type, node[1], "This element does not have a definite type"
            if lhs_type == String
                return String
            rhs_type = get_type node[2]
            if lhs_type\is_a(ListType) and rhs_type\is_a(lhs_type.item_type)
                return lhs_type
            ret_type = get_op_type(node, lhs_type, node.__tag, rhs_type)
            node_assert ret_type, node, "Invalid #{node.__tag} types: #{lhs_type} and #{rhs_type}"
            return ret_type
        when "ButWith"
            base_type = get_type node.base[1]
            if base_type\is_a(ListType)
                for i in *node
                    node_assert i.index, i, "Field names are not allowed for Lists"
                    i_type = get_type(i.index[1])
                    value_type = get_type(i.value[1])
                    if i_type\is_a(Int)
                        node_assert value_type == base_type.item_type, i.value[1], "Value is #{value_type} not #{base_type.item_type}"
                    elseif i_type\is_a(Range)
                        node_assert value_type == base_type, i.value[1], "Value is #{value_type} not #{base_type}"
                    else
                        node_error i.index[1], "Value is #{value_type} not Int or Range"
                return base_type
            elseif base_type\is_a(String)
                for i in *node
                    node_assert i.index, i, "Field names are not allowed for Strings"
                    if get_type(i.index[1])\is_a(Range)
                        value_type = get_type(i.value[1])
                        node_assert value_type == base_type, i.value[1], "Value is #{value_type} not #{base_type}"
                    else
                        node_error i.index[1], "Value is #{value_type} not Range"
                return base_type
            elseif base_type\is_a(StructType)
                for i in *node
                    if i.field
                        node_assert base_type.members_by_name[i.field[0]], i.field, "Not a valid struct member of #{base_type}"
                    elseif i.index
                        node_assert i.index[1].__tag == "Int", i.index[1], "Only field names and integer literals are supported for using |[..]=.. on Structs"
                        n = tonumber(i.index[0])
                        node_assert 1 <= n and n <= #base_type.members, i.index[i], "#{base_type} only has members between 1 and #{#base_type.members}"
                return base_type
            else
                node_error node, "| operator is only supported for List and Struct types"

            return base_type
        when "Negative"
            t = get_type node[1]
            node_assert t\is_a(Int) or t\is_a(Num) or t\is_a(Range), node, "Invalid negation type: #{t}"
            return t
        when "Len"
            t = get_type node[1]
            node_assert t\is_a(ListType) or t\is_a(Range) or t\is_a(String), node, "Attempt to get length of non-iterable: #{t}"
            return Int
        when "Not"
            t = get_type node[1]
            node_assert t == Bool, node, "Invalid type for 'not': #{t}"
            return Bool
        when "Pow"
            base_type = get_type node.base[1]
            node_assert base_type\is_a(Num) or base_type\is_a(Int), node.base[1], "Expected Num or Int, not #{base_type}"
            exponent_type = get_type node.exponent[1]
            node_assert exponent_type\is_a(Num) or base_type\is_a(Int), node.exponent[1], "Expected Num or Int, not #{exponent_type}"
            return base_type
        when "Lambda","FnDecl"
            decl_ret_type = node.return and parse_type(node.return[1])
            node_assert node.body[1].__tag == "Block", node.body, "Uh oh"
            ret_type = nil
            for ret in coroutine.wrap ->find_returns(node.body)
                if ret_type == nil
                    ret_type = ret[1] and get_type(ret[1]) or Void
                else
                    t2 = ret[1] and get_type(ret[1]) or Void
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
                node_assert ret_type == Void or not has_fallthrough(node.body), node, "Function is not guaranteed to return a value"
            else
                ret_type = Void
            -- ret_type = ret_type or Void
            if decl_ret_type
                node_assert decl_ret_type == ret_type, node, "Conflicting return types"
            return FnType([parse_type a.type[1] for a in *node.args], ret_type)
        when "Var"
            if node.__decl
                return get_type(node.__decl)
            var_type = find_declared_type(node.__parent, node[0])
            if not var_type
                return Int if node[0] == "argc"
                return ListType(String) if node[0] == "argv"
            node_assert var_type, node, "Cannot determine type for undefined variable"
            return var_type
        when "Global"
            return nil
        when "MethodCall"
            return parse_type(node.type[1]) if node.type
            self_type = get_type node[1]
            target_sig = "(#{concat [tostring(get_type(a)) for a in *node], ","})"
            fn_type = find_declared_type node, node.fn[0], target_sig
            node_assert fn_type and fn_type\is_a(FnType), node.fn[1], "This is not a method, it's a #{fn_type}"
            return fn_type.return_type
        when "FnCall"
            return parse_type(node.type[1]) if node.type
            fn_type = if node.fn[1].__tag == "Var"
                target_sig = "(#{concat [tostring(get_type(a)) for a in *node], ","})"
                find_declared_type node, node.fn[0], target_sig
            else
                get_type node.fn[1]
            node_assert fn_type, node.fn[1], "This function's return type cannot be inferred. It must be specified manually using a type annotation"
            node_assert fn_type\is_a(FnType), node.fn[1], "This is not a function, it's a #{fn_type or "???"}"
            return fn_type.return_type
        when "Block"
            error "Blocks have no type"
            -- return get_type(node[#node])
        when "Struct"
            if node.name
                alias = find_type_alias node, node.name[0]
                -- node_assert alias, node, "Undefined struct"
                return alias if alias

            key = "{#{concat ["#{m.name and "#{m.name[0]}=" or ""}#{get_type m.value[1]}" for m in *node], ","}}"
            unless tuples[key]
                members = [{type: get_type(m.value[1]), name: m.name and m.name[0]} for m in *node]
                name = node.name and node.name[0] or "Tuple.#{tuple_index}"
                tuple_index += 1
                tuples[key] = StructType(name, members)
            return tuples[key]
        else
            node_assert not node.__tag, node, "Cannot infer type for: #{node.__tag}"
    if #node > 0
        error "Getting a node without a tag: #{viz node}"
        return get_type(node[#node])
    return Void

return {:add_parenting, :parse_type, :get_type, :Type, :NamedType, :ListType, :FnType, :StructType, :Int, :Num, :String, :Bool, :Void, :Nil, :Range, :OptionalType}
