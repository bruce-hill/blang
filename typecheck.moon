-- Type checking/inference logic
concat = table.concat
import log, viz, print_err, assert_node from require 'util'

local get_type, parse_type

class Type
    is_a: (cls)=> @ == cls or cls\contains @
    contains: (other)=> @ == other
    base_type: 'l'
    abi_type: 'l'
    __eq: (other)=> type(other) == type(@) and other.__class == @__class and tostring(other) == tostring(@)

class NamedType extends Type
    new: (@name)=>
    __tostring: => @name
    __eq: Type.__eq

class ListType extends Type
    new: (@item_type)=>
    __tostring: => "[#{@item_type}]"
    __eq: Type.__eq

class FnType extends Type
    new: (@arg_types, @return_type)=>
    __tostring: => "#{@arg_signature!}->#{@return_type}"
    __eq: Type.__eq
    arg_signature: => "(#{concat ["#{a}" for a in *@arg_types], ","})"

class VariantType extends Type
    new: (variants)=>
        flattened = {}
        for v in *variants
            if v.__class == VariantType
                for v2 in *v.variants
                    table.insert flattened, v2
            else
                table.insert flattened, v
        @variants = flattened
        table.sort @variants, (a,b)=> tostring(a) < tostring(b)
    __tostring: => "#{concat ["#{t}" for t in *@variants], "|"}"
    __eq: Type.__eq
    contains: (other)=>
        return true if @ == other
        to_check = if other.__class == VariantType
            other.variants
        else
            {other}

        -- Test if `to_check` is a subset of @variants
        self_i, check_i = 1, 1
        while self_i <= #@variants and check_i <= #to_check
            if @variants[self_i] == to_check[check_i]
                self_i += 1
                check_i += 1
            else
                self_i += 1
        return check_i > #to_check

class StructType extends Type
    new: (@name, @members)=> -- Members: {{type=t, name="Foo"}, {type=t2, name="Baz"}, ...}
        @members_by_name = {}
        for i,m in ipairs @members
            @members_by_name[m.name] = {index: i, type: m.type} if m.name
        @abi_type = ":#{@name}"
    __tostring: => "#{@name}{#{concat ["#{m.name and m.name..':' or ''}#{m.type}" for m in *@members], ","}}"
    __eq: Type.__eq

-- Primitive Types:
Int = NamedType("Int")
Float = NamedType("Float")
Float.base_type = 'd'
Float.abi_type = 'd'
Void = NamedType("Void")
Nil = NamedType("Nil")
Bool = NamedType("Bool")
String = NamedType("String")
Range = StructType("Range", {{name:"first",type:Int},{name:"next",type:Int},{name:"last",type:Int}})
primitive_types = {:Int, :Float, :Void, :Nil, :Bool, :String, :Range}

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
                return Int if iter_type == Range
                assert_node iter_type.__class == ListType or iter_type.__class == Range, scope.iterable[1], "Not an iterable"
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

parse_type = memoize (type_node)->
    switch type_node.__tag
        when "NamedType"
            if primitive_types[type_node[0]]
                return primitive_types[type_node[0]]
            alias = find_type_alias type_node, type_node[0]
            assert_node alias, type_node, "Undefined type"
            return alias
        when "ListType"
            return ListType(parse_type(type_node[1]))
        when "FnType"
            arg_types = [parse_type(a) for a in *type_node.args]
            return FnType(arg_types, parse_type(type_node.return[1]))
        -- when "OptionalType"
        --     return VariantType({parse_type(type_node[1]), Nil})
        -- when "VariantType"
        --     return VariantType([parse_type(t) for t in *type_node])
        when "StructType"
            return StructType(type_node.name[0], [{name:m.name[0], type: parse_type(m.type[1])} for m in *type_node])
        else
            error "Not a type node: #{viz type_node}"

get_op_type = (t1, op, t2)=>
    all_member_types = (t, pred)->
        for mem in *t.members
            return false unless pred(mem.type)
        return true

    switch op
        when "Add"
            if t1 == t2 and (t1 == Int or t1 == Float or t1.__class == ListType)
                return t1
        when "Sub"
            if t1 == t2 and (t1 == Int or t1 == Float)
                return t1
        when "Mul","Div","Mod"
            if t1 == Int and t2 == Int
                return Int
            elseif t1 == Float and t2 == Float
                return Float

    overload_names = Add:"add", Sub:"subtract", Mul:"multiply", Div:"divide", Mod:"modulus", Pow:"raise", Append:"append"
    return unless overload_names[op]
    overload = find_declared_type @, overload_names[op], "(#{t1},#{t2})"
    return overload.return_type if overload

get_type = memoize (node)->
    switch node.__tag
        when "Int" then return Int
        when "Float" then return Float
        when "Bool" then return Bool
        when "Nil" then return Nil
        when "String" then return String
        when "Range" then return Range
        when "List"
            decl_type = node.type and parse_type(node.type[1])
            return decl_type if #node == 0
            t = get_type node[1]
            assert_node t == decl_type, node[1], "Not expected type: #{t}" if decl_type
            for i=2,#node
                assert_node get_type(node[i]) == t, node[i], "Not expected type: #{t}"
            return ListType(t)
        when "IndexedTerm"
            t = get_type node[1]
            if t.__class == ListType
                index_type = get_type(node[2], vars)
                if index_type == Int
                    return t.item_type
                elseif index_type == Range
                    return t
                else
                    assert_node false, node[2], "Index has type #{index_type}, but expected Int or Range"
            elseif t.__class == StructType
                if node[2].__tag == "FieldName"
                    member_name = node[2][0]
                    assert_node t.members_by_name[member_name], node[2], "Not a valid struct member of #{t}"
                    return t.members_by_name[member_name].type
                elseif node[2].__tag == "Int"
                    i = tonumber(node[2][0])
                    assert_node 1 <= i and i <= #t.members, node[2], "#{t} only has members between 1 and #{#t.members}"
                    return t.members[i].type
                else
                    assert_node false, node[2], "Structs can only be indexed by a field name or Int literal"
            elseif t == String
                index_type = get_type(node[2], vars)
                if index_type == Int
                    return Int
                elseif index_type == Range
                    return String
                else
                    assert_node false, node[2], "Strings can only be indexed by Ints or Ranges"
            else
                print_err node, "Indexing is only valid on structs and lists"
        when "And","Or"
            for val in *node
                t = get_type val
                assert_node t == Bool, val, "Expected a Bool, but got a #{t}"
            return Bool
        when "Equal","NotEqual","Less","LessEq","Greater","GreaterEq"
            return Bool
        when "TernaryOp"
            cond_type = get_type node.condition[1]
            assert_node cond_type == Bool, node.condition, "Expected a Bool here"
            true_type = get_type node.ifTrue[1]
            false_type = get_type node.ifFalse[1]
            assert_node true_type == false_type, node, "Values for true/false branches are different: #{lhs_type} vs #{rhs_type}"
            return true_type
        when "Add","Sub","Mul","Div","Mod"
            lhs_type = get_type node[1]
            rhs_type = get_type node[2]
            ret_type = get_op_type(node, lhs_type, node.__tag, rhs_type)
            assert_node ret_type, node, "Invalid #{node.__tag} types: #{lhs_type} and #{rhs_type}"
            return ret_type
        when "Append"
            lhs_type = get_type node[1]
            assert_node lhs_type, node[1], "This element does not have a definite type"
            if lhs_type == String
                return String
            rhs_type = get_type node[2]
            if lhs_type.__class == ListType and rhs_type == lhs_type.item_type
                return lhs_type
            ret_type = get_op_type(node, lhs_type, node.__tag, rhs_type)
            assert_node ret_type, node, "Invalid #{node.__tag} types: #{lhs_type} and #{rhs_type}"
            return ret_type
        when "Negative"
            t = get_type node[1]
            assert_node t == Int or t == Float or t == Range, node, "Invalid negation type: #{t}"
            return t
        when "Len"
            t = get_type node[1]
            assert_node t.__class == ListType or t == Range or t == String, node, "Attempt to get length of non-iterable: #{t}"
            return Int
        when "Not"
            t = get_type node[1]
            assert_node t == Bool, node, "Invalid type for 'not': #{t}"
            return Bool
        when "Pow"
            base_type = get_type node.base[1]
            assert_node base_type == Float or base_type == Int, node.base[1], "Expected Float or Int, not #{base_type}"
            exponent_type = get_type node.exponent[1]
            assert_node exponent_type == Float or base_type == Int, node.exponent[1], "Expected Float or Int, not #{exponent_type}"
            return base_type
        when "Lambda","FnDecl"
            decl_ret_type = node.return and parse_type(node.return[1])
            ret_type = if node.body[1].__tag != "Block"
                get_type node.body[1]
            else
                t = nil
                for ret in coroutine.wrap ->find_returns(node.body)
                    if t == nil
                        t = ret[1] and get_type(ret[1]) or Void
                    else
                        t2 = ret[1] and get_type(ret[1]) or Void
                        unless t2\is_a t
                            t = Types.VariantType({t, t2})
                t or Void
            if decl_ret_type
                assert_node decl_ret_type == ret_type, node, "Conflicting return types"
            return FnType([parse_type a.type[1] for a in *node.args], ret_type)
        when "Var"
            if node.__decl
                return get_type(node.__decl)
            var_type = find_declared_type(node.__parent, node[0])
            if not var_type
                return Int if node[0] == "argc"
                return ListType(String) if node[0] == "argv"
            assert_node var_type, node, "Cannot determine type for undefined variable"
            return var_type
        when "Global"
            return nil
        when "MethodCall"
            return parse_type(node.type[1]) if node.type
            self_type = get_type node[1]
            target_sig = "(#{concat [tostring(get_type(a)) for a in *node], ","})"
            fn_type = find_declared_type node, node.fn[0], target_sig
            assert_node fn_type and fn_type.__class == FnType, node.fn[1], "This is not a method, it's a #{fn_type}"
            return fn_type.return_type
        when "FnCall"
            return parse_type(node.type[1]) if node.type
            fn_type = if node.fn[1].__tag == "Var"
                target_sig = "(#{concat [tostring(get_type(a)) for a in *node], ","})"
                find_declared_type node, node.fn[0], target_sig
            else
                get_type node.fn[1]
            assert_node fn_type, node.fn[1], "This function's return type cannot be inferred. It must be specified manually using a type annotation"
            assert_node fn_type.__class == FnType, node.fn[1], "This is not a function, it's a #{fn_type or "???"}"
            return fn_type.return_type
        when "Block"
            error "Blocks have no type"
            -- return get_type(node[#node])
        when "Struct"
            if node.name
                alias = find_type_alias node, node.name[0]
                -- assert_node alias, node, "Undefined struct"
                return alias if alias

            key = "{#{concat ["#{m.name and "#{m.name[0]}=" or ""}#{get_type m.value[1]}" for m in *node], ","}}"
            unless tuples[key]
                members = [{type: get_type(m.value[1]), name: m.name and m.name[0]} for m in *node]
                name = node.name and node.name[0] or "Tuple.#{tuple_index}"
                tuple_index += 1
                tuples[key] = StructType(name, members)
            return tuples[key]
        when "Stop","Skip"
            return Void
        else
            assert_node not node.__tag, node, "Cannot infer type for: #{node.__tag}"
    if #node > 0
        error "Getting a node without a tag: #{viz node}"
        return get_type(node[#node])
    return Void

return {:add_parenting, :parse_type, :get_type, :Type, :NamedType, :ListType, :FnType, :VariantType, :StructType, :Int, :Float, :String, :Bool, :Void, :Nil, :Range}
