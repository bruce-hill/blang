-- Type checking/inference logic
concat = table.concat
import log, viz, print_err, assert_node from require 'util'

local get_type, parse_type

parents = setmetatable {}, __mode:"k"

class Type
    is_a: (cls)=> @ == cls or cls\contains @
    contains: (other)=> @ == other
    abi_type: 'l'

class NamedType extends Type
    new: (@name)=>
    __tostring: => @name
    __eq: (other)=>
        type(other) == type(@) and other.__class == @__class and other.name == @name

class ListType extends Type
    new: (@item_type)=>
    __tostring: => "[#{@item_type}]"
    __eq: (other)=>
        type(other) == type(@) and other.__class == @__class and other.item_type == @item_type

class FnType extends Type
    new: (@arg_types, @return_type)=>
    __tostring: => "(#{concat ["#{a}" for a in *@arg_types], ","})->#{@return_type}"
    __eq: (other)=>
        return false unless type(other) == type(@) and other.__class == @__class and other.return_type == @return_type and #other.arg_types == #@arg_types
        for i=1,#@arg_types
            return false unless other.arg_types[i] == @arg_types[i]
        return true

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
    __tostring: => "(#{concat ["#{t}" for t in *@variants], "|"})"
    __eq: (other)=>
        return false unless type(other) == type(@) and other.__class == @__class and #other.variants == #@variants
        for i=1,#@variants
            return false unless other.variants[i] == @variants[i]
        return true
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

-- Primitive Types:
Int = NamedType("Int")
Float = NamedType("Float")
Float.abi_type = 'd'
Void = NamedType("Void")
Nil = NamedType("Nil")
Bool = NamedType("Bool")
String = NamedType("String")
primitive_types = {:Int, :Float, :Void, :Nil, :Bool, :String}

memoize = (fn)->
    cache = setmetatable {}, __mode:'k'
    return (x)->
        unless cache[x]
            cache[x] = fn(x)
        return cache[x]

add_parenting = (ast)->
    for _,node in pairs ast
        if type(node) == 'table'
            parents[node] = ast
            add_parenting node

find_returns = (node)->
    switch node.__tag
        when "Return"
            coroutine.yield(node)
        when "Lambda","FnDecl","Declaration"
            return
        else
            for _,child in pairs node
                find_returns(child) if type(child) == 'table'

find_declared_type = (scope, name)->
    return nil unless scope
    switch scope.__tag
        when "Block"
            for i=#scope,1,-1
                stmt = scope[i]
                if stmt.__tag == "FnDecl" and stmt.name[0] == name
                    return get_type(stmt)
                elseif stmt.__tag == "Declaration" and stmt.var[0] == name
                    return parse_type(stmt.type[1]) if stmt.type
                    return get_type stmt.value[1]
        when "FnDecl","Lambda"
            for a in *scope.args
                if a.arg[0] == name
                    return parse_type(a.type[1])
        when "For-loop"
            if scope.var[0] == name
                return Int if scope.iterable.__tag == "Range"
                iter_type = get_type(scope.iterable)
                assert_node iter_type.__tag == "ListType", scope.iterable, "Not an iterable"
                return parse_type(iter_type.ast[1])
    
    return find_declared_type(parents[scope], name)

find_type_alias = (scope, name)->
    while scope
        switch scope.__tag
            when "Block"
                for i=#scope,1,-1
                    stmt = scope[i]
                    if stmt.__tag == "TypeDeclaration" and stmt[1][0] == name
                        return parse_type stmt[2]
        scope = parents[scope]

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
        when "OptionalType"
            return VariantType({parse_type(type_node[1]), Nil})
        when "VariantType"
            return VariantType([parse_type(t) for t in *type_node])
        else
            error "Not a type node: #{viz type_node}"

get_type = memoize (node)->
    switch node.__tag
        when "Int" then return Int
        when "Float" then return Float
        when "Bool" then return Bool
        when "Nil" then return Nil
        when "String" then return String
        when "List"
            decl_type = node.type and parse_type(node.type[1])
            return decl_type if #node == 0
            t = get_type node[1]
            assert_node t == decl_type, node[1], "Not expected type: #{t}" if decl_type
            for i=2,#node
                assert_node get_type(node[i]) == t, node[i], "Not expected type: #{t}"
            return ListType(t)
        when "IndexedTerm"
            list_type = get_type node[1]
            assert_node list_type.__class == ListType, node[1], "Value has type: #{list_type}, but expected a List"
            index_type = get_type(node[2], vars)
            assert_node index_type == Int, node[2], "Index has type #{index_type}, but expected Int"
            return list_type.item_type
        when "And","Or"
            for val in *node
                t = get_type val
                assert_node t == Bool, val, "Expected a Bool, but got a #{t}"
            return Bool
        when "Equal","NotEqual","Less","LessEq","Greater","GreaterEq"
            return Bool
        when "Add","Sub","Mul","Div"
            lhs_type = get_type node[1]
            rhs_type = get_type node[2]
            assert_node lhs_type == rhs_type and (lhs_type == Int or lhs_type == Float), node,
                "Invalid #{node.__tag} types: #{lhs_type} and #{rhs_type}"
            return lhs_type
        when "Pow"
            base_type = get_type node.base[1]
            assert_node base_type == Float, node.base[1], "Expected float, not #{base_type}"
            exponent_type = get_type node.exponent[1]
            assert_node exponent_type == Float, node.exponent[1], "Expected float, not #{exponent_type}"
            return Float
        when "Lambda","FnDecl"
            decl_type = node.type and parse_type(node.type[1])

            ret_type = if node.body[1].__tag != "Block"
                get_type node.body[1]
            else
                t = nil
                for ret in coroutine.wrap ->find_returns(node.body)
                    if t == nil
                        t = ret[1] and get_type(ret[1]) or Void
                    else
                        t2 = ret[1] and get_type(ret[1]) or Void
                        assert_node t2 == t, ret[1], "Return type here is: #{t2}, which conflicts with earlier return type: #{t}"
                t or Void
            return FnType([get_type a for a in *node.args], ret_type)
        when "Var"
            var_type = find_declared_type(parents[node], node[0])
            if not var_type
                return Int if node[0] == "argc"
                return ListType(String) if node[0] == "argv"
            assert_node var_type, node, "Undefined variable"
            return var_type
        when "FnCall"
            return parse_type(node.type[1]) if node.type
            fn_type = get_type node.fn[1]
            assert_node fn_type.__class == FnType, node.fn[1], "This is not a function, it's a #{fn_type}"
            return fn_type.return_type
        when "Block"
            error "Blocks have no type"
            -- return get_type(node[#node])
        else
            assert_node not node.__tag, node, "Unknown node tag: #{node.__tag}"
    if #node > 0
        error "WTF: #{viz node}"
        return get_type(node[#node])
    return Void

return {:add_parenting, :parse_type, :get_type, :Type, :NamedType, :ListType, :FnType, :VariantType, :Int, :Float, :String, :Bool, :Void, :Nil}
