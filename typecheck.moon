-- Type checking/inference logic
concat = table.concat
import log, viz from require 'util'

local get_type

parents = setmetatable {}, __mode:"k"

add_parenting = (ast)->
    for _,node in pairs ast
        if type(node) == 'table'
            parents[node] = ast
            add_parenting node

find_returns = (node)->
    switch node.__tag
        when "Return"
            coroutine.yield(node[1] or false)
        when "Func","FnDecl","Declaration"
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
                    return stmt.type[0] if stmt.type
                    return get_type stmt.value[1]
        when "FnDecl","Func"
            for a in *scope.args
                if a.arg[0] == name
                    return a.type[0]
        when "For-loop"
            if scope.var[0] == name
                return "Int" if scope.iterable.__tag == "Range"
                iter_type = get_type(scope.iterable)
                assert iter_type\match("^%b[]$"), "Not an iterable: #{iter_type}"
                return iter_type\sub(2,#iter_type-1)
    
    return find_declared_type(parents[scope], name)

memoize = (fn)-> fn
    -- cache = setmetatable {}, __mode:'k'
    -- return (x)->
    --     unless cache[x]
    --         cache[x] = fn(x)
    --     return cache[x]

get_type = memoize (node)->
    switch node.__tag
        when "Int","Float","Bool","String" then return node.__tag
        when "List"
            decl_type = node.type and node.type[0]
            return decl_type if #node == 0
            t = get_type node[1]
            assert t == decl_type, "List type mismatch" if decl_type
            for i=2,#node
                assert get_type(node[i]) == t, "List type mismatch"
            return "[#{t}]"
        when "IndexedTerm"
            assert node[1] and node[2], "No value/index"
            list_type = get_type node[1]
            assert list_type\match("^%b[]$"), "Not a list: #{viz node[1]} is: #{list_type}"
            assert get_type(node[2], vars) == "Int", "Bad index"
            return list_type\sub(2,#list_type-1)
        when "And","Or","Comparison" then return "Bool"
        when "Add","Sub","Mul","Div"
            lhs_type = get_type node[1]
            rhs_type = get_type node[2]
            assert lhs_type == rhs_type and (lhs_type == "Int" or lhs_type == "Float"), "Invalid #{node.__tag} types: #{lhs_type} and #{rhs_type}"
            return lhs_type
        when "Pow"
            assert get_type(node.base) == "Float", "Expected float"
            assert get_type(node.exponent) == "Float", "Expected float"
            return "Float"
        when "Func","FnDecl"
            return node.type[0] if node.type

            ret_type = if node.expr
                get_type node.expr[1]
            else
                t = nil
                for ret in coroutine.wrap ->find_returns(node.body)
                    if t == nil
                        t = ret and get_type(ret) or "Void"
                    else
                        t2 = ret and get_type(ret) or "Void"
                        assert(t2 == t, "Return type mismatch: #{t} vs #{t2}")
                t or "Void"
            return "(#{concat [get_type a for a in *node.args], ","})->#{ret_type}"
        when "Var"
            var_type = find_declared_type(parents[node], node[0])
            assert var_type, "Undefined variable: #{node[0]}"
            return var_type
        when "FnCall"
            if node.type
                return node.type[0]
            else
                fn_type = get_type node.fn[1]
                args = fn_type\match("^%b()->")
                assert args, "Not a function: #{viz node.fn[1]} is #{fn_type}"
                return fn_type\sub(#args+1,#fn_type)
        when "Block"
            error "Blocks have no type"
            -- return get_type(node[#node])
        else
            assert not node.__tag, "Unknown node tag: #{node.__tag}"
    if #node > 0
        error "WTF: #{viz node}"
        return get_type(node[#node])
    return "Void"

return {:add_parenting, :get_type, :get_abity}
