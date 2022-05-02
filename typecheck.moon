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
                if stmt.__tag == "FnDecl" and stmt.name == name
                    return get_func_type(stmt)
                elseif stmt.__tag == "Declaration" and stmt.var
                    return stmt.type[0] if stmt.type
                    return get_type stmt.value
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

get_type = (node)->
    switch node.__tag
        when "Int","Float","Bool","String" then return node.__tag
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
            ret_type = nil
            for ret in coroutine.wrap ->find_returns(node.body)
                if ret_type == nil
                    ret_type = ret and get_type(ret) or "Void"
                else
                    t2 = ret and get_type(ret) or "Void"
                    assert(t2 == ret_type, "Return type mismatch: #{ret_type} vs #{t2}")
            if not ret_type
                ret_type = get_type(node.body)
            return ret_type
        when "Var"
            var_type = find_declared_type(parents[node], node[0])
            assert var_type, "Undefined variable: #{node[0]}"
            return var_type
        when "FnCall"
            fn_type = get_type node.fn
            args = fn_type\match("^%b()->")
            assert args, "Not a function: #{fn_type}"
            return fn_type\sub(#args+1,#fn_type)
        when "Block"
            return get_type(node[#node])
    if #node > 0
        return get_type(node[#node])
    return "Void"

get_func_type = (node)->
    ret_type = find_type node.body
    return "(#{concat [a.type[0] for a in *node.args], ","})->#{ret_type}"

return {:add_parenting, :get_type, :get_abity}
