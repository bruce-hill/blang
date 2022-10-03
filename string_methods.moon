-- Custom implementations of list methods
import FnType, OptionalType, NilType, Bool, String, Int, ListType from require 'types'
import log, viz, node_assert, node_error, each_tag, context_err from require 'util'

types = {
    lowercase: => FnType({@},@,{"str"})
    uppercase: => FnType({@},@,{"str"})
    capitalized: => FnType({@},@,{"str"})
    titlecased: => FnType({@},@,{"str"})
    repeated: => FnType({@,Int},@,{"str","times"})
    starts_with: => FnType({@,@},Bool,{"str","prefix"})
    ends_with: => FnType({@,@},Bool,{"str","suffix"})
    strip: => FnType({@,OptionalType(@),OptionalType(Bool),OptionalType(Bool)},@,{"str","chars","left","right"})
    split: => FnType({@,@,OptionalType(Int)}, ListType(@), {"str","on","max_splits"})
    lines: => FnType({@}, ListType(@), {"str"})
    replacing: => FnType({@,@,@,OptionalType(Int)}, @, {"str","pattern","replacement","limit"})
    matches: => FnType({@,@}, Bool, {"str","pattern"})
    -- find: => FnType({@,@,OptionalType(Int)}, OptionalType(Int), {"str","target","start"})
    -- - matches() -> Bool
}

call_c_func = (code, cfunc)=>
    str = @fn and @fn.value or @[1]
    str_reg = code\add_value str
    result = code\fresh_locals "result"
    code\add "#{result} =l call $#{cfunc}(l #{str_reg})\n"
    return result

methods = {
    lowercase: (code)=> call_c_func(@, code, "bl_string_lower")
    uppercase: (code)=> call_c_func(@, code, "bl_string_upper")
    capitalized: (code)=> call_c_func(@, code, "bl_string_capitalized")
    titlecased: (code)=> call_c_func(@, code, "bl_string_titlecased")

    repeated: (code)=>
        args, err = types.repeated(@__type)\parse_args({@fn.value, table.unpack(@)})
        node_assert args, @, err
        str_reg, times_reg = code\add_values args.str, args.times
        result = code\fresh_locals "result"
        code\add "#{result} =l call $bl_string_repeat(l #{str_reg}, l #{times_reg})\n"
        return result

    starts_with: (code)=>
        args, err = types.starts_with(@__type)\parse_args({@fn.value, table.unpack(@)})
        node_assert args, @, err
        str_reg, prefix_reg = code\add_values args.str, args.prefix
        result = code\fresh_locals "result"
        code\add "#{result} =w call $bl_string_starts_with(l #{str_reg}, l #{prefix_reg})\n"
        return result
        
    ends_with: (code)=>
        args, err = types.ends_with(@__type)\parse_args({@fn.value, table.unpack(@)})
        node_assert args, @, err
        str_reg, prefix_reg = code\add_values args.str, args.suffix
        result = code\fresh_locals "result"
        code\add "#{result} =w call $bl_string_ends_with(l #{str_reg}, l #{prefix_reg})\n"
        return result

    strip: (code)=>
        args, err = types.strip(@__type)\parse_args({@fn.value, table.unpack(@)})
        node_assert args, @, err
        str_reg = code\add_value args.str
        chars_reg = if args.chars
            code\add_value args.chars
        else
            "#{String.nil_value}"

        left_reg = if args.left
            code\add_value args.left
        else
            "#{Bool.nil_value}"

        right_reg = if args.right
            code\add_value args.right
        else
            "#{Bool.nil_value}"

        result = code\fresh_locals "result"
        code\add "#{result} =l call $bl_string_strip(l #{str_reg}, l #{chars_reg}, w #{left_reg}, w #{right_reg})\n"
        return result

    replacing: (code)=>
        args, err = types.replacing(@__type)\parse_args({@fn.value, table.unpack(@)})
        node_assert args, @, err

        str_reg, pat_reg, replacement_reg = code\add_values args.str, args.pattern, args.replacement
        limit_reg = if args.limit
            code\add_value args.limit
        else
            "#{Int.nil_value}"

        result = code\fresh_locals "result"
        code\add "#{result} =l call $bl_string_replace(l #{str_reg}, l #{pat_reg}, l #{replacement_reg}, l #{limit_reg})\n"
        return result

    matches: (code)=>
        args, err = types.matches(@__type)\parse_args({@fn.value, table.unpack(@)})
        node_assert args, @, err

        str_reg, pat_reg = code\add_values args.str, args.pattern
        result = code\fresh_locals "result"
        code\add "#{result} =w call $bl_string_matches(l #{str_reg}, l #{pat_reg})\n"
        return result
}

return {:methods, :types}
