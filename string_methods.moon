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
    strip: => FnType({@,@,OptionalType(Bool),OptionalType(Bool)},@,{"str","chars","left","right"})
    split: => FnType({@,@,OptionalType(Int)}, ListType(@), {"str","on","max_splits"})
    lines: => FnType({@}, ListType(@), {"str"})
    -- find: FnType({@,@,OptionalType(Int)}, OptionalType(Int), {"str","target","start"})
    -- replacing: FnType({@,@,@,OptionalType(Int),OptionalType(Int)}, @, {"str","target","replacement","start","limit"})
    -- - matches() -> Bool
}

call_c_func = (env, cfunc)=>
    str = @fn and @fn.value or @[1]
    str_reg, str = env\to_regs str
    result = env\fresh_locals "result"
    code ..= "#{result} =l call $#{cfunc}(l #{str_reg})\n"
    return result, str

methods = {
    lowercase: (env)=> call_c_func(@, env, "bl_string_lower")
    uppercase: (env)=> call_c_func(@, env, "bl_string_upper")
    capitalized: (env)=> call_c_func(@, env, "bl_string_capitalized")
    titlecased: (env)=> call_c_func(@, env, "bl_string_titlecased")

    repeated: (env)=>
        args, err = types.repeated(@__type)\parse_args({@fn.value, table.unpack(@)})
        node_assert args, @, err
        str_reg, times_reg, code = env\to_regs args.str, args.times
        result = env\fresh_locals "result"
        code ..= "#{result} =l call $bl_string_repeat(l #{str_reg}, l #{times_reg})\n"
        return result, code

    starts_with: (env)=>
        args, err = types.starts_with(@__type)\parse_args({@fn.value, table.unpack(@)})
        node_assert args, @, err
        str_reg, prefix_reg, code = env\to_regs args.str, args.prefix
        result = env\fresh_locals "result"
        code ..= "#{result} =w call $bl_string_starts_with(l #{str_reg}, l #{prefix_reg})\n"
        return result, code
        
    ends_with: (env)=>
        args, err = types.ends_with(@__type)\parse_args({@fn.value, table.unpack(@)})
        node_assert args, @, err
        str_reg, prefix_reg, code = env\to_regs args.str, args.suffix
        result = env\fresh_locals "result"
        code ..= "#{result} =w call $bl_string_ends_with(l #{str_reg}, l #{prefix_reg})\n"
        return result, code
}

return {:methods, :types}
