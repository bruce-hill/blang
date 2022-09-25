-- Custom implementations of table methods
import FnType, OptionalType, ListType, NilType, String, Bool, Int from require 'types'
import log, viz, node_assert, node_error, each_tag, context_err from require 'util'

types = {
    copy: => FnType({@}, @, {"table"})
    equal_entries: => FnType({@,@}, Bool, {"table","other"})
    set: => FnType({@,@key_type,@value_type}, NilType, {"table","key","value"})
    set_all: => FnType({@, @}, NilType, {"table","other"})
    get: => FnType({@,@key_type}, OptionalType(@key_type), {"table","key"})
    get_or_fail: => FnType({@,@key_type}, @key_type, {"table","key"})
    update: => FnType({@,@key_type,FnType({OptionalType(@value_type)},@value_type,nil)}, NilType, {"table","key","fn"})
    remove: => FnType({@,@key_type}, NilType, {"table","key"})
    pop: => FnType({@,@key_type}, OptionalType(@value_type), {"table","key"})
}


to_table_format = (env, t, reg, dest_reg)->
    if t.base_type == "s" or t.base_type == "d"
        code = "#{dest_reg} =l cast #{reg}\n"
        return code.."#{dest_reg} =l xor #{dest_reg}, #{t.nil_value}\n"
    else
        code = if t.bytes == 8
            "#{dest_reg} =l copy #{reg}\n"
        else
            "#{dest_reg} =l extu#{t.abi_type} #{reg}\n"

        if t.nil_value != 0
            -- Swap nil_value and 0:
            do_toggle,done = env\fresh_labels "do_toggle","done"
            is_zero,is_nil,needs_toggle = env\fresh_locals "is_zero","is_nil","needs_toggle"
            code ..= "#{is_zero} =w ceq#{t.base_type} #{reg}, 0\n"
            code ..= "#{is_nil} =w ceq#{t.base_type} #{reg}, 0\n"
            code ..= "#{needs_toggle} =w or #{is_zero}, #{is_nil}\n"
            code ..= "jnz #{needs_toggle}, #{do_toggle}, #{done}\n"
            code ..= "#{do_toggle}\n"
            code ..= "#{dest_reg} =l xor #{dest_reg}, #{t.nil_value}\n"
            code ..= "#{done}\n"
        return code

from_table_format = to_table_format

get = (env, fail_on_missing)=>
    table,key = if @__tag == "IndexedTerm"
        @value, @index
    else
        @[1], @[2]
    t = table.__type
    table_reg, key_reg, code = env\to_regs table, key
    code = "\n# Table Get\n"..code
    key_getter = env\fresh_local "key.getter"
    code ..= to_table_format env, t.key_type, key_reg, key_getter
    raw_value = env\fresh_local "value.raw"
    code ..= "#{raw_value} =l call $hashmap_get(l #{table_reg}, l #{key_getter})\n"
    if fail_on_missing
        missing,found = env\fresh_labels "missing","found"
        code ..= "jnz #{raw_value}, #{found}, #{missing}\n"
        code ..= "#{missing}\n"
        tostring_fn = env\get_tostring_fn t.key_type, @
        str = env\fresh_locals "str"
        code ..= "#{str} =l call #{tostring_fn}(#{t.base_type} #{key_reg}, l 0)\n"
        code ..= "call $dprintf(l 2, l #{env\get_string_reg(context_err(key, "Key is not present in this table: %s", 2).."\n", "index_error")}, l #{str})\n"
        code ..= "call $_exit(l 1)\n"
        code ..= "jmp #{missing}\n"
        code ..= "#{found}\n"

    value_reg = env\fresh_local "value"
    code ..= from_table_format env, t.value_type, raw_value, value_reg
    return value_reg,code

maybe_reg_to_reg = (env, val)->
    if type(val) == 'string'
        return val, ""
    else
        return env\to_reg(val)

methods = {
    get: (env)=> get(@, env, false)
    get_or_fail: (env)=> get(@, env, true)

    set: (env,skip_ret,table_t=nil)=>
        table, key, value = @[1], @[2], @[3]
        key_t,value_t = if table_t
            table_t.key_type, table_t.value_type
        else
            key.__type, value.__type
        table_reg,code = maybe_reg_to_reg(env, table)
        code = "\n# Table set\n"..code
        key_reg,key_code = maybe_reg_to_reg(env, key)
        code ..= key_code
        value_reg,value_code = maybe_reg_to_reg(env, value)
        code ..= value_code
        key_setter,value_setter = env\fresh_locals "key.setter", "value.setter"
        code ..= to_table_format env, key_t, key_reg, key_setter
        code ..= to_table_format env, value_t, value_reg, value_setter
        if skip_ret
            code ..= "call $hashmap_set(l #{table_reg}, l #{key_setter}, l #{value_setter})\n"
            return nil, code
        else
            prev_raw,prev = env\fresh_locals "prev_value.raw","prev_value"
            code ..= "#{prev_raw} =l call $hashmap_set(l #{table_reg}, l #{key_setter}, l #{value_setter})\n"
            code ..= from_table_format env, value_t, prev_raw, prev
            return prev, code

    copy: (env)=>
        copy = env\fresh_locals "copy"
        table_reg, code = env\to_regs @[1]
        code ..= "#{copy} =l call $hashmap_copy(l #{table_reg})\n"
        return copy, code
}

return {:methods, :types, :to_table_format, :from_table_format}
