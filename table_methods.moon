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

    value_bits, key_bits, value = env\fresh_locals "value.bits", "key.bits", "value"
    if t.key_type.base_type == "s" or t.key_type.base_type == "d"
        code ..= "#{key_bits} =l cast #{key_reg}\n"
    else
        code ..= "#{key_bits} =l copy #{key_reg}\n"
    code ..= "#{value_bits} =l call $bl_table_get(l #{table_reg}, l #{key_bits}, l #{t.key_type.nil_value}, l #{t.value_type.nil_value})\n"

    if t.value_type.base_type == "s" or t.value_type.base_type == "d"
        code ..= "#{value} =#{t.value_type.base_type} cast #{value_bits}\n"
    else
        code ..= "#{value} =#{t.value_type.base_type} copy #{value_bits}\n"

    if fail_on_missing
        is_nil = env\fresh_locals "is_nil"
        if t.value_type.base_type == "d"
            code ..= "#{is_nil} =w cuod #{value}, d_0.0 # Test for NaN\n"
        elseif t.value_type.base_type == "s"
            code ..= "#{is_nil} =w cuos #{value}, s_0.0 # Test for NaN\n"
        else
            code ..= "#{is_nil} =w ceq#{t.value_type.base_type} #{value}, #{t.value_type.nil_value}\n"
        nil_label,done_label = env\fresh_labels "is_nil", "nonnil"
        code ..= "jnz #{is_nil}, #{nil_label}, #{done_label}\n"
        code ..= "#{nil_label}\n"
        key_str = env\fresh_locals "key_str"
        code ..= "#{key_str} =l call #{env\get_tostring_fn(t.key_type)}(#{t.key_type.base_type} #{key_reg}, l 0)\n"
        code ..= "call $dprintf(l 2, l #{env\get_string_reg(context_err(key, "Key is not present in this table: %s", 2).."\n", "index_error")}, l #{key_str})\n"
        code ..= "call $_exit(l 1)\n"
        code ..= "jmp #{nil_label}\n"
        code ..= "#{done_label}\n"

    return value,code

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

        value_bits, key_bits = env\fresh_locals "value.bits", "key.bits"
        if key_t.base_type == "s" or key_t.base_type == "d"
            code ..= "#{key_bits} =l cast #{key_reg}\n"
        else
            code ..= "#{key_bits} =l copy #{key_reg}\n"

        if value_t.base_type == "s" or value_t.base_type == "d"
            code ..= "#{value_bits} =l cast #{value_reg}\n"
        else
            code ..= "#{value_bits} =l copy #{value_reg}\n"
        code ..= "#{value_bits} =l call $bl_table_set(l #{table_reg}, l #{key_bits}, l #{value_bits}, l #{key_t.nil_value}, l #{value_t.nil_value})\n"
        return nil,code

    copy: (env)=>
        copy = env\fresh_locals "copy"
        table_reg, code = env\to_regs @[1]
        code ..= "#{copy} =l call $hashmap_copy(l #{table_reg})\n"
        return copy, code
}

return {:methods, :types, :to_table_format, :from_table_format}
