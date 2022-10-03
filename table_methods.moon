-- Custom implementations of table methods
import FnType, OptionalType, ListType, NilType, String, Bool, Int from require 'types'
import log, viz, node_assert, node_error, each_tag, context_err from require 'util'

types = {
    copy: => FnType({@}, @, {"table"})
    equal_entries: => FnType({@,@}, Bool, {"table","other"})
    set: => FnType({@,@key_type,@value_type}, NilType, {"table","key","value"})
    set_all: => FnType({@, @}, NilType, {"table","other"})
    get: => FnType({@,@key_type}, OptionalType(@value_type), {"table","key"})
    get_or_fail: => FnType({@,@key_type}, @key_type, {"table","key"})
    update: => FnType({@,@key_type,FnType({OptionalType(@value_type)},@value_type,nil)}, NilType, {"table","key","fn"})
    remove: => FnType({@,@key_type}, NilType, {"table","key"})
    pop: => FnType({@,@key_type}, OptionalType(@value_type), {"table","key"})
}


to_table_format = (code, t, reg, dest_reg)->
    if t.base_type == "s" or t.base_type == "d"
        code\add "#{dest_reg} =l cast #{reg}\n"
        code\add "#{dest_reg} =l xor #{dest_reg}, #{t.nil_value}\n"
    else
        if t.bytes == 8
            code\add "#{dest_reg} =l copy #{reg}\n"
        else
            code\add "#{dest_reg} =l extu#{t.abi_type} #{reg}\n"

    if t.nil_value != 0
        -- Swap nil_value and 0:
        do_toggle,done = code\fresh_labels "do_toggle","done"
        is_zero,is_nil,needs_toggle = code\fresh_locals "is_zero","is_nil","needs_toggle"
        code\add "#{is_zero} =w ceq#{t.base_type} #{reg}, 0\n"
        code\add "#{is_nil} =w ceq#{t.base_type} #{reg}, 0\n"
        code\add "#{needs_toggle} =w or #{is_zero}, #{is_nil}\n"
        code\add "jnz #{needs_toggle}, #{do_toggle}, #{done}\n"
        code\add "#{do_toggle}\n"
        code\add "#{dest_reg} =l xor #{dest_reg}, #{t.nil_value}\n"
        code\add "#{done}\n"

from_table_format = to_table_format

get = (code, fail_on_missing)=>
    table,key = if @__tag == "IndexedTerm"
        @value, @index
    else
        @fn.value, @[1]
    t = table.__type
    code\add "\n# Table Get\n"
    table_reg, key_reg = code\add_values table, key

    value_bits, key_bits, value = code\fresh_locals "value.bits", "key.bits", "value"
    if t.key_type.base_type == "s" or t.key_type.base_type == "d"
        code\add "#{key_bits} =l cast #{key_reg}\n"
    else
        code\add "#{key_bits} =l copy #{key_reg}\n"
    code\add "#{value_bits} =l call $bl_table_get(l #{table_reg}, l #{key_bits}, l #{t.key_type.nil_value}, l #{t.value_type.nil_value})\n"

    if t.value_type.base_type == "s" or t.value_type.base_type == "d"
        code\add "#{value} =#{t.value_type.base_type} cast #{value_bits}\n"
    else
        code\add "#{value} =#{t.value_type.base_type} copy #{value_bits}\n"

    if fail_on_missing
        is_nil = code\fresh_locals "is_nil"
        if t.value_type.base_type == "d"
            code\add "#{is_nil} =w cuod #{value}, d_0.0 # Test for NaN\n"
        elseif t.value_type.base_type == "s"
            code\add "#{is_nil} =w cuos #{value}, s_0.0 # Test for NaN\n"
        else
            code\add "#{is_nil} =w ceq#{t.value_type.base_type} #{value}, #{t.value_type.nil_value}\n"
        nil_label,done_label = code\fresh_labels "is_nil", "nonnil"
        code\add "jnz #{is_nil}, #{nil_label}, #{done_label}\n"
        code\add "#{nil_label}\n"
        key_str = code\fresh_locals "key_str"
        code\add "#{key_str} =l call #{code\get_tostring_fn(t.key_type)}(#{t.key_type.base_type} #{key_reg}, l 0)\n"
        code\add "call $dprintf(l 2, l #{code\get_string_reg(context_err(key, "Key is not present in this table: %s", 2).."\n", "index_error")}, l #{key_str})\n"
        code\add "call $_exit(l 1)\n"
        code\add "jmp #{nil_label}\n"
        code\add "#{done_label}\n"

    return value

maybe_reg_to_reg = (code, val)->
    if type(val) == 'string'
        return val
    else
        return code\add_value(val)

methods = {
    get: (code)=> get(@, code, false)
    get_or_fail: (code)=> get(@, code, true)

    set: (code,skip_ret,table_t=nil)=>
        code\add "\n# Table set\n"
        table, key, value = @[1], @[2], @[3]
        key_t,value_t = if table_t
            table_t.key_type, table_t.value_type
        else
            key.__type, value.__type

        table_reg = maybe_reg_to_reg(code, table)
        key_reg = maybe_reg_to_reg(code, key)
        value_reg = maybe_reg_to_reg(code, value)

        value_bits, key_bits = code\fresh_locals "value.bits", "key.bits"
        if key_t.base_type == "s" or key_t.base_type == "d"
            code\add "#{key_bits} =l cast #{key_reg}\n"
        else
            code\add "#{key_bits} =l copy #{key_reg}\n"

        if value_t.base_type == "s" or value_t.base_type == "d"
            code\add "#{value_bits} =l cast #{value_reg}\n"
        else
            code\add "#{value_bits} =l copy #{value_reg}\n"
        code\add "#{value_bits} =l call $bl_table_set(l #{table_reg}, l #{key_bits}, l #{value_bits}, l #{key_t.nil_value}, l #{value_t.nil_value})\n"
        return

    copy: (code)=>
        copy = code\fresh_locals "copy"
        table_reg = code\add_value @[1]
        code\add "#{copy} =l call $hashmap_copy(l #{table_reg})\n"
        return copy
}

return {:methods, :types, :to_table_format, :from_table_format}
