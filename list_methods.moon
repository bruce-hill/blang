-- Custom implementations of list methods
import FnType, OptionalType, ListType, NilType, String, Bool, Int from require 'types'
import log, viz, node_assert, node_error, each_tag, context_err from require 'util'

types = {
    copy: => FnType({@}, @, {"list"})
    equal_items: => FnType({@,@}, Bool, {"list","other"})
    append: => FnType({@,@item_type}, NilType, {"list","item"})
    prepend: => FnType({@,@item_type}, NilType, {"list","item"})
    append_all: => FnType({@,@}, NilType, {"list","items"})
    prepend_all: => FnType({@,@}, NilType, {"list","items"})
    insert: => FnType({@,@item_type,OptionalType(Int)}, NilType, {"list","item","at"})
    insert_all: => FnType({@,@,OptionalType(Int)}, NilType, {"list","items","at"})
    pop: => FnType({@,OptionalType(Int)}, @item_type, {"list","from"})
    delete: => FnType({@,OptionalType(Int)}, NilType, {"list","at"})
    delete_range: => FnType({@,Range}, NilType, {"list","range"})
    find: => FnType({@,@item_type,OptionalType(Int)}, OptionalType(Int), {"list","item","after"})
    count: => FnType({@,@item_type,OptionalType(Int)}, Int, {"list","item","after"})
    reverse: => FnType({@}, NilType, {"list"})
    reversed: => FnType({@}, @, {"list"})
    wrapped: => FnType({@,Int}, Int, {"list","index"})
    at: => FnType({@,Int}, OptionalType(@item_type), {"list","index"})
    join: => FnType({@,OptionalType(String)}, String, {"list","glue"})
    sort: => FnType({@,OptionalType(FnType(@item_type,@item_type,Bool)),Bool}, NilType, {"list","by","reversed"})
    sorted: => FnType({@,OptionalType(FnType(@item_type,@item_type,Bool)),Bool}, @, {"list","by","reversed"})
}

insert = (env, list, item, index)->
    import get_type from require('typecheck')
    list_t = get_type(list)
    item_t = node_assert get_type(item), item, "No type"
    list_reg, item_reg, code = env\to_regs(list, item)

    node_assert item_t\is_a(list_t.item_type), item, "Cannot put a #{item_t} in a list of type #{list_t}"
    new_len,len,new_items,items,new_size,size = env\fresh_locals "new.len","len","new.items","items","new.size","size"
    code ..= "\n# Insert\n"
    code ..= "#{len} =l loadl #{list_reg}\n"
    code ..= "#{new_len} =l add #{len}, 1\n"
    code ..= "#{items} =l add #{list_reg}, 8\n"
    code ..= "#{items} =l loadl #{items}\n"
    code ..= "#{new_size} =l mul #{new_len}, #{item_t.bytes}\n"
    code ..= "#{new_items} =l call $gc_realloc(l #{items}, l #{new_size})\n"
    
    dest = env\fresh_local "dest"
    if index == nil
        code ..= "#{dest} =l add #{new_items}, #{new_size}\n"
        code ..= "#{dest} =l sub #{dest}, #{item_t.bytes}\n"
        code ..= "store#{item_t.abi_type} #{item_reg}, #{dest}\n"
    elseif index[0] == "1"
        code ..= "#{size} =l mul #{len}, #{item_t.bytes}\n"
        code ..= "call $memmove(l #{dest}, l #{new_items}, l #{size})\n"
        code ..= "store#{item_t.abi_type} #{item_reg}, #{new_items}\n"
    else
        node_assert get_type(index) == Int, index, "Index is not an Int, it's #{get_type(index)}"
        src,index_too_low,index_too_high,bad_index = env\fresh_locals "src","index_too_low","index_too_high","bad_index"
        index_error,index_ok = env\fresh_labels "index_error","index_ok"
        index_reg,index_code = env\to_reg index
        code ..= index_code

        code ..= "#{index_too_low} =w csltl #{index_reg}, 1\n"
        code ..= "#{index_too_high} =w csgtl #{index_reg}, #{new_len}\n"
        code ..= "#{bad_index} =w or #{index_too_low}, #{index_too_high}\n"
        code ..= "jnz #{bad_index}, #{index_error}, #{index_ok}\n"

        code ..= "#{index_error}\n"
        code ..= "call $dprintf(l 2, l #{env\get_string_reg(context_err(index, "Invalid list index: %ld", 2).."\n", "index_error")}, l #{index_reg})\n"
        code ..= "call $_exit(l 1)\n"
        code ..= "jmp #{index_error}\n"
        
        code ..= "#{index_ok}\n"
        code ..= "#{dest} =l mul #{index_reg}, #{item_t.bytes}\n"
        code ..= "#{dest} =l add #{dest}, #{new_items}\n"
        code ..= "#{src} =l sub #{dest}, #{item_t.bytes}\n"
        code ..= "#{size} =l sub #{len}, #{index_reg}\n"
        code ..= "#{size} =l add #{size}, 1\n"
        code ..= "#{size} =l mul #{size}, #{item_t.bytes}\n"
        code ..= "call $memmove(l #{dest}, l #{src}, l #{size})\n"
        code ..= "store#{item_t.abi_type} #{item_reg}, #{src}\n"

    code ..= "storel #{new_len}, #{list_reg}\n"
    code ..= "#{dest} =l add #{list_reg}, 8\n"
    code ..= "storel #{new_items}, #{dest}\n"
    return "0",code

methods = {
    append: (env, skip_ret)=>
        list = node_assert @fn.value, @, "No list provided"
        item = node_assert @[1], @, "No item provided to append"
        return insert(env, list, item)

    prepend: (env, skip_ret)=>
        import get_type from require('typecheck')
        list = node_assert @fn.value, @, "No list provided"
        item = node_assert @[1], @, "No item provided to append"
        return insert(env, list, item, 0)

    insert: (env, skip_ret)=>
        list = node_assert @fn.value, @, "No list provided"
        local index, item
        positional = {}
        for arg in *@
            if arg.__tag == "KeywordArg" and arg.name[0] == "at"
                index = arg.value
            elseif arg.__tag == "KeywordArg" and arg.name[0] == "item"
                item = arg.value
            else
                table.insert positional, arg
        if not item
            item = table.remove(positional,1)
        if not index
            index = table.remove(positional,1)
        node_assert item, @, "No item provided to insert"
        return insert(env, list, item, index)

    append_all: (env, skip_ret)=>
        import get_type from require('typecheck')
        list = node_assert @fn.value, @, "No list provided"
        items = node_assert @[1], @, "No items provided to append"
        list_t = get_type(list)
        items_t = get_type(items)
        node_assert items_t\is_a(list_t), items, "Cannot append items from a #{items_t} to a list of type #{list_t}"
        list_reg, items_reg, code = env\to_regs(list, items)
        len1,len2,len3,items1,items2,items3,size,tmp = env\fresh_locals "len1","len2","len3","items1","items2","items3","size","tmp"
        code ..= "\n# Append All\n"
        code ..= "#{len1} =l loadl #{list_reg}\n"
        code ..= "#{len2} =l loadl #{items_reg}\n"
        code ..= "#{len3} =l add #{len1}, #{len2}\n"
        code ..= "#{list_reg} =l add #{list_reg}, 8\n"
        code ..= "#{items1} =l loadl #{list_reg}\n"
        code ..= "#{items_reg} =l add #{items_reg}, 8\n"
        code ..= "#{items2} =l loadl #{items_reg}\n"
        code ..= "#{size} =l mul #{len3}, #{list_t.item_type.bytes}\n"
        code ..= "#{items3} =l call $gc_realloc(l #{items1}, l #{size})\n"
        code ..= "#{tmp} =l mul #{len1}, #{list_t.item_type.bytes}\n"
        code ..= "#{tmp} =l add #{tmp}, #{items3}\n"
        code ..= "#{size} =l mul #{len2}, #{list_t.item_type.bytes}\n"
        code ..= "call $memcpy(l #{tmp}, l #{items2}, l #{size})\n"
        code ..= "storel #{len3}, #{list_reg}\n"
        code ..= "#{tmp} =l add #{list_reg}, 8\n"
        code ..= "storel #{items3}, #{tmp}\n"
        reg = if skip_ret then nil else "0"
        return reg,code

    equal_items: (env, skip_ret)=>
        import get_type from require('typecheck')
        list = node_assert @fn.value, @, "No list provided"
        other = node_assert @[1], @, "No items provided for comparison"
        list_t = get_type(list)
        other_t = get_type(other)
        node_assert other_t\is_a(list_t), item, "Cannot compare a list of #{list_t.item_type} with a list of type #{other_t.item_type}"
        item_type = list_t.item_type
        if item_type.base_type == "s" or item_type.base_type == "d"
            node_error @, "equal_items() is not yet supported for floating point values. You should avoid doing equality checks on floating point values because of precision and NaN issues."
        list_reg, other_reg, code = env\to_regs(list, other)
        eq_reg = env\fresh_local "equal"
        compare_mem,done = env\fresh_labels "compare_memory","done"
        code ..= "\n# List comparison\n"
        len1,len2,items1,items2,size = env\fresh_locals "len1","len2","items1","items2","size"
        code ..= "#{len1} =l loadl #{list_reg}\n"
        code ..= "#{len2} =l loadl #{other_reg}\n"
        code ..= "#{eq_reg} =w ceql #{len1}, #{len2}\n"
        code ..= "jnz #{eq_reg}, #{compare_mem}, #{done}\n"
        code ..= "#{compare_mem}\n"
        code ..= "#{size} =l mul #{len1}, #{item_type.bytes}\n"
        code ..= "#{items1} =l add #{list_reg}, 8\n"
        code ..= "#{items1} =l loadl #{items1}\n"
        code ..= "#{items2} =l add #{other_reg}, 8\n"
        code ..= "#{items2} =l loadl #{items2}\n"
        code ..= "#{eq_reg} =w call $memcmp(l #{items1}, l #{items2}, l #{size})\n"
        code ..= "#{eq_reg} =w ceqw #{eq_reg}, 0\n"
        code ..= "jmp #{done}\n"
        code ..= "#{done}\n"
        return eq_reg,code

    copy: (env, skip_ret)=>
        import get_type from require('typecheck')
        list = node_assert @fn.value, @, "No list provided"
        list_t = get_type(list)
        ret,size,items1,items2,copy = env\fresh_locals "ret","size","items1","items2","copy"
        list_reg, code = env\to_reg list
        code ..= "#{ret} =l call $gc_alloc(l 16)\n"
        code ..= "#{size} =l loadl #{list_reg}\n"
        code ..= "storel #{size}, #{ret}\n"
        code ..= "#{size} =l mul #{size}, #{list_t.bytes}\n"
        code ..= "#{items1} =l add #{list_reg}, 8\n"
        code ..= "#{items1} =l loadl #{items1}\n"
        code ..= "#{items2} =l add #{ret}, 8\n"
        code ..= "#{copy} =l call $gc_alloc(l #{size})\n"
        code ..= "call $memcpy(l #{copy}, l #{items1}, l #{size})\n"
        code ..= "storel #{copy}, #{items2}\n"
        return ret,code
        
}

return {:methods, :types}
