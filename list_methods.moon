-- Custom implementations of list methods
import FnType, OptionalType, ListType, NilType, String, Bool, Int from require 'types'
import log, viz, node_assert, node_error, each_tag from require 'util'

types = {
    copy: => @
    append: => FnType({@,@item_type}, NilType, {"list","item"})
    prepend: => FnType({@,@item_type}, NilType, {"list","item"})
    append_all: => FnType({@,@}, NilType, {"list","items"})
    prepend_all: => FnType({@,@}, NilType, {"list","items"})
    insert: => FnType({@,@item_type,OptionalType(Int)}, NilType, {"list","item","at"})
    insert_all: => FnType({@,@,OptionalType(Int)}, NilType, {"list","items","at"})
    pop: => FnType({@,OptionalType(Int)}, NilType, {"list","from"})
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

methods = {
    append: (env, skip_ret)=>
        import get_type from require('typecheck')
        list = node_assert @fn.value, @, "No list provided"
        item = node_assert @[1], @, "No item provided to append"
        list_t = get_type(list)
        item_t = get_type(item)
        node_assert item_t\is_a(list_t.item_type), item, "Cannot append a #{item_t} to a list of type #{list_t}"
        list_reg, item_reg, code = env\to_regs(list, item)
        new_len,len,new_items,items,new_size,tmp = env\fresh_locals "new.len","len","new.items","items","new.size","tmp"
        code = "\n# Append\n"
        code ..= "#{len} =l loadl #{list_reg}\n"
        code ..= "#{new_len} =l add #{len}, 1\n"
        code ..= "#{items} =l add #{list_reg}, 8\n"
        code ..= "#{items} =l loadl #{items}\n"
        code ..= "#{new_size} =l mul #{new_len}, #{item_t.bytes}\n"
        code ..= "#{new_items} =l call $gc_realloc(l #{items}, l #{new_size})\n"
        code ..= "#{tmp} =l add #{new_items}, #{new_size}\n"
        code ..= "#{tmp} =l sub #{tmp}, #{item_t.bytes}\n"
        code ..= "store#{item_t.abi_type} #{item_reg}, #{tmp}\n"
        code ..= "storel #{new_len}, #{list_reg}\n"
        code ..= "#{tmp} =l add #{list_reg}, 8\n"
        code ..= "storel #{new_items}, #{tmp}\n"
        reg = if skip_ret then nil else "0"
        return reg,code

    prepend: (env, skip_ret)=>
        import get_type from require('typecheck')
        list = node_assert @fn.value, @, "No list provided"
        item = node_assert @[1], @, "No item provided to prepend"
        list_t = get_type(list)
        item_t = get_type(item)
        node_assert item_t\is_a(list_t.item_type), item, "Cannot prepend a #{item_t} to a list of type #{list_t}"
        list_reg, item_reg, code = env\to_regs(list, item)
        new_len,len,new_items,items,size,new_size,tmp = env\fresh_locals "new.len","len","new.items","items","size","new.size","tmp"
        code = "\n# Prepend\n"
        code ..= "#{len} =l loadl #{list_reg}\n"
        code ..= "#{size} =l mul #{len}, #{item_t.bytes}\n"
        code ..= "#{new_len} =l add #{len}, 1\n"
        code ..= "#{items} =l add #{list_reg}, 8\n"
        code ..= "#{items} =l loadl #{items}\n"
        code ..= "#{new_size} =l mul #{new_len}, #{item_t.bytes}\n"
        code ..= "#{new_items} =l call $gc_realloc(l #{items}, l #{new_size})\n"
        code ..= "#{tmp} =l add #{new_items}, #{item_t.bytes}\n"
        code ..= "call $memmove(l #{tmp}, l #{new_items}, l #{size})\n"
        code ..= "store#{item_t.abi_type} #{item_reg}, #{new_items}\n"
        code ..= "storel #{new_len}, #{list_reg}\n"
        code ..= "#{tmp} =l add #{list_reg}, 8\n"
        code ..= "storel #{new_items}, #{tmp}\n"
        code ..= "\n"
        reg = if skip_ret then nil else "0"
        return reg,code

    append_all: (env, skip_ret)=>
        import get_type from require('typecheck')
        list = node_assert @fn.value, @, "No list provided"
        items = node_assert @[1], @, "No items provided to append"
        list_t = get_type(list)
        items_t = get_type(items)
        node_assert items_t\is_a(list_t), items, "Cannot append items from a #{items_t} to a list of type #{list_t}"
        list_reg, items_reg, code = env\to_regs(list, items)
        len1,len2,len3,items1,items2,items3,size,tmp = env\fresh_locals "len1","len2","len3","items1","items2","items3","size","tmp"
        code = "\n# Append All\n"
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
}

return {:methods, :types}
