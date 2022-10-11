-- Custom implementations of list methods
import FnType, OptionalType, ListType, StructType, NilType, String, Bool, Int32, Int, Range, Pointer from require 'types'
import log, viz, node_assert, node_error, each_tag, context_err from require 'util'

types = {
    get: => FnType({@,Int}, OptionalType(@item_type), {"list","index"})
    get_or_fail: => FnType({@,Int}, @item_type, {"list","index"})
    data_pointer: => FnType({@}, Pointer, {"list"})
    range: => FnType({@,Range}, @, {"list","range"})
    copy: => FnType({@}, @, {"list"})
    equal_items: => FnType({@,@}, Bool, {"list","other"})
    insert: => FnType({@,@item_type,OptionalType(Int)}, NilType, {"list","item","at"})
    insert_all: => FnType({@,@,OptionalType(Int)}, NilType, {"list","items","at"})
    remove: => FnType({@,OptionalType(Int)}, NilType, {"list","at"})
    remove_range: => FnType({@,Range}, NilType, {"list","range"})
    find: => FnType({@,@item_type,OptionalType(Int)}, OptionalType(Int), {"list","item","after"})
    count: => FnType({@,@item_type,OptionalType(Int)}, Int, {"list","item","after"})
    reverse: => FnType({@}, NilType, {"list"})
    reversed: => FnType({@}, @, {"list"})
    wrapped: => FnType({@,Int}, Int, {"list","index"})
    join: => FnType({@,OptionalType(String)}, String, {"list","glue"})
    sort: =>
        ptr = StructType("", {{name:1, type:@item_type}})
        FnType({@,FnType({ptr,ptr},Int32),OptionalType(Bool)}, NilType, {"list","by","reversed"})
    sorted: => FnType({@,OptionalType(FnType(@item_type,@item_type,Int32)),Bool}, @, {"list","by","reversed"})
    get_random: => FnType({@}, @item_type, {"list"})
}

get = (code, use_failure)=>
    assert @__type, "No type"
    local list,index
    if @__tag == "IndexedTerm"
        list,index = @value,@index
    elseif @__tag == "FnCall"
        list,index = @fn.value,@[1]
    assert list and list.__type\is_a(ListType), "WTF: #{@__type}"
    assert index, "WTF: #{viz @}"

    list_reg,index_reg = code\add_values list, index
    len = code\fresh_locals "len"
    code\add "#{len} =l loadl #{list_reg}\n"

    -- Bounds check:
    src,index_too_low,index_too_high,bad_index,item = code\fresh_locals "src","index_too_low","index_too_high","bad_index","item"
    index_error,index_ok,done = code\fresh_labels "index_error","index_ok","done"
    code\add "#{index_too_low} =w csltl #{index_reg}, 1\n"
    code\add "#{index_too_high} =w csgtl #{index_reg}, #{len}\n"
    code\add "#{bad_index} =w or #{index_too_low}, #{index_too_high}\n"
    code\add "jnz #{bad_index}, #{index_error}, #{index_ok}\n"
    code\add_label index_error
    if use_failure
        code\add "call $dprintf(l 2, l #{code\get_string_reg(context_err(index, "Invalid index: %ld (list size = %ld)", 2).."\n", "index_error")}, l #{index_reg}, l #{len})\n"
        code\add "call $_exit(l 1)\n"
        code\add "jmp #{index_error}\n"
    else
        code\set_nil list.__type.item_type, item
        code\add "jmp #{done}\n"
    code\add_label index_ok

    items = code\fresh_local "items"
    code\add "#{items} =l add #{list_reg}, 8\n"
    code\add "#{items} =l loadl #{items}\n"
    offset,item_loc = code\fresh_locals "offset","item_location"
    code\add "#{offset} =l sub #{index_reg}, 1\n"
    item_type = list.__type.item_type
    code\add "#{offset} =l mul #{offset}, #{item_type.bytes}\n"
    code\add "#{item_loc} =l add #{items}, #{offset}\n"
    if item_type.base_type == "d" or item_type.base_type == "s"
        tmp = code\fresh_local "list.item.as_int"
        int_type = item_type.base_type == "d" and "l" or "w"
        code\add "#{tmp} =#{int_type} load#{int_type} #{item_loc}\n"
        code\add "#{item} =d cast #{tmp}\n"
    else
        code\add "#{item} =#{item_type.base_type} #{item_type.load} #{item_loc}\n"

    if not use_failure
        code\add_label done
        
    return item

methods = {
    get: (code)=> get(@, code, false)
    get_or_fail: (code)=> get(@, code, true)

    data_pointer: (code)=>
        list_reg = code\add_value @[1]
        data = code\fresh_locals "data"
        code\add "#{data} =l add list_reg, 8\n"
        return data

    range: (code)=>
        list,range = if @__tag == "IndexedTerm"
            @value,@index
        else
            @[1],@[2]

        t = list.__type
        list_reg,range_reg = code\add_values list,range
        use_aliasing = "1" -- TODO: re-enable when it's safe to do so
        slice = code\fresh_local "slice"
        code\add "#{slice} =l call $list_slice(l #{list_reg}, l #{range_reg}, l #{t.item_type.bytes}, w #{use_aliasing})\n"
        return slice

    insert: (code)=>
        list = node_assert @fn.value, @, "No list provided"
        local index, item
        positional = {}
        for arg in *@
            if arg.__tag == "KeywordArg"
                if arg.name[0] == "at"
                    index = arg.value
                elseif arg.name[0] == "item"
                    item = arg.value
                else
                    node_error arg.name, "Not a valid keyword argument, expected `at=` or `item=`"
            else
                table.insert positional, arg
        if not item
            item = table.remove(positional,1)
        if not index
            index = table.remove(positional,1)
        node_assert item, @, "No item provided to insert"

        list_t = list.__type
        list_reg, item_reg = code\add_values list, item
        item_t = item.__type
        node_assert item_t\is_a(list_t.item_type), item, "Cannot put a #{item_t} in a list of type #{list_t}"

        item64 = if item_t.base_type == "s" or item_t.base_type == "d"
            reg = code\fresh_local "item64"
            code\add "#{reg} =l cast #{item_reg}\n"
            reg
        elseif item_t.bytes < 8
            reg = code\fresh_local "item64"
            "#{reg} =l extu#{item_t.abi_type} #{item_reg}\n"
            reg
        else
            item_reg

        index_reg = if index
            code\add_value index
        else
            "#{Int.nil_value}"

        err_fmt = if index
            code\get_string_reg(context_err(index, "Invalid list index: %ld", 2).."\n", "index_error")
        else
            code\get_string_reg("", "empty")
        code\add "call $list_insert(l #{list_reg}, l #{item_t.bytes}, l #{index_reg}, l #{item64}, l #{err_fmt})\n"
        return "0"

    insert_all: (code)=>
        list = node_assert @fn.value, @, "No list provided"
        local index, items
        positional = {}
        for arg in *@
            if arg.__tag == "KeywordArg"
                if arg.name[0] == "at"
                    index = arg.value
                elseif arg.name[0] == "items"
                    items = arg.value
                else
                    node_error arg.name, "Not a valid keyword argument, expected `at=` or `items=`"
            else
                table.insert positional, arg
        if not items
            items = table.remove(positional,1)
        if not index
            index = table.remove(positional,1)
        node_assert items, @, "No items provided to insert"

        list_t = list.__type
        list_reg, items_reg = code\add_values(list, items)

        index_reg = if index
            code\add_value index
        else
            "#{Int.nil_value}"

        items_t = items.__type
        node_assert items_t == list_t, @, "Cannot put item from #{items_t} in a list of type #{list_t}"
        err_fmt = code\get_string_reg(context_err(@, "Invalid list index: %ld", 2).."\n", "index_error")
        code\add "call $list_insert_all(l #{list_reg}, l #{list_t.item_type.bytes}, l #{index_reg}, l #{items_reg}, l #{err_fmt})\n"
        return "0"

    equal_items: (code)=>
        list = node_assert @fn.value, @, "No list provided"
        other = node_assert @[1], @, "No items provided for comparison"
        list_t = list.__type
        other_t = other.__type
        node_assert other_t\is_a(list_t), item, "Cannot compare a list of #{list_t.item_type} with a list of type #{other_t.item_type}"
        item_type = list_t.item_type
        if item_type.base_type == "s" or item_type.base_type == "d"
            node_error @, "equal_items() is not yet supported for floating point values. You should avoid doing equality checks on floating point values because of precision and NaN issues."
        list_reg, other_reg = code\add_values(list, other)
        eq_reg = code\fresh_locals "equal"
        code\add "#{eq_reg} =w call $list_equal(l #{list_reg}, l #{other_reg}, l #{item_type.bytes})\n"
        return eq_reg

    copy: (code)=>
        list = node_assert @fn.value, @, "No list provided"
        list_t = list.__type
        list_reg = code\add_value list
        copy_reg = code\fresh_locals "copy"
        code\add "#{copy_reg} =l call $list_copy(l #{list_reg}, l #{list_t.item_type.bytes})\n"
        return copy_reg

    remove: (code)=>
        list = node_assert @fn.value, @, "No list provided"
        local first,last
        positional = {}
        for arg in *@
            if arg.__tag == "KeywordArg"
                if arg.name[0] == "at"
                    first = arg.value
                elseif arg.name[0] == "through"
                    last = arg.value
                else
                    node_error arg.name, "Not a valid keyword argument, expected `at=`"
            else
                table.insert positional, arg
        if not first
            first = table.remove(positional,1)
        if not last
            last = table.remove(positional,1)

        list_reg = code\add_value(list)
        first_reg = if first
            code\add_value first
        else
            "#{Int.nil_value}"

        last_reg = if last
            code\add_value last
        else
            "#{Int.nil_value}"

        item_t = list.__type.item_type
        err_fmt = if first
            code\get_string_reg(context_err(@, "Invalid removal range: %ld..%ld", 2).."\n", "index_error")
        else
            code\get_string_reg("", "empty")
        code\add "call $list_remove(l #{list_reg}, l #{item_t.bytes}, l #{first_reg}, l #{last_reg}, l #{err_fmt})\n"
        return "0"

    get_random: (code)=>
        list = if @__tag == "IndexedTerm"
            @value
        elseif @__tag == "FnCall"
            @fn.value
        list_reg = code\add_value list
        len,items = code\fresh_locals "len","items"
        code\add "#{len} =l loadl #{list_reg}\n"
        empty_label,ok_label,done = code\fresh_labels "is_empty","has_items","done"
        code\add "jnz #{len}, #{ok_label}, #{empty_label}\n"

        code\add_label empty_label
        code\add "call $dprintf(l 2, l #{code\get_string_reg(context_err(list, "List is unexpectedly empty", 2).."\n", "index_error")})\n"
        code\add "call $_exit(l 1)\n"
        code\add "jmp #{done}\n"

        code\add_label ok_label

        offset,item_loc,item = code\fresh_locals "offset","item_location","item"
        code\add "#{offset} =l call $random_range(l 0, l #{len})\n"
        code\add "#{items} =l add #{list_reg}, 8\n"
        code\add "#{items} =l loadl #{items}\n"
        item_type = list.__type.item_type
        code\add "#{offset} =l mul #{offset}, #{item_type.bytes}\n"
        code\add "#{item_loc} =l add #{items}, #{offset}\n"
        if item_type.base_type == "d" or item_type.base_type == "s"
            tmp = code\fresh_local "list.item.as_int"
            int_type = item_type.base_type == "d" and "l" or "w"
            code\add "#{tmp} =#{int_type} load#{int_type} #{item_loc}\n"
            code\add "#{item} =d cast #{tmp}\n"
        else
            code\add "#{item} =#{item_type.base_type} #{item_type.load} #{item_loc}\n"
        code\add "jmp #{done}\n"

        code\add_label done

        return item

    sort: (code)=>
        list = node_assert @fn.value, @, "No list provided"
        list_reg = code\add_value list
        by = node_assert @[1], @, "No comparison function provided"
        by_reg = code\add_value by
        len = code\fresh_local "len"
        code\add "#{len} =l loadl #{list_reg}\n"
        list_t = list.__type
        items_reg = code\fresh_local "items"
        code\add "#{items_reg} =l add #{list_reg}, 8\n"
        code\add "#{items_reg} =l loadl #{items_reg}\n"
        code\add "call $qsort(l #{items_reg}, l #{len}, l #{list_t.item_type.bytes}, l #{by_reg})\n"
        return "0"

    sorted: (code)=> error "Not implemented"
    remove_range: => error "Not implemented"
    find: => error "Not implemented"
    count: => error "Not implemented"
    join: (code)=>
        list = @fn.value
        glue = @[1]
        t = list.__type
        list_reg = code\add_value list
        buf_reg = code\fresh_local "buf"
        code\add "#{buf_reg} =l copy 0\n"
        make_between = if glue
            glue_reg = code\add_value glue
            -- NOTE: CORD_cat() works with 0 as equivalent to "", so no need to check
            -- for a nil value
            -> "#{buf_reg} =l call $CORD_cat(l #{buf_reg}, l #{glue_reg})\n"
        else
            nil

        item_reg = code\fresh_local "item"
        code\add_for_loop({
            type: t, iter_reg:list_reg, val_reg:item_reg,
            make_body: ->
                item_str = code\fresh_local "item.string"
                fn = code\get_tostring_fn t.item_type, scope
                return code\new_code "#{item_str} =l call #{fn}(#{t.item_type.base_type} #{item_reg}, l 0)\n",
                    "#{buf_reg} =l call $CORD_cat(l #{buf_reg}, l #{item_str})\n"
            make_between: make_between
        })
        code\add "#{buf_reg} =l call $CORD_to_const_char_star(l #{buf_reg})\n"
        code\add "#{buf_reg} =l call $bl_string(l #{buf_reg})\n"
        return buf_reg

    reverse: => error "Not implemented"
    reversed: => error "Not implemented"
    wrapped: => error "Not implemented"
}

return {:methods, :types}
