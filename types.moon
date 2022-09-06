-- Type checking/inference logic
concat = table.concat
import log, viz, print_err, node_assert, node_error, each_tag from require 'util'
import Measure, register_unit_alias from require 'units'

local Int,Int32,Int16,Int8,Num,Num32

class Type
    is_a: (cls)=> @ == cls or @.__class == cls or cls\contains @
    is_numeric: => @is_a(Int) or @is_a(Num) or @is_a(Int32) or @is_a(Int16) or @is_a(Int8) or @is_a(Num32)
    contains: (other)=> @ == other
    base_type: 'l'
    abi_type: 'l'
    bytes: 8
    nil_value: 0x7FFFFFFFFFFFFFFF
    id_str: => tostring(@)\gsub('[^%w%d.]','')
    __eq: (other)=> type(other) == type(@) and other.__class == @__class and tostring(other) == tostring(@)
    verbose_type: => "#{@}"

class NamedType extends Type
    new: (@name)=>
    __tostring: => @name
    __eq: Type.__eq

Value = NamedType("Value")
Value.contains = (other)=> other.bytes == @bytes
Value.is_a = (other)=> other == @ or other == @__class
Value.nil_value = 0x7FFFFFFFFFFFFFFF

Value32 = NamedType("Value32")
Value32.contains = (other)=> other.bytes == @bytes
Value32.is_a = (other)=> other == @ or other == @__class
Value32.base_type = 'w'
Value32.abi_type = 'w'
Value32.bytes = 4
Value32.nil_value = 0x7FFFFFFF

Value16 = NamedType("Value16")
Value16.contains = (other)=> other.bytes == @bytes
Value16.is_a = (other)=> other == @ or other == @__class
Value16.base_type = 'w'
Value16.abi_type = 'h'
Value16.bytes = 2
Value16.nil_value = 0x7FFF

Value8 = NamedType("Value8")
Value8.contains = (other)=> other.bytes == @bytes
Value8.is_a = (other)=> other == @ or other == @__class
Value8.base_type = 'w'
Value8.abi_type = 'b'
Value8.bytes = 1
Value8.nil_value = 0x7F

class DerivedType extends Type
    new: (@name, @derived_from)=>
        @base_type = @derived_from.base_type
        @abi_type = @derived_from.abi_type
        @bytes = @derived_from.bytes
        @nil_value = @derived_from.nil_value
    __tostring: => @name
    __eq: Type.__eq
    is_a: (cls)=> @ == cls or @derived_from\is_a(cls) or @.__class == cls or cls\contains(@)

class MeasureType extends Type
    new: (@units)=>
    is_numeric: => true
    normalized: => @units == "" and assert(Num) or @
    base_type: 'd'
    abi_type: 'd'
    __tostring: => "<#{@units}>"
    __eq: Type.__eq
    is_a: (cls)=> @ == cls or @.__class == cls or cls\contains @

class ListType extends Type
    new: (@item_type)=>
    __tostring: => "[#{@item_type}]"
    id_str: => "#{@item_type\id_str!}.List"
    __eq: Type.__eq
    is_a: (cls)=> cls == @ or cls == @__class or (cls.__class == ListType and @item_type\is_a(cls.item_type)) or cls\contains(@) or cls\contains(@)
    nil_value: 0

class TableType extends Type
    new: (@key_type, @value_type)=>
        assert @key_type and @value_type
    __tostring: => "{#{@key_type}=#{@value_type}}"
    id_str: => "#{@key_type\id_str!}.#{@value_type\id_str!}.Table"
    is_a: (cls)=> cls == @ or cls == @__class or (cls.__class == TableType and @key_type\is_a(cls.key_type) and @value_type\is_a(cls.value_type)) or cls\contains(@)
    __eq: Type.__eq
    nil_value: 0

local OptionalType
class FnType extends Type
    new: (@arg_types, @return_type, @arg_names=nil)=>
    __tostring: => "#{@arg_signature!}=>#{@return_type}"
    __eq: Type.__eq
    nil_value: 0
    id_str: => "Fn"
    arg_signature: => "(#{concat ["#{a}" for a in *@arg_types], ","})"
    matches: (arg_types, return_type=nil)=>
        if arg_types == "*"
            _=0 -- Free pass
        elseif @arg_names
            unmatched = {name,@arg_types[i] for i,name in ipairs @arg_names}
            for name,t in pairs arg_types
                continue unless type(name) == 'string'
                return false unless unmatched[name] and t\is_a(unmatched[name])
                unmatched[name] = nil

            i,j = 1,1
            while i <= #arg_types and j <= #@arg_names
                t = unmatched[@arg_names[j]]
                if t
                    return false unless arg_types[i]\is_a(t)
                    unmatched[@arg_names[j]] = nil
                    i += 1
                j += 1
                
            unless @varargs
                for _,t in pairs unmatched
                    return false unless t\is_a(OptionalType)
        else
            return false unless #arg_types == #@arg_types or @varargs
            for i=1,#arg_types
                return false unless arg_types[i]\is_a(@arg_types[i])

        if return_type
            return false unless return_type == "*" or @return_type\is_a(return_type)
        return true

class StructType extends Type
    new: (@name, members)=> -- Members: {{type=t, name="Foo"}, {type=t2, name="Baz", inline=true}, ...}
        @members = {}
        @sorted_members = {}
        @memory_size = 0
        if members
            for memb in *members
                @add_member memb.name, memb.type, memb.inline
    add_member: (name, memtype, inline)=>
        offset = @memory_size
        -- Align memory:
        if offset % memtype.bytes != 0
            offset = offset - (offset % memtype.bytes) + memtype.bytes
        @members[name] = {name: name, type: memtype, offset: offset, inline: inline}
        table.insert @sorted_members, @members[name]
        if inline
            @memory_size = offset + (memtype.memory_size or memtype.bytes)
        else
            @memory_size = offset + memtype.bytes
    __tostring: => "#{@name}"
    nil_value: 0
    verbose_type: =>
        mem_strs = {}
        for m in *@sorted_members
            table.insert mem_strs, "#{m.name and type(m.name) == 'string' and m.name..':' or ''}#{m.type}"
        "#{@name}{#{concat mem_strs, ","}}"
    id_str: => "#{@name}"
    __eq: Type.__eq

local EnumType
class UnionType extends Type
    new: (@name, @members)=> -- Members: {{type=t, name="Foo"}, {type=t2, name="Baz"}, ...}
        @abi_type = "l"
        @base_type = "l"
        @memory_size = 8
        @members = {}
        @num_members = 0
        if members
            for memb in *members
                @add_member memb.name, memb.type
                @enum\add_field memb.name
    add_member: (name, member_type)=>
        @num_members += 1
        @members[name] = {type: member_type, index: @num_members}
        @memory_size = math.max(@memory_size, 8+member_type.memory_size)
    __tostring: => "#{@name}"
    nil_value: 0
    verbose_type: =>
        mem_strs = {}
        for name,info in pairs @members
            table.insert mem_strs, "#{name}:#{info.type}"
        "union #{@name}{#{concat mem_strs, ","}}"
    id_str: => "#{@name}"
    __eq: Type.__eq

NilType = NamedType("NilType")
NilType.nil_value = 0

class OptionalType extends Type
    new: (@nonnil)=>
        assert @nonnil and @nonnil != NilType
        if @nonnil.__class == OptionalType
            @nonnil = assert(@nonnil.nonnil)
        @base_type = @nonnil.base_type
        @abi_type = @nonnil.abi_type
        @nil_value = @nonnil.nil_value
        @bytes = @nonnil.bytes
    contains: (other)=> other == @ or other == NilType or (@nonnil and other\is_a(@nonnil))
    __tostring: => @nonnil\is_a(FnType) and "(#{@nonnil})?" or "#{@nonnil}?"
    verbose_type: => @nonnil\is_a(FnType) and "(#{@nonnil\verbose_type!})?" or "#{@nonnil\verbose_type!}?"
    id_str: => "Optional.#{@nonnil\id_str!}"
    __eq: Type.__eq

class EnumType extends Type
    new: (@name, fields={})=>
        @next_value = 0
        @field_values = {}
        @fields = {}
        for f in *fields
            @add_field(f.name, f.value)
    add_field: (name, value=nil)=>
        assert value >= 0 if value
        table.insert @fields, name
        value or= @next_value
        @next_value = value + 1
        @nil_value = @next_value
        @field_values[name] = value
    nil_value: 0
    __tostring: => @name
    id_str: => @name
    __eq: Type.__eq

-- Primitive Types:
Pointer = NamedType("Pointer")
Pointer.nil_value = 0

Num = NamedType("Num")
Num.base_type = 'd'
Num.abi_type = 'd'
Num32 = NamedType("Num32")
Num32.base_type = 's'
Num32.abi_type = 's'
Num32.bytes = 4
Num32.nil_value = 0x7FFFFFFF

Int = NamedType("Int")
Int.base_type = 'l'
Int.abi_type = 'l'

Int32 = NamedType("Int32")
Int32.base_type = 'w'
Int32.abi_type = 'w'
Int32.bytes = 4
Int32.nil_value = 0x7FFFFFFF

Int16 = NamedType("Int16")
Int16.base_type = 'w'
Int16.abi_type = 'h'
Int16.bytes = 2
Int16.nil_value = 0x7FFF

Int8 = NamedType("Int8")
Int8.base_type = 'w'
Int8.abi_type = 'b'
Int8.bytes = 1
Int8.nil_value = 0x7F

Percent = DerivedType("Percent", Num)

Abort = NamedType("Abort")

Bool = NamedType("Bool")
Bool.base_type = 'w'
Bool.abi_type = 'b'
Bool.bytes = 1
Bool.nil_value = 0x7F

String = NamedType("String")
String.nil_value = 0
TypeString = DerivedType("TypeString", String)
Range = StructType("Range", {{name:"first",type:Int},{name:"next",type:Int},{name:"last",type:Int}})
Range.item_type = Int
Range.nil_value = 0

return {
    :Type, :NamedType, :ListType, :TableType, :FnType, :StructType,
    :Value, :Value32, :Value16, :Value8, :Pointer, :Int, :Int32, :Int16, :Int8, :Num, :Num32, :Percent, :String, :Bool, :Abort, :NilType, :Range,
    :OptionalType, :MeasureType, :TypeString, :EnumType, :UnionType,
}
