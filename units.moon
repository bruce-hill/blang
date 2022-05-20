aliases = {}

canonicalize = (str)->
    scale = 1.0
    units = {}
    for div,u,exp in str\gmatch("(%/?)[ ]*(%w+)%^?(%-?%d*)")
        exp = (not exp or exp == "") and 1 or tonumber(exp)
        if div != "" then exp = -exp
        alias = aliases[u]
        if alias
            for u2,exp2 in pairs(alias.units)
                scale = exp < 0 and scale / alias.amount or scale * alias.amount
                units[u2] = (units[u2] or 0) + exp*exp2
        else
            units[u] = (units[u] or 0) + exp

    units_sorted = [u for u,exp in pairs(units)]
    table.sort units_sorted, (a,b)->
        if units[a] == units[b]
            return a < b
        else
            return units[a] > units[b]

    chunks = {}
    for _,u in ipairs(units_sorted)
        exp = units[u]
        if exp == 1
            table.insert(chunks, u)
        elseif exp == -1
            table.insert(chunks, (("/%s")\format(u)))
        elseif exp < 0
            table.insert(chunks, (("/%s^%d")\format(u, -exp)))
        elseif exp > 0
            table.insert(chunks, (("%s^%d")\format(u, exp)))
    return table.concat(chunks, " ")\gsub(" /","/"), units, scale

class Measure
    new: (amount, str)=>
        @str, @units, scale = canonicalize(str)
        @amount = amount * scale
    __add: (other)=>
        assert(@str == other.str, "Incompatible units")
        return Measure(@amount + other.amount, @str)
    __sub: (other)=>
        assert(@str == other.str, "Incompatible units")
        return Measure(@amount - other.amount, @str)
    __mul: (other)=>
        if type(self) == 'number'
            return Measure(self * other.amount, other.str)
        elseif type(other) == 'number'
            return Measure(other * @amount, @str)
        return Measure(@amount * other.amount, @str.." "..other.str)
    __div: (other)=>
        if type(other) == 'number'
            return Measure(@amount / other, @str)
        return @ * other\invert()
    __tostring: =>
        if @str == ""
            return tostring(@amount)
        return ("%s<%s>")\format(@amount, @str)
    invert: =>
        chunks = [("%s^%d")\format(u, -exp) for u,exp in pairs(@units) when exp != 0]
        return Measure(1/@amount, table.concat(chunks, " "))
    in_units: (target)=> ("%s<%s>")\format(self/Measure(1, target), target)

return {
    :Measure,
    register_unit_alias: (alias_name, unit)->
        aliases[alias_name] = unit
}
