-- Math functions as methods on numbers
import FnType, OptionalType, NilType, Bool, Num, Int from require 'types'
import log, viz, node_assert, node_error, each_tag, context_err from require 'util'

simple_methods = {
    "acos", "acosh", "asin", "asinh", "atan", "atanh", "cbrt", "ceil", "cos", "cosh", "erf",
    "erfc", "exp", "exp2", "expm1", "fabs", "floor", "j0", "j1", "lgamma", "log", "log10",
    "log1p", "log2", "logb", "round", "sin", "sinh", "sqrt", "tan", "tanh", "tgamma", "trunc", "y0", "y1",
}

types = {}
methods = {}

for method in *simple_methods
    types[method] = (t)-> FnType({t},t,{"n"})
    methods[method] = (code)=>
        num_reg = code\add_value(@fn.value)
        result = @fresh_locals "result"
        code\add "#{result} =d call $#{method}(d #{num_reg})\n"
        return result

return {:methods, :types}
