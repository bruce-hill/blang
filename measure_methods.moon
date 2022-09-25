-- Custom implementations of list methods
import FnType, OptionalType, NilType, Num, Percent from require 'types'
import log, viz, node_assert, node_error, each_tag, context_err from require 'util'

types = {
    units: => FnType({@}, @, nil)
    scalar: => FnType({@}, Num, nil)
}

methods = {
    units: (env)=>
        return "d_1.0", ""

    scalar: (env)=>
        reg, code = env\to_regs(@fn.value)
        return reg,code
}

return {:methods, :types}
