-- Custom implementations of list methods
import FnType, OptionalType, NilType, Int, Num from require 'types'
import log, viz, node_assert, node_error, each_tag, context_err from require 'util'

types = {
    of: => FnType({@,Num}, Num, nil)
}

methods = {
    of: (env)=>
        pct_reg, num_reg, code = env\to_regs(@fn.value, @[1])
        ret = env\fresh_locals "result"
        code ..= "#{ret} =d mul #{pct_reg}, #{num_reg}\n"
        return ret, code
}

return {:methods, :types}
