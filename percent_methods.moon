-- Custom implementations of list methods
import FnType, OptionalType, NilType, Num, Percent from require 'types'
import log, viz, node_assert, node_error, each_tag, context_err from require 'util'

types = {
    of: => FnType({@,Num}, Num, nil)
    clamped: => FnType({@,@,@}, @, nil)
}

methods = {
    of: (env)=>
        pct_reg, num_reg, code = env\to_regs(@fn.value, @[1])
        ret = env\fresh_locals "result"
        code ..= "#{ret} =d mul #{pct_reg}, #{num_reg}\n"
        return ret, code

    clamped: (env)=>
        pct_reg, low_reg, high_reg, code = env\to_regs(@fn.value, @[1], @[2])
        result = env\fresh_locals "result"
        code ..= "#{result} =d call $d_mid(d #{pct_reg}, d #{low_reg}, d #{high_reg})\n"
        return result,code
}

return {:methods, :types}
