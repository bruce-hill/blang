-- Custom implementations of list methods
import FnType, OptionalType, NilType, Num, Percent from require 'types'
import log, viz, node_assert, node_error, each_tag, context_err from require 'util'

types = {
    of: => FnType({@,Num}, Num, nil)
    clamped: => FnType({@,@,@}, @, nil)
}

methods = {
    of: (code)=>
        pct_reg, num_reg = code\add_values(@fn.value, @[1])
        ret = code\fresh_locals "result"
        code\add "#{ret} =d mul #{pct_reg}, #{num_reg}\n"
        return ret

    clamped: (code)=>
        pct_reg, low_reg, high_reg = code\add_values(@fn.value, @[1], @[2])
        result = @fresh_locals "result"
        code\add "#{result} =d call $d_mid(d #{pct_reg}, d #{low_reg}, d #{high_reg})\n"
        return result
}

return {:methods, :types}
