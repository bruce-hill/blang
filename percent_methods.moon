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
        -- Branchless clamp:
        --  tmp := (x + hi - |x - high|) / 2
        --  ret := (tmp + lo + |tmp - lo|) / 2
        tmp,result,diff_lo,diff_hi = env\fresh_locals "tmp","result","diff_lo","diff_hi"
        code ..= "#{tmp} =d add #{pct_reg}, #{high_reg}\n"
        code ..= "#{diff_hi} =d sub #{pct_reg}, #{high_reg}\n"
        code ..= "#{diff_hi} =d call $fabs(d #{diff_hi})\n"
        code ..= "#{tmp} =d sub #{tmp}, #{diff_hi}\n"
        code ..= "#{tmp} =d mul #{tmp}, d_0.5\n"

        code ..= "#{result} =d add #{tmp}, #{low_reg}\n"
        code ..= "#{diff_lo} =d sub #{tmp}, #{low_reg}\n"
        code ..= "#{diff_lo} =d call $fabs(d #{diff_lo})\n"
        code ..= "#{result} =d add #{result}, #{diff_lo}\n"
        code ..= "#{result} =d mul #{result}, d_0.5\n"
        return result,code
}

return {:methods, :types}
