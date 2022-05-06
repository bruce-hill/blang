#!/usr/bin/env moon
import log, viz, set_file from require 'util'
parse = require 'parse'
import compile_prog from require 'compile'

number_code = (code, color="1")->
    line = 0
    (code\gsub("\n$","")\gsub "[^\n]*", =>
        line += 1
        "\x1b[2m#{("% 4d")\format line}|\x1b[22m \x1b[#{color}m#{@}\x1b[m"
    )

files = arg
args = {}
for i=1,#arg
    if arg[i] == "--"
        files = {table.unpack(arg, 1, i-1)}
        args = {table.unpack(arg, i+1, #arg)}

for f in *files
    log "\x1b[1;4mFile #{f}\x1b[m"
    with io.open f
        text = \read "*a"
        set_file f, text
        log number_code(text, "34;1")
        ast = parse text, f
        assert ast, "No match!"
        log viz(ast)

        code = compile_prog ast, f

        log number_code(code, "36;1")

        with io.open f..".qbe", "w"
            \write code
            \close!

        run = (cmd)->
            log "> \x1b[1m#{cmd}\x1b[m"
            assert os.execute cmd

        log "\x1b[2mRunning QBE...\x1b[m"
        run "qbe #{f}.qbe > #{f}.s"
        log "\x1b[2mCompiling assembly...\x1b[m"
        run "cc #{f}.s lib/say.o lib/range.o -ggdb -o #{f}.o -lm"
        log "\x1b[2mRunning program:\x1b[m"
        run "./#{f}.o #{table.concat args, " "}"

        \close!
