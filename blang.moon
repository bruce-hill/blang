#!/usr/bin/env moon
import log, viz from require 'util'
parse = require 'parse'
import compile_prog from require 'compile'

number_code = (code, color="1")->
    line = 0
    (code\gsub("\n$","")\gsub "[^\n]*", =>
        line += 1
        "\x1b[2m#{("% 4d")\format line}|\x1b[22m \x1b[#{color}m#{@}\x1b[m"
    )

files = arg
for f in *files
    break if f == "--"
    log "Compiling #{f}"
    with io.open f
        text = \read "*a"
        log number_code(text, "34;1")
        ast = parse text, f
        assert ast, "No match!"
        log viz(ast)

        code = compile_prog ast, f

        log number_code(code, "36;1")

        with io.open f..".ssa", "w"
            \write code
            \close!

        run = (cmd)->
            log "> \x1b[1m#{cmd}\x1b[m"
            assert os.execute cmd

        log "\x1b[2mRunning QBE...\x1b[m"
        run "qbe #{f}.ssa > #{f}.S"
        log "\x1b[2mCompiling assembly...\x1b[m"
        run "cc -O0 #{f}.S -o #{f}.o -lm"
        log "\x1b[2mRunning program:\x1b[m"
        run "./#{f}.o one two three"

        \close!
