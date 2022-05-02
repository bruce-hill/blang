#!/usr/bin/env moon
import log, viz from require 'util'
parse = require 'parse'
import compile_prog from require 'compile'

for f in *arg
    log "Compiling #{f}"
    with io.open f
        text = \read "*a"
        log "\x1b[1;34m#{text}\x1b[m"
        ast = parse text, f
        assert ast, "No match!"
        log viz(ast)

        code = compile_prog ast, f

        line = 0
        numbered_code = code\gsub "[^\n]*", =>
            line += 1
            "#{("% 4d")\format line}| #{@}"
        log "\x1b[1;36m#{numbered_code}\x1b[m"

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
        run "./#{f}.o"

        \close!
