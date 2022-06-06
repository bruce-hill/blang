# Blang

Blang is a small, statically typed, compiled imperative language with ergonomic
syntax. It uses [QBE](https://c9x.me/compile/) as a backend IR, and compiles
from there to assembly code and then to a binary.

## Example

```
def sing_bottles_song(n:Int):
    for i in n..0
        when i is 0
            "No more bottles of beer on the wall! :(" | $puts
        is 1
            "One last bottle of beer on the wall" | $puts
        else
            "$i bottles of beer on the wall" | $puts
    between
        "Take one down, pass it around... " | $puts


sing_bottles_song(99)
```

See [test/\*.bl](test/) for more examples.

## Language Features

[See features.md for writeups of some of the features in blang.](features.md)

## Dependencies

The Blang compiler is written in [Moonscript](https://moonscript.org), uses
[QBE](https://c9x.me/compile/) as a backend, before being compiled from
assembly with your assembler of choice. Blang uses the following libraries:

- Garbage collection: [Boehm garbage collector](https://www.hboehm.info/gc/)
    - Available from your package manager of choice: `pacman -S gc`
- Parsing and string pattern matching: [bp](https://github.com/bruce-hill/bp/)
    - Install via `git clone https://github.com/bruce-hill/bp/ && cd bp && make && sudo make install-lib`
- Hash maps and string interning: [bhash](https://github.com/bruce-hill/bhash/)
    - Install via `git clone https://github.com/bruce-hill/bhash/ && cd bhash && make && sudo make install`

## Usage

Once the necessary dependencies are installed, you can use `./blang
your-file.bl` to run a file directly or `./blangc your-file.bl` to compile it
into a binary called `your-file.o`. See `blang --help` and `blangc --help` for
full usage info.

## License

Blang is released under the MIT license with the Commons Clause, see
[LICENSE](LICENSE) for full details.
