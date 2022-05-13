# Blang

Blang is a small, statically typed, compile imperative language with ergonomic
syntax that uses [QBE](https://c9x.me/compile/) as a backend to compile from
there to assembly code and then to a binary.

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

## License

Blang is released under the MIT license with the Commons Clause, see
[LICENSE](LICENSE) for full details.
