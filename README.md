# Blang

Blang is a small, statically typed, compile imperative language with ergonomic
syntax that uses [QBE](https://c9x.me/compile/) as a backend to compile from
there to assembly code and then to a binary.

## Example

```
def sing_bottles_song(n:Int):
    for i in -(1..n)
        "$i bottle$(i > 1? "s"; "") of beer on the wall" | $puts
    between
        "Take one down, pass it around... " | $printf

    "No more bottles of beer on the wall :(" | $puts

sing_bottles_song(99)
```

## License

Blang is released under the MIT license with the Commons Clause, see
[LICENSE](LICENSE) for full details.
