# AlgebraicDatas
This package literally provides algebraic data types(ADT) and performs pattern matching for them. It's inspried by some packages: [ast-pattern-mathing](https://github.com/krux02/ast-pattern-matching) and [gara](https://github.com/alehander92/gara), and [`enum`](https://doc.rust-lang.org/book/ch06-01-defining-an-enum.html) and [pattern matching](https://doc.rust-lang.org/book/ch18-00-patterns.html) in the [Rust](https://www.rust-lang.org/) language.

It provids two macros:
* `` `?=` `` macro  
    It can be used like Rust's if let syntax.
    ```nim
    let a = Option.Some(3)
    if Some(val) ?= a:
        echo val #> 3
    if None ?= a:
        echo "none"
    ```
* `match` macro  
    It's used for pattern matching. It's internally a compostion of if-else statement and `` `?=` `` macros.
    ```nim
    let a = Option.Some(3)
    match a
    of Some(val):
        echo val #> 3
    of None:
        echo "none"
    ```
    If you are using [CaseStatementMacros, an experimental feature](https://nim-lang.org/docs/manual_experimental.html#case-statement-macros) via `{.experimental: "caseStmtMacros".}`, you can use the `case` syntax instead of the `match` macro.
    ```nim
    let a = Option.Some(3)
    case a # not `match`
    of Some(val):
        echo val #> 3
    of None:
        echo "none"
    ```
    You can use `case` syntax and `match` macro as an expression.
    ```nim
    let
        a = Option.Some(3)
        b = case a # The same goes for `match` macro
        of Some(val):
            val
        of _:
            0
    echo b #> 3
    ```

## Features
* [ADT](#adt)
  * [Defining an ADT](#defining-an-adt)
* [Pattern matching](#pattern-mathing)
  * [Discarding](#discarding)
  * [Value](#value)
  * [Named variable](#named-variable)
  * [Exsiting variable](#existing-variable)
##  ADT
**TODO**: write motivation to implement
### Defining an ADT
You can define an ADT by using a macro called `Algebraic`. It looks like this:
```nim
Algebraic Option[T]:
    Some(T)
    None
```
## Pattern mathing
### Discarding
A discarding pattern `_` will match anything. It will be used when you want to evaluate a branch ignoring the value.
```nim
let a = "a"

match a:
of _:
    echo "hello"

#> hello
```
expands to:
```nim
if true:
    echo "hello"
```
and, 
```nim
let a = "a"

match a:
of anyPattern:
    echo "hello"
of _:
    echo "world"
```
roughly expands to:
```nim
if anyPattern ?= a:
    echo "hello"
else:
    echo "world"
```
### Value
You can use value pattern with `AtomType` or `string` type as you does in case statement. Examples would be:
```nim
let a = 2

{.hint: "When you use case statement macro instead of `match` macro with string type, int type or ordered types, the Nim compiler dose not invoke `match` macro but the built-in case statement.".}
match a: # colon is needed on `match` macro
of 1:
    echo "One"
of 2:
    echo "Two"
of _:
    echo "Any number"

#> Two
```
### Range pattern
```nim
let a = 2

match a:
of 0:
    echo "Zero"
of 1..int.high:
    echo "Positive"
of int.low .. -1:
    echo "Negative"

#> Positive
```
### Named variable 
```nim
let a = (3, 4)

case a # colon is optional on `case` statement macro
of (b, _):
    echo b
    
#> 3
```
### Existing variable
```nim
let
    a = (3, 4)
    b = 1
    c = 3

case a
of (!b, _):
    echo "a[0] == b"
of (!c, _):
    echo "a[0] == c"
of _:
    echo "not match"

#> a[0] == c
```
### Tuple
Defining a tuple like below:
```nim
type Color = tuple
    r: uint8
    g: uint8
    b: uint8
    a: uint8
```
#### Destructing a tuple
```nim
var red: Color = (r: 255'u8, g: 1'u8, b: 2'u8, a: 3'u8)

case red
of (r: 255, g: _, b, a: _):
    echo b

#> 2
```
#### Same value
```nim
var red: Color = (r: 128, g: 128, b: 255, a: 255)

case red
of (r, r, b, b):
    echo "match"

#> match

case red
of (r, g: r, b: r@_, a: r):
    echo r

#> 255

case red
of (r, b: r, g: r@_, a: r):
    echo r
```
### Tuple (who has unnamed field)
Defining a tuple like below:
```nim
type Color = (int8, int8, int8, int8)
```
```nim
var red: Color = (255, 0, 0, 255)
case red
of (a1, a2, a3, a4):
    echo a1 + a2 + a3 + a4

#> 510
```
plan:  
like field pattern
```nim
case red
of (0: a1, 1: a2, 2: a3, 3: a4):
    echo a1 + a2 + a3 + a4
```
### Object
The same goes for the tuple pattern
#### Nil pattern
You can use Nil pattern `nil` with nillable object, namely `ref object` or `ptr object`.
```nim
var
    fs = newFileStream("example.txt", fmRead)
    line: string

case fs
of nil:
    raise newException(IOError, "Not found such file")
of _:
    while fs.readLine(line):
        echo line
    fs.close()
```


## License
Mit License  
**author**: chocobo333

# Internal implementations
**TODO**: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa


# TODO
- [ ] documentation
- [ ] smarter error infomation: tuple length check, wheter ofBranch is, wheter discard pattern is,  and so on
- [ ]     detect whether `==` is declared and emit error

- [ ] support for slice(range) pattern
- [ ] string
- [ ] regular expression
- [ ] support for seq
- [ ] support for Table
- [ ] support for set
- [ ] support for NimNode
- [ ] general variant object

- [ ] check whether exhaustive or not
- [ ] else branch


- [ ] refactoring

- [ ] strict func
- [ ] view types