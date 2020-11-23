# AlgebraicDataTypes
This package literally provides algebraic data types(ADT) and performs pattern matching for them. It's inspried by some packages: [ast-pattern-mathing](https://github.com/krux02/ast-pattern-matching) and [gara](https://github.com/alehander92/gara), and [`enum`](https://doc.rust-lang.org/book/ch06-01-defining-an-enum.html) and [pattern matching](https://doc.rust-lang.org/book/ch18-00-patterns.html) in the [Rust](https://www.rust-lang.org/) language.

it provids:
* `` `?=` ``  
    It can be used like Rust's if let syntax.
    ```nim
    let a = Option.Some(3)
    if Some(val) ?= a:
        echo val #> 3
    if None ?= a:
        echo "none"
    ```
* `match`  
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
        of None:
            0
    echo b #> 3
    ```

## Features
* [ADT](#adt)
  * [Defining an ADT](#defining-an-adt)
* [Pattern matching](#pattern-mathing)
  * [value](#value)
##  ADT

### Defining an ADT
You can define an ADT by using a macro called `Algebraic`. It looks like this:
```nim
Algebraic Option[T]:
    Some(T)
    None
```
## Pattern mathing
### value
### existing variable
```nim
let
    a = 3
    b = (3, 4)
case b
of (a, _):
    echo "b[0] == a"
```
### discarding
```nim
case a
of _:
    echo "hello"
```
expands to:
```nim
if true:
    echo "hello"
```



# TODO
- [ ] smarter error infomation: tuple length check, wheter ofBranch is, wheter discard pattern is,  and so on
- [ ]     detect whether `==` is declared and emit error

- [ ] support for seq
- [ ] support for Table
- [ ] support for set
- [ ] support for NimNode

- [ ] check whether exhaustive or not
- [ ] else branch


- [ ] refactoring

- [ ] strict func
- [ ] view types