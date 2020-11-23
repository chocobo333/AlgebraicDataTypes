
import unittest

import algebraicdatas


Algebraic Color:
    Rgb(int8, int8, int8)
    Name(string)
Algebraic Shape[T: SomeFloat]:
    Square(T)
    Rectangle(w: T, h: T)
    x: T
    y: T
    color: Color
Algebraic Option[T]:
    Some(T)
    None
Algebraic Result[T, E]:
    Ok(T)
    Err(E)
Algebraic Number:
    nbits: int
    Int(val: int)
    Float(val: float)

export
    Some

test "variant":
    check declared(Color)
    check declared(Shape)
    check declared(Option)
    check declared(Result)
    check declared(Number)