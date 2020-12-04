
import unittest

import algebraicdatas

{.experimental: "caseStmtMacros".}

suite "Pattern Matching":
    test "Discarding":
        let
            a = "a"
            b = match a:
            of _:
                "hello"
            c = match a:
            of "b":
                "hello"
            of _:
                "world"
        check b == "hello"
        check c == "world"
    
    test "Value":
        {.hint: "When you use case statement macro instead of `match` macro with string type, int type or ordered types, the Nim compiler dose not invoke `match` macro but the built-in case statement.".}
        let
            a = 2
            b = match a: # colon is needed on `match` macro
            of 1:
                "One"
            of 2:
                "Two"
            of _:
                "Any number"
        check b == "Two"
    test "Range pattern":
        let
            a = 2
            b = match a:
            of 0:
                "Zero"
            of 1..int.high:
                "Positive"
            of int.low .. -1:
                "Negative"
        check b == "Positive"
    test "Named variable":
        let
            a = (3, 4)
            b = case a
            of (b, _):
                b
        check b == a[0]
    test "Exisiting variable":
        let
            a = (3, 4)
            b = 1
            c = 3
            d = case a
            of (!b, _):
                "a[0] == b"
            of (!c, _):
                "a[0] == c"
            of _:
                "not match"
        check d == "a[0] == c"
    test "Tuple":
        type Color = tuple
            r: uint8
            g: uint8
            b: uint8
            a: uint8
        var
            red: Color = (r: 255'u8, g: 1'u8, b: 2'u8, a: 3'u8)
            a = case red
            of (r: 255, g: _, b, a: _):
                b
        check a == red.b