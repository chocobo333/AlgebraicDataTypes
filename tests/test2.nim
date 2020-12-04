
import unittest
import sequtils

import algebraicdatas

import test1

test "match for int":
    let
        a = 2
        b = toSeq(countup(1, 3)).mapIt(
            block:
                match it: # needs wrapping with block statement, parhaps parsing of `of branch` is weak
                of 1:
                    "first"
                of !a:
                    "equals to a"
                of _:
                    "otherwise"
        )
    check b == @["first", "equals to a", "otherwise"]

{.experimental: "caseStmtMacros".}

test "match for untagged tuple":
    let a = @[(2, 2), (3, 4), (1, 1)]

    let
        b = 2
        c = a.mapIt(
            case it: # needs no block statement for case statement
            of (!b, !b): # reckoned as (2, 2)
                b
            of (3, second):
                second
            of _:
                3
        )
    check c == @[2, 4, 3]
    check (a@_, a) ?= a[2]

test "match for tagged tuple":
    let a = (a: 3, b: (3, 4))
    check (if (a: 3, b: second) ?= a:
        second
    else:
        (0, 0)) == (3, 4)
    
    check(
        `==`(
            case a
            of (a, b: (a, _)):
                a
            of _:
                0,
            3
        )
    )

test "match for variant":
    let
        a = Option.Some(3)
        b = case a # The same goes for `match` macro
        of Some(val):
            val
        of _:
            0
    check b == 3