
import unittest

import algebraicdatas


{.experimental: "caseStmtMacros".}

suite "named tuple":
    type IntTuple = tuple
        a: int
        b: int
        c: int

    var intTuple: IntTuple = (a: 1, b: 2, c: 3)

    test "literal":
        var flag: bool = false
        case intTuple
        of (a: 1, b: 1, c: 1):
            flag = false
        of (a: 1, b: 2, c: 3):
            flag = true
        of _:
            flag = false

        check flag

    test "range literal":
        var flag: bool = false
        case intTuple
        of (a: int.low..0, b: int.low..int.high, c: int.low..int.high):
            flag = false
        of (a: 2..int.high, b: int.low..int.high, c: int.low..int.high):
            flag = false
        of (a: int.low..int.high, b: int.low..int.high, c: int.low..2):
            flag = false
        of (a: int.low..int.high, b: int.low..int.high, c: 4..int.high):
            flag = false
        of (a: int.low..int.high, b: int.low..int.high, c: 3):
            flag = true
        of _:
            flag = false

        check flag
    
    test "variable":
        var flag: bool = false
        case intTuple
        of (a: x, b: 2, c: x):
            flag = false
        of (a: x, b: y, c: 2):
            flag = false
        of (a: x, b: 2, c: z):
            flag = true
        of (a: x, b: y, c: z):
            flag = false
        
        check flag

    test "exaustive":
        const flag = compiles:
            var flag = false
            case intTuple
            of (a: int.low..0, b: int.low..1, c: int.low..int.high):
                flag = false
            of (a: 1, b: int.low..1, c: int.low..int.high):
                flag = false
            of (a: 2..int.high, b: int.low..1, c: int.low..int.high):
                flag = false
            of (a: int.low..0, b: 2, c: int.low..int.high):
                flag = false
            of (a: 1, b: 2, c: 3):
                flag = true
            of (a: 2..int.high, b: 2, c: int.low..int.high):
                flag = false
            of (a: int.low..0, b: 3..int.high, c: int.low..int.high):
                flag = false
            of (a: 1, b: 3..int.high, c: int.low..int.high):
                flag = false
            of (a: 2..int.high, b: 3..int.high, c: int.low..int.high):
                flag = false   
            # of (a: 1, b: 2, c: int.low..int.high):
            #     flag = false
        
        # check exaustive
        # check (not flag)

    # test "dead code":
    #     const flag = compiles:
    #         case intTuple
    #         of _:
    #             discard
    #         of (a: 1, b: 2, c: 3):
    #             discard
            
    #     check (not flag)

suite "Int(Exp)":
    type IntTuple = tuple
        a: int
        b: int
        c: int

    var intTuple: IntTuple = (a: 1, b: 2, c: 3)

    test "literal":
        let
            x = case intTuple
            of (a: 1, b: 1, c: 1):
                0
            of (a: 1, b: 2, c: 3):
                1
            of _:
                2

        check x == 1

    test "range literal":
        let
            x = case intTuple
            of (a: int.low..0, b: int.low..int.high, c: int.low..int.high):
                0
            of (a: 2..int.high, b: int.low..int.high, c: int.low..int.high):
                1
            of (a: int.low..int.high, b: int.low..int.high, c: int.low..2):
                2
            of (a: int.low..int.high, b: int.low..int.high, c: 4..int.high):
                3
            of (a: int.low..int.high, b: int.low..int.high, c: 3):
                4
            of _:
                5

        check x == 4
    
    # test "variable":
    #     var
    #         x = case IntTuple
    #         of (a: x, b: 2, c: z):
    #             0
    #         of (a: x, b: y, c: 2):
    #             1
    #         of (a: x, b: 2, c: z):
    #             2
    #         of (a: x, b: y, c: z):
    #             3
    #         of _:
    #             4
        
    #     check x = 2

    test "exaustive":
        const flag = compiles:
            let x = case intTuple:
            of (a: int.low..0, b: int.low..1, c: int.low..int.high):
                0
            of (a: 1, b: int.low..1, c: int.low..int.high):
                2
            of (a: 2..int.high, b: int.low..1, c: int.low..int.high):
                3
            of (a: int.low..0, b: 2, c: int.low..int.high):
                4
            of (a: 1, b: 2, c: 3):
                5
            of (a: 2..int.high, b: 2, c: int.low..int.high):
                6
            of (a: int.low..0, b: 3..int.high, c: int.low..int.high):
                7
            of (a: 1, b: 3..int.high, c: int.low..int.high):
                8
            of (a: 2..int.high, b: 3..int.high, c: int.low..int.high):
                9   
            # of (a: 1, b: 2, c: int.low..int.high):
            #     10
        
        # check exaustive
        # check (not flag)

    # test "dead code":
    #     const flag = compiles:
    #         let x = case intTuple:
    #         of _:
    #             0
    #         of (a: 1, b: 2, c: 3):
    #             1
            
    #     check (not flag)