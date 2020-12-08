
import unittest

import algebraicdatas


{.experimental: "caseStmtMacros".}

suite "tuple":
    var testTuple = (1, 2, 3)

    test "literal":
        var flag = false
        case testTuple
        of (1, 1, 1):
            flag = false
        of (2, 3, 4):
            flag = false
        of (1, 2, 3):
            flag = true
        of _:
            flag = false
        
        check flag

    test "range literal":
        var flag = false
        case testTuple
        of (int.low..0, int.low..int.high, int.low..int.high):
            flag = false
        of (2..int.high, int.low..int.high, int.low..int.high):
            flag = false
        of (int.low..int.high, int.low..int.high, int.low..2):
            flag = false
        of (int.low..int.high, int.low..int.high, 4..int.high):
            flag = false
        of (int.low..int.high, int.low..int.high, 3):
            flag = true
        of _:
            flag = false

        check flag

    test "variable":
        var flag = false
        case testTuple:
        of (x, x, x):
            flag = false
        of (x, x, y):
            flag = false
        of (x, y, x):
            flag = false
        of (y, x, x):
            flag = false
        of (x, y, z):
            flag = true
        of _:
            flag = false

        check flag

    test "exaustive":
        const flag = compiles:
            var flag = false
            case testTuple
            of (int.low..0, int.low..1, int.low..int.high):
                flag = false
            of (1, int.low..1, int.low..int.high):
                flag = false
            of (2..int.high, int.low..1, int.low..int.high):
                flag = false
            of (int.low..0, 2, int.low..int.high):
                flag = false
            of (1, 2, 3):
                flag = true
            of (2..int.high, 2, int.low..int.high):
                flag = false
            of (int.low..0, 3..int.high, int.low..int.high):
                flag = false
            of (1, 3..int.high, int.low..int.high):
                flag = false
            of (2..int.high, 3..int.high, int.low..int.high):
                flag = false   
            # of (1, 2, int.low..int.high):
            #     flag = false
        
        # check exaustive
        # check (not flag)

    # test "dead code":
    #     const flag = compiles:
    #         case testTuple
    #         of _:
    #             discard
    #         of (a: 1, b: 2, c: 3):
    #             discard
            
    #     check (not flag)           

suite "tuple (Exp)":
    var testTuple = (1, 2, 3)

    test "literal":
        var x = case testTuple
        of (1, 1, 1):
            0
        of (2, 3, 4):
            1
        of (1, 2, 3):
            2
        of _:
            3
        
        check x == 2

    test "range literal":
        var x = case testTuple
        of (int.low..0, int.low..int.high, int.low..int.high):
            0
        of (2..int.high, int.low..int.high, int.low..int.high):
            1
        of (int.low..int.high, int.low..int.high, int.low..2):
            2
        of (int.low..int.high, int.low..int.high, 4..int.high):
            3
        of (int.low..int.high, int.low..int.high, 3):
            4
        of _:
            5

        check x == 4

    test "variable":
        var x = case testTuple
        of (x, x, x):
            0
        of (x, x, y):
            1
        of (x, y, x):
            2
        of (y, x, x):
            3
        of (x, y, z):
            4
        of _:
            5

        check x == 4

    test "exaustive":
        const flag = compiles:
            var x = case testTuple
            of (int.low..0, int.low..1, int.low..int.high):
                0
            of (1, int.low..1, int.low..int.high):
                1
            of (2..int.high, int.low..1, int.low..int.high):
                2
            of (int.low..0, 2, int.low..int.high):
                3
            of (1, 2, 3):
                4
            of (2..int.high, 2, int.low..int.high):
                5
            of (int.low..0, 3..int.high, int.low..int.high):
                6
            of (1, 3..int.high, int.low..int.high):
                7
            of (2..int.high, 3..int.high, int.low..int.high):
                8
            # of (1, 2, int.low..int.high):
            #     flag = false
        
        # check exaustive
        # check (not flag)

    test "dead code":
        const flag = compiles:
            let x = case testTuple:
            of _:
                0
            of (a: 1, b: 2, c: 3):
                1
            
        check (not flag)