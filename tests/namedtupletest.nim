
import unittest

import algebraicdatas

block NamedTuple:

    block Int:
        echo "### type: Int ###"
        type IntTuple = tuple
            a: int
            b: int
            c: int

        var intTuple: IntTuple = (a: 1, b: 2, c: 3)

        block Literal:
            var flag: bool = false
            match intTuple:
            of (a: 1, b: 1, c: 1):
                flag = false
            of (a: 1, b: 2, c: 3):
                flag = true
            of _:
                flag = false

            test "literal":
                check flag

        block RangeLiteral:
            var flag: bool = false
            match intTuple:
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

            test "range literal":
                check flag
        
        block Variable:
            var flag: bool = false
            match intTuple:
            of (a: x, b: 2, c: x):
                flag = false
            of (a: x, b: y, c: 2):
                flag = false
            of (a: x, b: 2, c: z):
                flag = true
            of (a: x, b: y, c: z):
                flag = false
            
            test "variable":
                check flag

        block Covertness:
            var flag = false
            match intTuple:
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

        block DeadCode:
            match intTuple:
            of _:
                echo "[OK] dead code"
            # of (a: 1, b: 2, c: 3):
            #     echo "piyo"
