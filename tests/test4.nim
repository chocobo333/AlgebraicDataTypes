
import algebraicdatas

import unittest

import macros

{.experimental: "caseStmtMacros".}


AlgebraicRef Tree[T]:
    Val(T)
    Node(a: Tree[T], b: Tree[T])

test "variant":
    check declared(Tree)
    let a = Tree[int].Node(Tree.Val(4), Tree.Val(3))

proc `$`*[T](self: Tree[T]): string =
    # case self
    # of Val(n):
    #     $n
    # of Node(a, b):
    #     "Node(" & $a & ", " & $b & )
    ""