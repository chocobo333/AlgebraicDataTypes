
import algebraicdatas

import unittest

import macros

{.experimental: "caseStmtMacros".}


AlgebraicRef Tree[T]:
    Val(T)
    Node(a: Tree[T], b: Tree[T])

proc `$`*[T](self: Tree[T]): string =
    discard match self[]:
    of Val(n):
        $n
    of Node(a, b):
        "Node(" & $a & ", " & $b & ")"
    match self:
    of Val(n):
        $n
    of Node(a, b):
        "Node(" & $a & ", " & $b & ")"

test "variant":
    check declared(Tree)
    let a = Tree[int].Node(Tree.Val(4), Tree.Val(3))
    echo `$`[int](a)
