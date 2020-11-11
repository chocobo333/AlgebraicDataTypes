
import macros


macro Algebraic(name: untyped, body: untyped): untyped =
    echo body.treeRepr

Algebraic Option[T]:
    Some(T)
    None