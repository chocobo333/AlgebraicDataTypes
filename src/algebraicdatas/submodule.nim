
import macros


dumpTree:
    type
        ShapeKind {.pure.} = enum
            Square
            Rectangle
        SquareImpl[T: SomeFloat] = (T, )
        RectangleImpl[T: SomeFloat] = object
            w: T
            h: T
        Shape*[T: SomeFloat] = object
            x: T
            y: T
            case kind: ShapeKind
            of ShapeKind.Square:
                SquareField: SquareImpl[T]
            of ShapeKind.Rectangle:
                RectangleField: RectangleImpl[T]

    proc `==`*[T: SomeFloat](self: Shape[T], other: Shape[T]): bool =
        if self.kind != other.kind:
            return false
        return case self.kind
        of ShapeKind.Square:
            self.SquareField == other.SquareField
        of ShapeKind.Rectangle:
            self.RectangleField == other.RectangleField

    proc Square[T](typ: typedesc[Shape], a0: T): Shape[T] =
        Shape[T](kind: ShapeKind.Square, SquareField: (a0, ))
    var
        a = Shape.Square(3.5)

    echo a == a