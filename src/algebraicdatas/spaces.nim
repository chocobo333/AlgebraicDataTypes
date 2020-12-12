
import strformat
import strutils
import sequtils
import tables
import sugar

import macros
import ast_pattern_matching

import
    utils,
    rangesets,
    contexts


type
    SpaceKind* {.pure.} = enum
        Empty
        Ty
        Constructor
        Int
        Float
        Union
    Space* = object
        typ*: NimNode
        case kind*: SpaceKind
        of Empty:
            nil
        of Ty:
            nil
        of Constructor:
            name*: string
            args*: seq[Space]
        of Int:
            intRanges*: RangeSet[BiggestInt]
        of Float:
            floatRanges*: RangeSet[BiggestFloat]
        of Union:
            sets*: seq[Space]

    SpaceError = object of ValueError

func isEmpty*(self: Space): bool =
    case self.kind
    of SpaceKind.Empty:
        true
    of SpaceKind.Ty:
        false
    of SpaceKind.Constructor:
        self.args.anyIt(it.isEmpty)
    of SpaceKind.Int:
        self.intRanges.len == 0
    of SpaceKind.Float:
        self.floatRanges.len == 0
    of SpaceKind.Union:
        self.sets.allIt(it.isEmpty)

func flatten(self: Space): Space =
    if self.kind != SpaceKind.Union:
        return
    result = self
    var i = 0
    while i < result.sets.len:
        if result.sets[i].isEmpty:
            result.sets.del(i)
            continue
        if result.sets[i].kind == SpaceKind.Union:
            result.sets.add result.sets[i].sets
            result.sets.del(i)
            continue
        inc i

proc Empty*(_: typedesc[Space]): Space =
    Space(kind: SpaceKind.Empty)
proc Ty*(_: typedesc[Space], typ: NimNode): Space =
    Space(kind: SpaceKind.Ty, typ: typ)
proc Constructor*(_: typedesc[Space], typ: NimNode, name: string, args: seq[Space]): Space =
    Space(kind: SpaceKind.Constructor, typ: typ, name: name, args: args)
proc Int*(_: typedesc[Space], typ: NimNode, ranges: Slice[BiggestInt]): Space =
    Space(kind: SpaceKind.Int, typ: typ, intRanges: @[ranges])
proc Float*(_: typedesc[Space], typ: NimNode, ranges: Slice[BiggestFloat]): Space =
    Space(kind: SpaceKind.Float, typ: typ, floatRanges: @[ranges])
proc Union*(_: typedesc[Space], sets: seq[Space]): Space =
    let sets = sets.filterIt(not it.isEmpty)
    if sets.len == 0:
        result = Space.Empty()
    else:
        result = Space(kind: SpaceKind.Union, typ: newNilLit(), sets: sets).flatten()


proc `$`*(self: Space): string =
    case self.kind
    of SpaceKind.Empty:
        fmt"E()"
    of SpaceKind.Ty:
        fmt"T({self.typ.repr})"
    of SpaceKind.Constructor:
        fmt"K({self.name}; {self.args.join("", "")})"
    of SpaceKind.Int:
        fmt"K(int; {self.intRanges})"
    of SpaceKind.Float:
        fmt"K(float; {self.floatRanges})"
    of SpaceKind.Union:
        fmt"U({self.sets.join("" | "")})"

proc decompose*(self: Space): Space =
    case self.kind
    of SpaceKind.Ty:
        self.typ.getTypeImpl.matchAst:
        of nnkSym:
            if self.typ.sameType(bindSym"int"):
                return Space.Int(self.typ, Slice[BiggestInt](a: int.low, b: int.high))
            elif self.typ.sameType(bindSym"int8"):
                return Space.Int(self.typ, Slice[BiggestInt](a: int8.low, b: int8.high))
            elif self.typ.sameType(bindSym"int16"):
                return Space.Int(self.typ, Slice[BiggestInt](a: int16.low, b: int16.high))
            elif self.typ.sameType(bindSym"int32"):
                return Space.Int(self.typ, Slice[BiggestInt](a: int32.low, b: int32.high))
            elif self.typ.sameType(bindSym"int64"):
                return Space.Int(self.typ, Slice[BiggestInt](a: int64.low, b: int64.high))
            raise newException(SpaceError, "notimplemented")
        of nnkTupleConstr:
            return Space.Constructor(self.typ, "untaggedTuple", self.typ.getTypeImpl.mapIt(Space.Ty(it.getTypeInst))) # it.newSpace(ident"_")
        of nnkTupleTy:
            return Space.Constructor(self.typ, "taggedTuple", self.typ.getTypeImpl.mapIt(Space.Ty(it[1].getTypeInst))) # it.newSpace(ident"_")
        of nnkObjectTy:
            let objectInfo = objectContext[self.typ.getSymHash]
            case objectInfo.mode:
            of Wrapped:
                let
                    a = objectInfo.fields
                    args = collect(newSeq):
                        for e in a[0].zip(a[2]):
                            if e[1].len == 1:
                                Space.Constructor(self.typ, e[0].strVal, Space.Ty(e[1][0]).decompose().args)
                            else:
                                Space.Constructor(self.typ, e[0].strVal, @[])
                return Space.Union(args)
                    # a[0].zip(a[2]).mapIt(
                    #     Space.Constructor(self.typ, it[0].strVal, Space.Ty(it[1][0]).decompose().args)
                    # )
            of NoVariant:
                let a = objectContext[self.typ.getSymHash].fields
                return Space.Constructor(self.typ, a[0][0].strVal, a[2][0].mapIt(Space.Ty(it.getTypeInst)))
            else:
                error "notimplemented", self.typ
        else:
            echo self
            echo self.typ.getTypeImpl.treeRepr
            raise newException(SpaceError, "notimplemented")
    else:
        return self

proc simplify(self: Space): Space =
    result = self.flatten()
    if self.isEmpty:
        return Space.Empty()

proc intersect(self, other: Space): Space =
    if self.isEmpty or other.isEmpty:
        return Space.Empty()


proc `\`*(self, other: Space): Space =
    if self.isEmpty:
        return Space.Empty()
    if other.isEmpty:
        return self

    #
    case self.kind
    of SpaceKind.Empty:
        return self
    of SpaceKind.Union:
        return Space.Union(self.sets.mapIt(it\other))
    else:
        discard

    case other.kind
    of SpaceKind.Empty:
        return self
    of SpaceKind.Ty:
        if self.typ.sameType(other.typ):
            return Space.Empty()
        else:
            return self
    of SpaceKind.Constructor:
        case self.kind
        of SpaceKind.Ty:
            return self.decompose() \ other
        of SpaceKind.Constructor:
            if (self.typ.sameType(other.typ) or self.typ.getSymHash == other.typ.getSymHash) and self.name == other.name:
                assert self.args.len == other.args.len
                var args: seq[Space]
                for i in 0..<self.args.len:
                    var tmp = self.args
                    tmp[i] = tmp[i] \ other.args[i]
                    if not tmp[i].isEmpty:
                        args.add Space.Constructor(self.typ, self.name, tmp)
                return Space.Union(
                    args
                    # toSeq(0..<self.args.len).mapIt(
                    #     block:
                    #         var args = self.args
                    #         args[it] = args[it] \ other.args[it]
                    #         Space.Constructor(self.typ, self.name, args)
                    # )
                )
            else:
                return self
        else:
            echo self
            raise newException(SpaceError, "notimplemented")
            # return self
    of SpaceKind.Int:
        case self.kind:
        of SpaceKind.Ty:
            return self.decompose() \ other
        of SpaceKind.Int:
            if self.typ.getTypeImpl.strVal == other.typ.getTypeImpl.strVal:
                return Space(kind: SpaceKind.Int, typ: self.typ, intRanges: self.intRanges \ other.intRanges)
            raise newException(SpaceError, "notimplemented")
        else:
            raise newException(SpaceError, "notimplemented")
    of SpaceKind.Float:
        raise newException(SpaceError, "notimplemented")
    of SpaceKind.Union:
        # result = self
        # for e in other.sets:
        #     result = result \ e
        # return
        return other.sets.foldl(a\b, self)
    raise newException(SpaceError, "notimplemented")