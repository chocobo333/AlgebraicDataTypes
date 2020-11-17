
import strformat
import sequtils
import tables

import macros
import ast_pattern_matching

import typetraits

func enumerate*[T](s: openArray[T]): auto =
    toSeq(0..<s.len).zip(s)

type
    VariantKind = enum
        NoField
        Tagged
        Untagged
func scanName(name: NimNode): (NimNode, NimNode) =
    name.matchAst:
    of nnkIdent:
        return (name, newEmptyNode())
    of nnkBracketExpr:
        name[0].expectKind(nnkIdent)
        result[0] = name[0]
        result[1] = nnkGenericParams.newNimNode()
        let generics = name[1..^1]
        for e in generics:
            e.matchAst:
            of nnkIdent:
                result[1].add newIdentDefs(e, newEmptyNode())
            of nnkExprColonExpr:
                result[1].add newIdentDefs(e[0], e[1])

func scanFields(body: NimNode): (seq[NimNode], seq[(NimNode, VariantKind, seq[NimNode])]) =
    var
        fields: seq[NimNode]
        kinds: typeof(result[1])
    for field in body:
        field.matchAst:
        of nnkCall(`field`@nnkIdent, nnkStmtList(`typ`@nnkIdent)):
            fields.add newIdentDefs(field, typ)
        of nnkObjConstr:
            field[0].expectKind(nnkIdent)
            var kind: (NimNode, VariantKind, seq[NimNode]) = (field[0], Tagged, @[])
            let
                params = field[1..^1]
            for param in params:
                param.expectKind(nnkExprColonExpr)
                kind[2].add newIdentDefs(param[0], param[1])
            kinds.add kind
        of nnkCall:
            field[0].expectKind(nnkIdent)
            var kind: (NimNode, VariantKind, seq[NimNode]) = (field[0], Untagged, @[])
            let
                params = field[1..^1]
            for i, param in params:
                param.expectKind(nnkIdent)
                kind[2].add param
            kinds.add kind
        of nnkIdent:
            var kind: (NimNode, VariantKind, seq[NimNode]) = (field, NoField, @[])
            kinds.add kind
    (fields, kinds)

proc makeType(name: NimNode, generics: NimNode, fields: seq[NimNode], kinds: seq[(NimNode, VariantKind, seq[NimNode])]): NimNode =
    name.expectKind(nnkIdent)
    result = nnkTypeSection.newNimNode()
    proc generalize(id: NimNode): NimNode =
        if generics.kind == nnkEmpty:
            return id
        # id, @[T1: SomeInteger, T2: SomeFloat] -> id[T1, T2]
        nnkBracketExpr.newTree(id).add(
            generics.mapIt(
                block:
                    it.expectKind(nnkIdentDefs);
                    it[0]
            )
        )
    let
        genericParams = generics.mapIt(it)
        kindId = ident(fmt"{name}kind")
        kind = newEnum(kindId, kinds.mapIt(it[0]), false, true)[0]
        impls = kinds.filterIt(it[1] != NoField).mapIt(
            nnkTypeDef.newTree(
                ident(fmt"{it[0]}Impl"),
                generics,
                case it[1]
                of Tagged:
                    nnkObjectTy.newTree(
                        newEmptyNode(),
                        newEmptyNode(),
                        nnkRecList.newTree(
                            it[2]
                        )
                    )
                of Untagged:
                    nnkTupleConstr.newTree(
                        it[2]
                    )
                of NoField:
                    newEmptyNode()
            )
        )
        variant = nnkTypeDef.newTree(
            postfix(name, "*"),
            generics,
            nnkObjectTy.newTree(
                newEmptyNode(),
                newEmptyNode(),
                nnkRecList.newTree(fields).add(
                    nnkRecCase.newTree(
                        newIdentDefs(ident"kind", kindId)
                    ).add kinds.mapIt(
                        nnkOfBranch.newTree(
                            newDotExpr(kindId, it[0]),
                            nnkRecList.newTree(
                                case it[1]
                                of NoField:
                                    newNilLit()
                                else:
                                    newIdentDefs(
                                        ident(fmt"{it[0]}Field"),
                                        ident(fmt"{it[0]}Impl").generalize()
                                    )
                            )
                        )
                    )
                )
            )
        )
    result.add kind
    result.add impls
    result.add variant

func makeConstructor(name: NimNode, generics: NimNode, kinds: seq[(NimNode, VariantKind, seq[NimNode])]): seq[NimNode] =
    proc generalize(id: NimNode): NimNode =
        if generics.kind == nnkEmpty:
            return id
        # id, @[T1: SomeInteger, T2: SomeFloat] -> id[T1, T2]
        nnkBracketExpr.newTree(id).add(
            generics.mapIt(
                block:
                    it.expectKind(nnkIdentDefs);
                    it[0]
            )
        )
    let
        kindId = ident(fmt"{name.strVal}Kind")
    kinds.mapIt(
        nnkProcDef.newTree(
            it[0],
            newEmptyNode(),
            generics,
            nnkFormalParams.newTree(
                name.generalize(),
                newIdentDefs(
                    ident"typ",
                    nnkBracketExpr.newTree(
                        ident"typedesc",
                        name.generalize()
                    )
                )
            ).add(
                case it[1]
                of Untagged:
                    it[2].enumerate.mapIt newIdentDefs(ident(fmt"a{it[0]}"), it[1])
                else:
                    it[2]
            ),
            newEmptyNode(),
            newEmptyNode(),
            newStmtList(
                nnkObjConstr.newTree(
                    name.generalize(),
                    newColonExpr(
                        ident"kind",
                        newDotExpr(
                            kindId,
                            ident(it[0].strVal),
                        )
                    )
                ).add(
                    case it[1]
                    of Tagged:
                        @[newColonExpr(
                            ident(fmt"{it[0].strVal}Field"),
                            nnkObjConstr.newTree(
                                ident(fmt"{it[0].strVal}Impl").generalize()
                            ).add(
                                it[2].mapIt(
                                    newColonExpr(it[0], it[0])
                                )
                            )
                        )]
                    of Untagged:
                        @[newColonExpr(
                            ident(fmt"{it[0].strVal}Field"),
                            nnkTupleConstr.newTree(
                                it[2].enumerate.mapIt ident(fmt"a{it[0]}")
                            )
                        )]
                    of NoField:
                        @[]
                )
            )
        )
    )

macro Algebraic*(name: untyped, body: untyped): untyped =
    var
        (name, generics) = scanName(name)
        (fields, kinds) = scanFields(body)
    result = newStmtList()
    result.add makeType(name, generics, fields, kinds)
    result.add makeConstructor(name, generics, kinds)

