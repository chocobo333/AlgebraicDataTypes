
import strformat
import strutils
import sequtils
import tables
import options
import sugar

import macros
import macroutils except Slice, Lit
import ast_pattern_matching
import hmisc/hexceptions

import algebraicdatas/[
    utils,
    contexts,
    spaces
]


func enumerate*[T](s: openArray[T]): auto =
    toSeq(0..<s.len).zip(s)
func enumerate*(s: NimNode): auto =
    toSeq(0..<s.len).zip(toSeq[s.children])

type
    VariantKind = enum
        NoField
        Tagged
        Untagged
    MatchError = object of ValueError

template variant {.pragma.}

func defaultDiscriminator: NimNode = ident"kind"
func implize(n: NimNode): NimNode =
    ident(":" & n.strVal)
func fieldize(n: NimNode): NimNode =
    ident(":" & n.strVal & "Field")
func kindize(n: NimNode): NimNode =
    ident(":" & n.strVal & "Kind")
func argize(n: int): NimNode =
    ident("arg" & $n)
func newize(n: NimNode): NimNode =
    ident("new" & n.strVal)

proc VariantImpl(typ: NimNode, kind: NimNode, getter: NimNode, children: NimNode): NimNode =
    echo 3
    newStmtList()
macro Variant*(typ: typed, kind: untyped, getter: typed, children: untyped): untyped =
    kind.expectKind({nnkIdent, nnkSym, nnkStrLit})
    children.expectKind({nnkIdent, nnkSym, nnkStrLit})
    VariantImpl(typ, kind, getter, children)

macro Variant*(typ: typed, kind: untyped, getter: typed): untyped =
    kind.expectKind({nnkIdent, nnkSym, nnkStrLit})
    VariantImpl(typ, kind, getter, newEmptyNode())

macro Variant*(typ: typed, kind: untyped): untyped =
    kind.expectKind({nnkIdent, nnkSym, nnkStrLit})
    VariantImpl(typ, kind, newEmptyNode(), newEmptyNode())
macro Variant*(typ: typed): untyped =
    VariantImpl(typ, newEmptyNode(), newEmptyNode(), newEmptyNode())

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

func generalize(id: NimNode, generics: NimNode): NimNode =
    generics.expectKind({nnkEmpty, nnkGenericParams})
    if generics.kind == nnkEmpty:
        return id
    generics.expectKind(nnkGenericParams)
    # id, @[T1: SomeInteger, T2: SomeFloat] -> id[T1, T2]
    nnkBracketExpr.newTree(id).add(
        generics.mapIt(
            block:
                it.expectKind(nnkIdentDefs);
                it[0]
        )
    )

func makeType(name: NimNode, generics: NimNode, fields: seq[NimNode], kinds: seq[(NimNode, VariantKind, seq[NimNode])], refer: bool = false): NimNode =
    name.expectKind(nnkIdent)
    result = nnkTypeSection.newNimNode()
    let
        genericParams = generics.mapIt(it)
        kindId = name.kindize
        kind = newEnum(kindId, kinds.mapIt(it[0]), true, true)[0]
        impls = kinds.filterIt(it[1] != NoField).mapIt(
            nnkTypeDef.newTree(
                postfix(it[0].implize, "*"),
                generics,
                case it[1]
                of Tagged:
                    nnkTupleTy.newTree(
                        it[2].mapIt(newIdentDefs(it[0], it[1]))
                    )
                of Untagged:
                    nnkTupleConstr.newTree(
                        it[2]
                    )
                of NoField:
                    newEmptyNode()
            )
        )
        typ = nnkObjectTy.newTree(
                newEmptyNode(),
                newEmptyNode(),
                nnkRecList.newTree(fields.mapIt(newIdentDefs(postfix(it[0], "*"), it[1]))).add(
                    nnkRecCase.newTree(
                        newIdentDefs(postfix(defaultDiscriminator(), "*"), kindId)
                    ).add kinds.mapIt(
                        nnkOfBranch.newTree(
                            newDotExpr(kindId, it[0]),
                            nnkRecList.newTree(
                                case it[1]
                                of NoField:
                                    newNilLit()
                                else:
                                    newIdentDefs(
                                        postfix(it[0].fieldize, "*"),
                                        it[0].implize.generalize(generics)
                                    )
                            )
                        )
                    )
                )
            )
        variant = nnkTypeDef.newTree(
            nnkPragmaExpr.newTree(
                postfix(name, "*"),
                nnkPragma.newTree(
                    bindSym"variant",
                )
            ),
            generics,
            if refer:
                nnkRefTy.newTree(typ)
            else:
                typ
        )
    result.add kind
    result.add impls
    result.add variant

macro makeTuple(values: varargs[untyped]): untyped =
    nnkTupleConstr.newTree(values)

func makeVariantObjConstr(name: NimNode, generics: NimNode, kind: NimNode): NimNode =
    name.expectKind(nnkIdent)
    nnkObjConstr.newTree(
        name.generalize(generics),
        newColonExpr(
            defaultDiscriminator(),
            kind
        )
    )
func makeProc(name, generics, formalParams, body: NimNode): NimNode =
    nnkProcDef.newTree(
        postfix(name, "*"),
        newEmptyNode(),
        generics,
        formalParams,
        newEmptyNode(),
        newEmptyNode(),
        body
    )
func makeConstructor(name: NimNode, generics: NimNode, fields: seq[NimNode], kinds: seq[(NimNode, VariantKind, seq[NimNode])]): seq[NimNode] =
    func makeParameters(fields: seq[NimNode], kind: VariantKind): seq[NimNode] =
        case kind
        of Untagged:
            fields.enumerate.mapIt newIdentDefs(it[0].argize, it[1])
        else:
            fields
    func makeObjConstr(cons: NimNode, name: NimNode, generics: NimNode, fields: seq[NimNode], kindId: NimNode, kind: VariantKind): NimNode =
        case kind
        of Tagged:
            makeVariantObjConstr(name, generics, newDotExpr(kindId, cons)).add(
                newColonExpr(
                    cons.fieldize,
                    nnkTupleConstr.newTree(
                        fields.mapIt(newColonExpr(it[0], it[0]))
                    )
                )
            )
        of Untagged:
            makeVariantObjConstr(name, generics, newDotExpr(kindId, cons)).add(
                newColonExpr(
                    cons.fieldize,
                    nnkTupleConstr.newTree(
                        fields.enumerate.mapIt it[0].argize
                    )
                )
            )
        of NoField:
            makeVariantObjConstr(name, generics, newDotExpr(kindId, cons))
    let
        kindId = name.kindize
        val = ident":val"
    result.add makeProc(
        name.newize,
        generics,
        nnkFormalParams.newTree(
            name.generalize(generics)
        ).add(fields),
        newStmtList(
            nnkObjConstr.newTree(
                name.generalize(generics),
            ).add fields.mapIt(newColonExpr(it[0], it[0]))
        )
    )
    result.add kinds.mapIt(
        makeProc(
            it[0],
            generics,
            nnkFormalParams.newTree(
                name.generalize(generics),
                newIdentDefs(
                    val,
                    name.generalize(generics)
                )
            ).add(it[2].makeParameters(it[1])),
            newStmtList(
                makeObjConstr(it[0], name, generics, it[2], kindId, it[1]).add(
                    fields.mapIt(newColonExpr(it[0], DotExpr(val, it[0])))
                )
            )
        )
    )
    result.add kinds.mapIt(
        makeProc(
            it[0],
            generics,
            nnkFormalParams.newTree(
                name.generalize(generics),
                newIdentDefs(
                    ident"_",
                    nnkBracketExpr.newTree(
                        ident"typedesc",
                        name.generalize(generics)
                    )
                )
            ).add(it[2].makeParameters(it[1])),
            newStmtList(makeObjConstr(it[0], name, generics, it[2], kindId, it[1]))
        )
    )

macro Algebraic*(name: untyped, body: untyped): untyped =
    var
        (name, generics) = scanName(name)
        (fields, kinds) = scanFields(body)
    result = newStmtList()
    result.add makeType(name, generics, fields, kinds)
    result.add makeConstructor(name, generics, fields, kinds)
macro AlgebraicRef*(name: untyped, body: untyped): untyped =
    var
        (name, generics) = scanName(name)
        (fields, kinds) = scanFields(body)
    result = newStmtList()
    result.add makeType(name, generics, fields, kinds, refer = true)
    result.add makeConstructor(name, generics, fields, kinds)

template `==?`(a, b: untyped): untyped =
    when compiles(a.contains(b)):
        a.contains(b)
    elif compiles(a == b):
        a == b
    else:
        bind error2
        static:
            const
                s1 = $typeof(a)
                s2 = $typeof(b)
            error2(
                astToStr(a) & " is of type " & s1 & "\n" &  "selector is of type " & s2 & "\n" & "`==`(" & s1 & ", " & s2 & ") and `contains`(" & s1 & ", " & s2 & ") is not declared",
                a
            )
        false
    
template `:=`(a: untyped, b: typed): untyped =
    when declaredInScope(a):
        a = b
    else:
        let a = b
    true

template `:==`(a: untyped, b: typed): untyped =
    when declaredInScope(a):
        bind `==?`
        a ==? b
    else:
        bind `:=`
        a := b

template matchDiscardingPattern(selector: NimNode, pattern: NimNode, inductive: untyped): untyped =
    pattern.matchAst:
    # discarding the value
    # _
    of nnkIdent(strVal = "_"):
        return newLit(true)
    # capturing or comparing to an already captured variable
    # name
    of `p`@nnkIdent:
        return Infix(bindSym":==", p, selector)
    # captruing, never comparing
    # name@_
    of nnkInfix(ident"@", `id`@nnkIdent, nnkIdent(strVal = "_")):
        return Infix(bindSym":=", id, selector)
    # mathing and capturing
    # name@pat
    of nnkInfix(ident"@", `id`@nnkIdent, `p`@_):
        return inductive and Infix(bindSym":=", id, selector)
    of nnkPrefix(ident"!", `id`@nnkIdent):
        return Infix(bindSym"==?", id, selector)
    else:
        discard

macro `?=`*(pattern: untyped, selector: AtomType|string): untyped {.discardable.} =
    func impl(selector: NimNode, pattern: NimNode): NimNode =
        selector.matchDiscardingPattern(pattern, impl(selector, pattern))
        pattern.matchAst:
        # match with literals: strict pattern
        # such as 3, 'a' or "abc"
        of `p`@nnkLiterals:
            return Infix(bindSym"==?", p, selector)
        # expression pattern
        of nnkPar(`p`@_):
            return Infix(bindSym"==?", p, selector)
        # range pattern
        of `p`@nnkInfix(ident"..", `a`@_, `b`@_):
            return Call("contains", p, selector)
        else:
            error "invlid pattern", pattern
    selector.impl(pattern)

func scanTupleInfo(selector: NimNode): (NimNodeKind, int, seq[string]) =
    let a = selector.getTypeImpl
    if a.kind == nnkTupleTy:
        (a.kind, a.len, a.mapIt(it[0].strVal))
    elif a.kind == nnkTupleConstr:
        (a.kind, a.len, @[])
    else:
        # TODO:
        raise newException(MatchError, "Unexpected Error")

proc mathcTupleConstr(selector: NimNode, pattern: NimNode, tupleLen: int): NimNode =
    selector.matchDiscardingPattern(pattern, mathcTupleConstr(selector, p, tupleLen))
    pattern.matchAst:
    # (pat0, pat1)
    of `p`@nnkPar:
        # TODO: use exactly match now
        #       support shorter pattern
        p.expectLen(tupleLen)
        result = p.enumerate.mapIt(
            Infix("?=", it[1], selector.newIndex(it[0]))
        ).foldl(a and b)
    else:
        error "invalid pattern", pattern

func matchTupleField(selector: NimNode, pattern: NimNode, tupleFields: seq[string], usedFields: var seq[string]): NimNode =
    pattern.matchAst:
    of nnkExprColonExpr(`field`@nnkIdent, `p`@_):
        if field.strVal notin tupleFields:
            error "undeclared field: " & field.strVal & "notin " & $tupleFields, field
        if field.strVal in usedFields:
            error "this field has already appeared in patten: " & field.strVal, field
        # if (p.kind == nnkIdent and p.strVal == field.strVal):
        p.matchAst:
        of nnkIdent(strVal = field.strVal):
            hint &"You can simply use the pattern `{p.strVal}` instead of `{p.strVal}: {p.strVal}` if you don't want to compare it with an existing variable", pattern
        of nnkInfix(ident"@", `p`@nnkIdent(strVal = field.strVal), nnkIdent(strVal = "_")):
            hint &"You can simply use the pattern `{p.strVal}` instead of `{p.strVal}: {p.strVal}@_` if you don't want to compare it with an existing variable", pattern
        else:
            discard
        usedFields.add field.strVal
        return Infix("?=", p, newDotExpr(selector, field))
    of `field`@nnkIdent:
        if field.strVal notin tupleFields:
            error(
                tupleFields.filterIt(it notin usedFields).mapIt(
                    &"You can use the pattern `{it}: subpattern` or `{it}`."
                ).join("\n") & &"\nundeclared field: {field.strVal}",
                field
            )
        if field.strVal in usedFields:
            error "this field has already appeared in patten: " & field.strVal, field
        usedFields.add field.strVal
        return Infix(bindSym":=", field, newDotExpr(selector, field))
    else:
        error(
                tupleFields.filterIt(it notin usedFields).mapIt(
                    &"You can use the pattern `{it}: subpattern` or `{it}`."
                ).join("\n"), pattern
            )
        error "invalid pattern", pattern

func matchTupleTy(selector: NimNode, pattern: NimNode, tupleFields: seq[string]): NimNode =
    selector.matchDiscardingPattern(pattern, matchTupleTy(selector, pattern, tupleFields))
    pattern.matchAst:
    of `p`@nnkPar:
        var usedFields: seq[string]
        result = p.mapIt(
            selector.matchTupleField(it, tupleFields, usedFields)
        ).foldl(a and b)
    else:
        error "invalid pattern", pattern

macro `?=`*(pattern: untyped, selector: tuple): untyped {.discardable.} =
    proc impl(selector: NimNode, pattern: NimNode): NimNode =
        let (tupleKind, tupleLen, tupleFields) = scanTupleInfo(selector)
        case tupleKind:
        # (val0, val1)
        of nnkTupleConstr:
            result = selector.mathcTupleConstr(pattern, tupleLen)
        # (tag0: val0, tag1: val1)
        of nnkTupleTy:
            result = selector.matchTupleTy(pattern, tupleFields)
        else:
            # TODO:
            error "unreachable", selector
    selector.impl(pattern)

func getTypeSym*(n: NimNode): NimNode =
    n.getTypeInst.matchAst:
    of `t`@nnkSym:
        result = t
    of `t`@nnkBracketExpr:
        result = t[0]
    else:
        error "notimplemented", n

func getTypeImpl2*(n: NimNode): NimNode =
    result = n.getTypeInst
    result = if result.kind == nnkSym:
        result.getImpl
    else:
        result[0].getImpl
    while true:
        result.matchAst:
        of nnkTypeDef(nnkSym, nnkEmpty, `n`@nnkSym): # that is, alias
            result = n.getImpl
        of nnkTypeDef(nnkSym, nnkEmpty, nnkDistinctTy(`n`@nnkSym)):
            result = n.getImpl
        of nnkTypeDef(nnkSym, nnkEmpty, nnkRefTy(`n`@nnkSym)):
            result = n.getImpl
        else:
            return

func hasVariantPragma*(n: NimNode): bool =
    template searchPragma(pragma: typed, variant: typed): untyped =
        for p in pragma:
            if (p.kind == nnkSym and p == variant) or
                    (p.kind in {nnkExprColonExpr, nnkCall, nnkCallStrLit} and p.len > 0 and p[0].kind == nnkSym and p[0] == variant):
                return true
    let variant = bindSym"variant"
    var tmp = n.getTypeInst
    tmp = if tmp.kind == nnkSym:
        tmp.getImpl
    else:
        tmp[0].getImpl
    while true:
        tmp.matchAst:
        of nnkTypeDef(nnkSym, nnkEmpty, `n`@nnkSym):
            tmp = n.getImpl
        of nnkTypeDef(nnkSym, nnkGenericParams, `n`@nnkBracketExpr):
            tmp = n[0].getImpl
        of nnkTypeDef(nnkSym, nnkEmpty, nnkDistinctTy(`n`@nnkSym)):
            tmp = n.getImpl
        of nnkTypeDef(nnkSym, nnkGenericParams, nnkDistinctTy(`n`@nnkBracketExpr)):
            tmp = n[0].getImpl
        of nnkTypeDef(nnkSym, nnkEmpty, nnkRefTy(`n`@nnkSym)):
            tmp = n.getImpl
        of nnkTypeDef(nnkSym, nnkGenericParams, nnkRefTy(`n`@nnkBracketExpr)):
            tmp = n[0].getImpl
        of nnkTypeDef(nnkPragmaExpr(nnkSym, `pragma`@nnkPragma), nnkEmpty, `n`@nnkSym):
            searchPragma(pragma, variant)
            tmp = n.getImpl
        of nnkTypeDef(nnkPragmaExpr(nnkSym, `pragma`@nnkPragma), nnkGenericParams, `n`@nnkBracketExpr):
            searchPragma(pragma, variant)
            tmp = n[0].getImpl
        of nnkTypeDef(nnkPragmaExpr(nnkSym, `pragma`@nnkPragma), nnkEmpty, nnkDistinctTy(`n`@nnkSym)):
            searchPragma(pragma, variant)
            tmp = n.getImpl
        of nnkTypeDef(nnkPragmaExpr(nnkSym, `pragma`@nnkPragma), nnkBracketExpr, nnkDistinctTy(`n`@nnkBracketExpr)):
            searchPragma(pragma, variant)
            tmp = n[0].getImpl
        of nnkTypeDef(nnkPragmaExpr(nnkSym, `pragma`@nnkPragma), nnkEmpty, nnkRefTy(`n`@nnkSym)):
            searchPragma(pragma, variant)
            tmp = n.getImpl
        of nnkTypeDef(nnkPragmaExpr(nnkSym, `pragma`@nnkPragma), nnkGenericParams, nnkRefTy(`n`@nnkBracketExpr)):
            searchPragma(pragma, variant)
            tmp = n[0].getImpl
        of nnkTypeDef(nnkPragmaExpr(nnkSym, `pragma`@nnkPragma), nnkGenericParams, nnkRefTy({nnkObjectTy})):
            searchPragma(pragma, variant)
            return false
        of nnkTypeDef(nnkPragmaExpr(nnkSym, `pragma`@nnkPragma), {nnkEmpty, nnkGenericParams}, {nnkObjectTy}):
            searchPragma(pragma, variant)
            return false
        else:
            return false

func st2ts2[T, U](a: seq[(T, U)]): (seq[T], seq[U]) =
    ## converts Seq of Tuple to Tuple of Seq
    (a.mapIt(it[0]), a.mapIt(it[1]))
func st2ts3[T, U, V](a: seq[(T, U, V)]): (seq[T], seq[U], seq[V]) =
    ## converts Seq of Tuple to Tuple of Seq
    (a.mapIt(it[0]), a.mapIt(it[1]), a.mapIt(it[2]))

func getEnumFieldAndIntValue(enumSym: NimNode): seq[(NimNode, BiggestInt)] =
    enumSym.expectKind(nnkSym)
    let enumTy = enumSym.getTypeImpl2[2]
    var i: BiggestInt = 0;
    for e in enumTy[1..^1]:
        e.matchAst:
        of nnkSym:
            result.add (e, i)
            inc i
        of nnkEnumFieldDef(`e`@nnkSym, `j`@nnkIntLit):
            result.add (e, j.intVal)
            i = j.intVal + 1
        else:
            error "unreachable", e

func getFieldsFromRecList(reclist: NimNode): (seq[NimNode], seq[NimNode]) =
    reclist.expectKind(nnkRecList)
    reclist.mapIt((
        case it.kind
        of nnkIdentDefs:
            (it[0], it[1])
        of nnkRecCase:
            (it[0][0], it[0][1])
        else:
            error "unreachable", it
            (newEmptyNode(), newEmptyNode())
    )).st2ts2

func getFieldsFromOfBranch(branch: NimNode): (BiggestInt, seq[NimNode], seq[NimNode]) =
    branch.expectKind({nnkOfBranch, nnkElse})
    branch.matchAst:
    of nnkOfBranch(`i`@nnkIntLit, `reclist`@nnkRecList):
        let tmp = reclist.getFieldsFromRecList
        return (i.intVal, tmp[0], tmp[1])
    of nnkElse(`reclist`@nnkRecList):
        let tmp = reclist.getFieldsFromRecList
        return (BiggestInt -1, tmp[0], tmp[1])
    else:
        error "unreachable", branch

proc getRecList(selector: NimNode): NimNode =
    let
        tmp = selector.getTypeImpl
    result = if tmp.kind == nnkRefTy: tmp[0].getTypeImpl[2] else: tmp[2]
    result.expectKind nnkRecList
proc getRecListFields(selector: NimNode): (seq[NimNode], seq[seq[NimNode]], seq[seq[NimNode]]) =
    let
        reclist = selector.getRecList
        typ = selector.getTypeSym
        tmp = reclist.getFieldsFromRecList
    (@[typ], @[tmp[0]], @[tmp[1]])
proc getRecCaseFields(selector: NimNode, kind: NimNode): (seq[NimNode], seq[seq[NimNode]], seq[seq[NimNode]]) =
    func impl(reccase: NimNode): auto =
        reccase.expectKind(nnkRecCase)
        reccase[1..^1].mapIt(
            it.getFieldsFromOfBranch()
        )
    let
        reclist = selector.getRecList
    for e in reclist:
        if e.kind == nnkRecCase:
            e[0].matchAst:
            of  nnkIdentDefs(nnkSym(strVal = kind.strVal), `sym`@nnkSym, nnkEmpty):
                let
                    kinds = getEnumFieldAndIntValue(sym)
                    (fieldsInd, fields, types) = impl(e).st2ts3
                    elseBInd = fieldsInd.find(-1)
                result = kinds.mapIt(
                    block:
                        let
                            ind = fieldsInd.find(it[1])
                            i = if ind == -1: elseBInd else: ind
                        (it[0], fields[i], types[i])
                ).st2ts3
            else:
                error "unreachable", e[0]

proc getKindType*(selector: NimNode, kind: NimNode): NimNode =
    let
        reclist = selector.getRecList
    for e in reclist:
        if e.kind == nnkRecCase:
            e[0].matchAst:
            of  nnkIdentDefs(nnkSym(strVal = kind.strVal), `sym`@nnkSym, nnkEmpty):
                return sym
            else:
                error "unreachable", e[0]


func findTag(kinds: seq[NimNode], pattern: NimNode): int =
    result = kinds.mapIt(it.strVal).find(pattern.strVal)
    if result == -1:
        let tmp = kinds[0..^2].mapIt(it.strVal).join(", ") & &" or {kinds[^1].strVal}"
        error "invalid discriminator\nYou can use " & tmp, pattern

proc objectInfoFromObject(selector: NimNode): ObjectInfo =
    if selector.hasVariantPragma:
        ObjectInfo(kind: defaultDiscriminator(), kindType: selector.getKindType(defaultDiscriminator()), mode: Wrapped, fields: selector.getRecCaseFields(defaultDiscriminator()))
    else:
        ObjectInfo(mode: NoVariant, fields: selector.getRecListFields)

proc matchVariantObject(selector: NimNode, pattern: NimNode, objectInfo: ObjectInfo): NimNode =
    selector.matchDiscardingPattern(pattern, matchVariantObject(selector, pattern, objectInfo))
    let
        (kinds, kindFields, _) = objectInfo.fields
    case objectInfo.mode
    of Wrapped:
        pattern.matchAst:
        of {nnkCall, nnkObjConstr} |= pattern[0].kind in {nnkIdent, nnkSym, nnkOpenSymChoice}:
            let
                id = pattern[0].idOrSym
                i = kinds.findTag(id)
                patterns = if pattern.len > 1: pattern[1..^1] else: @[]
            if i == -1:
                error "You can use one of " & $kinds.mapIt(it.strVal), pattern
            if kindFields[i] == @[]:
                error &"It has no fields\nYou can simply use the pattern `{kinds[i].strVal}`", pattern
            return Call(bindSym"annotation", DotExpr(objectInfo.kindType, id)) and Infix("==", selector.newDotExpr(objectInfo.kind), kinds[i]) and Infix("?=", nnkPar.newTree(patterns), selector.newDotExpr(kindFields[i][0]))
        of nnkIdent:
            let
                i = kinds.findTag(pattern)
            if kindFields[i] != @[]:
                error &"It has field(s)\nYou must use `{kinds[i].strVal}(subpatterns)`", pattern
            return Call(bindSym"annotation", DotExpr(objectInfo.kindType, pattern)) and Infix("==", selector.newDotExpr(objectInfo.kind), kinds[i])
        else:
            echo pattern.treeRepr
            error "invalid pattern", pattern
    of NotWrapped:
        pattern.matchAst:
        of {nnkCall, nnkObjConstr} |= pattern[0].kind == nnkIdent:
            let
                id = pattern[0]
                i = kinds.findTag(id)
                patterns = if pattern.len > 1: pattern[1..^1] else: @[]
            assert i != -1
            return  Infix("==", selector.newDotExpr(objectInfo.kind), kinds[i]) and selector.matchTupleTy(nnkPar.newTree(patterns), kindFields[i].mapIt(it.strVal))
        of nnkIdent:
            let
                i = kinds.findTag(pattern)
            if kindFields[i] != @[]:
                error &"It has field(s)\nYou must use `{kinds[i].strVal}(subpatterns)`", pattern
            return Infix("==", selector.newDotExpr(objectInfo.kind), kinds[i])
        else:
            error "invalid pattern", pattern
    of NoVariant:
        pattern.matchAst:
        of {nnkCall, nnkObjConstr} |= pattern[0].kind == nnkIdent:
            let
                id = pattern[0]
                i = kinds.findTag(id)
                patterns = if pattern.len > 1: pattern[1..^1] else: @[]
            if not id.eqIdent(selector.getTypeSym):
                error "Bad identifier", id
            assert i != -1
            return  Call(bindSym"annotation", id) and selector.matchTupleTy(nnkPar.newTree(patterns), kindFields[i].mapIt(it.strVal))
        else:
            discard
    of NoCase, Incomplete:
        error "notimplemented", pattern

macro `?=`*(pattern: untyped, selector: object): untyped {.discardable.} =
    proc impl(selector: NimNode, pattern: NimNode): NimNode =
        let objectInfo = selector.getObjectInfo
        return selector.matchVariantObject(pattern, objectInfo)
    selector.impl(pattern)
macro `?=`*(pattern: untyped, selector: ref object): untyped {.discardable.} =
    return Infix("?=", pattern, nnkBracketExpr.newTree(selector))

proc newSpace(selector: NimNode, pattern: NimNode, used: var seq[string]): Space
proc newSpaceInt(selector: NimNode, pattern: NimNode, used: var seq[string]): Space =
    proc toInt(a: NimNode): BiggestInt =
        a.matchAst:
        of nnkIntLit:
            return a.intVal
        of nnkPrefix(ident"-", `a`@_):
            return -a.toInt
        of nnkDotExpr(ident"int", ident"high"):
            return int.high
        of nnkDotExpr(ident"int", ident"low"):
            return int.low
    let
        typInst = selector.getTypeInst
        typ = selector.getTypeImpl
    pattern.matchAst:
    of nnkIntLit:
        return Space.Int(typ, Slice[BiggestInt](a: pattern.intVal, b: pattern.intVal))
    of nnkInfix(ident"..", `a`@_, `b`@_):
        return Space.Int(typ, Slice[BiggestInt](a: a.toInt, b: b.toInt))

proc newSpaceFloat(selector: NimNode, pattern: NimNode, used: var seq[string]): Space =
    proc toInt(a: NimNode): BiggestInt =
        a.matchAst:
        of nnkIntLit:
            return a.intVal
        of nnkPrefix(ident"-", `a`@_):
            return -a.toInt
        of nnkDotExpr(ident"int", ident"high"):
            return int.high
        of nnkDotExpr(ident"int", ident"low"):
            return int.low
    let
        typInst = selector.getTypeInst
        typ = selector.getTypeImpl
    return Space.Empty()
    # TODO: impl
    # pattern.matchAst:
    # of nnkFloatLit:
    #     return Space.Float(typ, Slice[BiggestFloat](a: pattern.floatVal, b: pattern.floatVal))
    # of nnkInfix(ident"..", `a`@_, `b`@_):
    #     return Space.Float(typ, Slice[BiggestFloat](a: a.floatVal, b: b.floatVal))

proc newSpaceTuple(selector: NimNode, pattern: NimNode, used: var seq[string]): Space =
    let
        typInst = selector.getTypeInst
        typ = selector.getTypeImpl
    pattern.matchAst:
    of nnkPar:
        typ.matchAst:
        of nnkTupleConstr:
            let args = toSeq(typ).zip(toSeq(pattern)).mapIt(
                block:
                    let res = it[0].newSpace(it[1], used)
                    if it[1].kind == nnkIdent and it[1].strVal != "_" and it[1].strVal notin used:
                        used.add it[1].strVal
                    # TODO: id@pattern
                    res
            )
            return Space.Constructor(typInst, "untaggedTuple", args)
        of nnkTupleTy:
            proc findPattern(self: NimNode, id: NimNode): NimNode =
                for e in self:
                    if e.kind == nnkIdent and e.eqIdent(id):
                        return e
                    if e.kind == nnkExprColonExpr and e[0].eqIdent(id):
                        return e[1]
                error "unreachable", id
            return Space.Constructor(
                typInst,
                "taggedTuple",
                typ.mapIt((
                    let id = it[0];
                    let typ = it[1];
                    typ.newSpace(pattern.findPattern(id), used)
                ))
            )

proc newSpaceObject(selector: NimNode, pattern: NimNode, used: var seq[string]): Space =
    let
        typInst = selector.getTypeInst
        typ = selector.getTypeImpl
        objectInfo = selector.getObjectInfo
    pattern.matchAst:
    of {nnkCall, nnkObjConstr}:
        proc findPattern(self: NimNode, id: NimNode): NimNode =
            for e in self[1..^1]:
                if e.kind == nnkIdent and e.eqIdent(id):
                    return ident"_"
                if e.kind == nnkExprColonExpr and e[0].eqIdent(id):
                    return e[1]
            error "unreachable", id
        let
            id = pattern[0].idOrSym
            objectInfo = selector.getObjectInfo
        case objectInfo.mode
        of Wrapped:
            let
                a = objectInfo[id.strVal]
            return Space.Constructor(
                typInst,
                id.strVal,
                a[1][0].newSpace(nnkPar.newTree(pattern[1..^1]), used).args
            )
        of NoVariant:
            let a = objectInfo[id.strVal]
            return Space.Constructor(
                typInst,
                id.strVal,
                a[0].zip(a[1]).toSeq.mapIt((
                    let id = it[0];
                    let typ = it[1];
                    typ.newSpace(pattern.findPattern(id), used))
                )
            )
        else:
            error "notimplemented", selector
proc newSpaceRefObject(selector: NimNode, pattern: NimNode, used: var seq[string]): Space =
    let
        typInst = selector.getTypeInst
        typ = selector.getTypeImpl
    pattern.matchAst:
    of {nnkCall, nnkObjConstr}:
        proc findPattern(self: NimNode, id: NimNode): NimNode =
            for e in self[1..^1]:
                if e.kind == nnkIdent and e.eqIdent(id):
                    return ident"_"
                if e.kind == nnkExprColonExpr and e[0].eqIdent(id):
                    return e[1]
            error "unreachable", id
        let
            id = pattern[0].idOrSym
            objectInfo = selector.getObjectInfo
        case objectInfo.mode
        of Wrapped:
            let
                a = objectInfo[id.strVal]
            echo objectInfo
            return Space.Constructor(
                typInst,
                id.strVal,
                a[1][0].newSpace(nnkPar.newTree(pattern[1..^1]), used).args
            )
        of NoVariant:
            let a = objectInfo[id.strVal]
            return Space.Constructor(
                typInst,
                id.strVal,
                a[0].zip(a[1]).toSeq.mapIt((
                    let id = it[0];
                    let typ = it[1];
                    typ.newSpace(pattern.findPattern(id), used))
                )
            )
        else:
            error "notimplemented", selector

proc newSpace(selector: NimNode, pattern: NimNode, used: var seq[string]): Space =
    let
        typInst = selector.getTypeInst
        typ = selector.getTypeImpl
    pattern.matchAst:
    of {nnkIdent, nnkSym, nnkOpenSymChoice}:
        let pattern = pattern.idOrSym
        if pattern.strVal in used:
            return Space.Empty()
        if pattern.strVal != "_":
            used.add pattern.strVal
        return Space.Ty(typInst)
    of nnkPrefix(ident"!", nnkIdent):
        return Space.Empty()
    else:
        discard
    case typ.typeKind
    of ntyInt:
        return selector.newSpaceInt(pattern, used)
    of ntyFloat:
        return selector.newSpaceFloat(pattern, used)
    of ntyTuple:
        return selector.newSpaceTuple(pattern, used)
    of ntyObject:
        return selector.newSpaceObject(pattern, used)
    of ntyString:
        # TODO:
        return Space.Empty()
    of ntyRef:
        # return selector.newSpaceRefObject(pattern, used)
        error "notimplemented", pattern
    else:
        echo typ.typeKind
        echo typ.treeRepr
        echo typInst.treeRepr
        echo pattern.treeRepr
        error "notimplemented", pattern

proc newSpace(selector: NimNode, pattern: NimNode): Space = 
    var used: seq[string]
    selector.newSpace(pattern, used)
proc checkExaustivity(selector: NimNode, patterns: seq[NimNode]): bool =
    let
        tySpace = Space.Ty(selector.getTypeInst)
        coveredSpace = patterns.mapIt(selector.newSpace(it))
    var
        uncoveredSpace = tySpace
        i = 0
    for e in coveredSpace:
        uncoveredSpace = uncoveredSpace \ e
        inc i
        if uncoveredSpace.isEmpty:
            break
    if i != patterns.len:
        error "redundant pattern", patterns[i]
    uncoveredSpace.isEmpty

proc scanPattern(a: NimNode): NimNode =
    a.matchAst:
    # discarding the value
    # _
    of nnkOfBranch(`p`@nnkIdent(strVal = "_"), `body`@nnkStmtList):
        result = p
    of nnkOfBranch(nnkInfix(nnkIdent(strVal="and"), `p`@_,  `cond`@_), `body`@nnkStmtList):
        result = p
    # pattern mathing
    of nnkOfBranch(`p`@_, `body`@nnkStmtList):
        result = p
    # else branch
    of nnkElse(`body`@nnkStmtList):
        result = ident"_"
        result.copyLineInfo(body)
    else:
        error "invalid branch", a
    
proc ifVerify(ifStmt: NimNode, selector: NimNode, body: seq[NimNode]): NimNode =
    if ifStmt.len == 1 and ifStmt[0].kind == nnkElse:
        let s = ifStmt[0][0]
        # ifStmt[0] = nnkElifBranch.newTree(
        #     newLit(true),
        #     s
        # )
        return s
    let tmp = ifStmt.enumerate.filterIt(it[1].kind == nnkElse)
    if tmp.len > 1 or tmp.len == 1 and tmp[0][0] != ifStmt.len - 1:
        error "redundant pattern", body[tmp[0][0] + 1]
    
    let
        patterns = body.map(scanPattern)
    if selector.checkExaustivity(patterns):
        if ifStmt[^1].kind == nnkElse:
            ifStmt
        else:
            if ifStmt.len == 1:
                ifStmt.addElse(
                    nnkElse.newTree(newStmtList((
                        let err = bindSym"MatchError";
                        quote do:
                            raise newException(typeof `err`, "No match. (This behavior is adhoc(deprecated) implementation.)")
                    )))
                )
            else:
                let lastBranch = ifStmt[^1]
                ifStmt[^1] = nnkElse.newTree(
                    newStmtList(
                        DiscardStmt(lastBranch[0]),
                        lastBranch[1]
                    )
                )
                ifStmt
    else:
        error "not exaustive", selector
        ifStmt.addElse(
            # TODO: check wheathre patterns are exhaustive or not
            nnkElse.newTree(newStmtList(
                block:
                    let
                        err = bindSym"MatchError"
                    quote do:
                        raise newException(typeof `err`, "No match. (This behavior is adhoc(deprecated) implementation.)")
            ))
        )

macro matchImpl(selector: typed, body: varargs[untyped]): untyped =
    func impl(selector: NimNode, body: NimNode): NimNode =
        body.matchAst:
        # discarding the value
        # _
        of nnkOfBranch(nnkIdent(strVal = "_"), `body`@nnkStmtList):
            result = nnkElse.newTree(
                body
            )
        of nnkOfBranch(nnkInfix(nnkIdent(strVal="and"), `p`@_,  `cond`@_), `body`@nnkStmtList):
            result = nnkElifBranch.newTree(
                Infix("?=", `p`, selector) and cond,
                body
            )
        # pattern mathing
        of nnkOfBranch(`p`@_, `body`@nnkStmtList):
            result = nnkElifBranch.newTree(
                Infix("?=", `p`, selector),
                body
            )
        # else branch
        of {nnkElse, nnkElseExpr}(`body`@nnkStmtList):
            hint "You can use wildcard `_` instead of `else` branch", body
            result = nnkElse.newTree(
                body
            )
        else:
            error "invalid branch", body
    let body = toSeq(body)
  
    nnkIfStmt.newTree(
        body.mapIt(
            selector.impl(it)
        )
    ).ifVerify(selector, body)

macro match*(n: varargs[untyped]): untyped =
    let
        selector = nskLet.genSym(":selector")
        body = n[1..^1]
    selector.copyLineInfo(n[0])
    newIfStmt(
        (
            cond: newLit(true),
            body: newStmtList(
                newLetStmt(selector, n[0]),
                nnkCommand.newTree(bindSym"matchImpl", selector).add(body)
            )
        )
    ).addElse(
        nnkElse.newTree(newStmtList(
            block:
                let err = bindSym"MatchError"
                quote do:
                    raise newException(typeof `err`, "unreachable")
        ))
    )
    # We cannot use break statement in Block statement.
    # newBlockStmt(
    #     ident":match",
    #     newStmtList(
    #         newLetStmt(selector, n[0]),
    #         nnkCommand.newTree(bindSym"matchImpl", selector, n[0]).add(body)
    #     )
    # )

template optAnd*{true and a}(a: bool): bool = a
template optAnd*{a and true}(a: bool): bool = a
template optAnd*{false and a}(a: bool{noSideEffect}): bool = false
template optAnd*{a and false}(a: bool{noSideEffect}): bool = false
template optOr*{true or a}(a: bool{noSideEffect}): bool = true
template optOr*{a or true}(a: bool{noSideEffect}): bool = true
template otpOr*{false or a}(a: bool): bool = a
template otpOr*{a or false}(a: bool): bool = a


{.experimental: "caseStmtMacros".}


# Variant Option[T], kind:
# of Some:
#     val: T
# of None:
#     nil

# Algebraic Result[T, E]:
#     Ok(T)
#     Err(T)

# type
#     InvalidUnwrapError = object of ValueError

# func unwrap[T, E](self: Result[T, E], msg: string = ""): T =
#     match self:
#     of Ok(x):
#         return x
#     of Err(_):
#         raise newException(InvalidUnwrapError, msg)

# var a = Result[int, string].Ok(3)
# echo a.unwrap()