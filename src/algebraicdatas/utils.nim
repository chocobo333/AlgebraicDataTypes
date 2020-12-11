
import options
import optionsutils
import sequtils

import macros
import ast_pattern_matching

import contexts

func add*(father: NimNode, child: Option[NimNode]): NimNode =
    withSome child:
        some child:
            father.add child
        none:
            father

func newIndex*(a: NimNode, b: int): NimNode =
    nnkBracketExpr.newTree(a, newIntLitNode(b))

func addElse*(ifStmt: NimNode, elseBranch: NimNode): NimNode =
    ## When `ifStmt` has no else branches, add to `elseBranch` `ifStmt`
    ifStmt.expectKind({nnkIfStmt, nnkIfExpr})
    elseBranch.expectKind({nnkElse, nnkElseExpr})
    if ifStmt.len == 0 or ifStmt[^1].kind notin {nnkElse, nnkElseExpr}:
        ifStmt.add elseBranch
    ifStmt

func `and`*(a, b: NimNode): NimNode =
    nnkInfix.newTree(ident"and", a, b)

macro error2*(msg: static[string], n: untyped): untyped =
    ## macro version of `error` in macros
    ## This is useful for use in template
    error msg, n
macro hint2*(msg: static[string], n: untyped): untyped =
    ## macro version of `hint` in macros
    ## This is useful for use in template
    hint msg, n
macro warning2*(msg: static[string], n: untyped): untyped =
    ## macro version of `warning` in macros
    ## This is useful for use in template
    warning msg, n

macro annotation*(a: enum): untyped = newLit(true)
macro annotation*(a: type): untyped = newLit(true)
macro annotation*(a: typed): untyped = newLit(true)

func getSymHash*(n: NimNode): string =
    n.matchAst:
    of `t`@nnkSym:
        result = t.signatureHash
    of `t`@nnkBracketExpr:
        result = t.mapIt(it.signatureHash).foldr(a & b)
    else:
        error "notimplemented", n
        
func getTypeHash*(n: NimNode): string =
    n.getTypeInst.matchAst:
    of `t`@nnkSym:
        result = t.signatureHash
    of `t`@nnkBracketExpr:
        result = t.mapIt(it.getSymHash).foldr(a & b)
    else:
        error "notimplemented", n

template getObjectInfo*(selector: typed): untyped = 
    let
        key = selector.getTypeHash
        objectInfo = if objectContext.contains(key):
            objectContext[key]
        else:
            let res = selector.objectInfoFromObject
            objectContext[key] = res
            res
    objectInfo