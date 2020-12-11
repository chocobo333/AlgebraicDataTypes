
import tables
import sequtils

import macros


type
    VariantMode* = enum
        Wrapped
        NotWrapped
        NoCase
        NoVariant
        Incomplete
    ObjectInfo* = object
        kind*: NimNode
        kindType*: NimNode
        kindGetter*: NimNode
        case mode*: VariantMode
        of Wrapped, NotWrapped, NoVariant:
            fields*: (seq[NimNode], seq[seq[NimNode]], seq[seq[NimNode]])
        of NoCase:
            children*: NimNode
        of Incomplete:
            nil
    ObjectContext* = Table[string, ObjectInfo]

func `[]`*(self: ObjectInfo, key: string): (seq[NimNode], seq[NimNode]) =
    let i = self.fields[0].mapIt(it.strVal).find(key)
    (self.fields[1][i], self.fields[2][i])

func newContext: ObjectContext = initTable[string, ObjectInfo]()
proc `$`(self: NimNode): string = self.repr
proc `$`*(self: ObjectContext): string =
    tables.`$`(self)

var
    objectContext* {.compileTime.}: ObjectContext = newContext()