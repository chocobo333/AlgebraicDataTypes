
type
    RangeSet*[T] = seq[Slice[T]]

func insert[T](self: var RangeSet[T], val: Slice[T]): var RangeSet[T] =
    if val.b in self[0]:
        self[0].a = min(self[0].a, val.a)
        return self
    var i = 1
    while i < self.len:
        if val in self[i]:
            return self
        if val.a in self[i]:
            if i + 1 < self.len and val.b in self[i+1]:
                self[i].b = self[i+1].b
                self.delete(i+1)
                return self
            self[i].b = val.b
        inc i

func contains[T](self, other: Slice[T]): bool =
    other.a in self and other.b in self
func `\=`[T](self: var RangeSet[T], other: Slice[T]) =
    var i = 0
    while i < self.len and other.b >= self[i].a:
        if self[i].b < other.a:
            inc i
            continue
        if self[i] in other:
            self.delete(i)
            continue
        if other in self[i]:
            if self[i].a == other.a:
                self[i].a = other.b
                inc self[i].a
                return
            if self[i].b == other.b:
                self[i].b = other.a
                dec self[i].b
                return
            self.insert(Slice[T](a: other.b, b: self[i].b), i+1)
            self[i].b = other.a
            dec self[i].b
            inc self[i+1].a
            return
        if self[i].b in other:
            self[i].b = other.a
            dec self[i].b
            inc i
            continue
        if self[i].a in other:
            self[i].a = other.b
            inc self[i].a
            inc i
            continue

func `\`*[T](self, other: RangeSet[T]): RangeSet[T] =
    result = self
    for e in other:
        result \= e