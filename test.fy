-- Test program:
: CInt64 = $$ctype int64_t
: Pos = | Pos int int
: Rect = | Rect Pos Pos
: MyBool = | True | False
: Opt a = | Some a | None
: Bar = | High int
        | Low (Opt int)
: Foo = | Foo Bar
        | Foo2 Bar Bar
        | Foone

if $$eq 1 1
then id (Foo2 (High (double (wooz () ($$eq 1 2) xy 2)))
           (Low None))
     | (Foo2 (High x) z) -> x
else -100
. qq = ()
. wow x y z = x
. x = $$add ($$add 1 1) ($$add 2 3)
. y = $$add x w
. w = (q . q = 3)
. wooz a b c d = 3
. k x = ($$add (f x) 1 . f x = $$add 0 x)
. id x = x
. double x = $$add x x
. xy = Pos 2 3
. truth = True

-- Cool huh?