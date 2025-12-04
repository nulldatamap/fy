-- Test program:
Test
-> double, main, cool, truth
-> CInt64, Pos, Opt
<- Data/List = L
<- Data/Maybe = M
<- Data/Maybe/Maybe/*

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

. main x = if $$eq x ()
          then id (Foo/Foo2 (Bar/High (double (wooz () ($$eq 1 2) (Pos/Pos cool 3) 2)))
                            (Bar/Low Opt/None))
               | (Foo/Foo2 (Bar/High x) z) -> x
          else second MyBool/True -100
. double x = $$add x x
. id x = x
. wooz a b c d = 3
. second a b = b
. cool = 3
. x = $$add ($$add 1 1) ($$add 2 3)
. y = $$add x w
. w = (q . q = 3)
. k x = ($$add (f x) 1 . f x = $$add 0 x)
. xy = Pos/Pos 2 3
. truth = MyBool/True

-- Cool huh?