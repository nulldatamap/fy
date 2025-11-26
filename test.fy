-- Test program:
: Pos = | Pos int int
: MyBool = | True | False
: OptInt = | Some int
           | None

if wow ($$eq 11 (k 3)) () (id qq)
then True
else False
. qq = ()
. wow x y z = x
. x = $$add ($$add 1 1) ($$add 2 3)
. y = $$add x w
. w = (q . q = 3)
. k x = ($$add (f x) 1 . f x = $$add 0 x)
. id x = x
. double x = $$add x x

-- Cool huh?