Test
: IntFunc = | IntFunc (int -> int)

. main () = apply incer 3
. apply i x = i | IntFunc/IntFunc f -> f x
. incer = IntFunc/IntFunc inc
. inc x = $$add x 1
. id x = x
