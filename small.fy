Test
: IntFunc = | IntFunc (int -> int)

. main x = if $$eq x () then apply incer 3 else 0
. apply i x = i | IntFunc/IntFunc f -> f x
. incer = IntFunc/IntFunc inc
. inc x = $$add x 1
. id x = x
