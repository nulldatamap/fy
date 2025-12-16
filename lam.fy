Lam

. main () = 0
-- Syntax
. zero = \ -> 0
. one  = \x -> 1
. inc  = \x -> $$add x 1
. const = \x y -> x
-- Global usage
. inc0 = \x -> inc x
-- Application
. three = (id 3 . id = \x -> x)
-- Scoping/closure
. holder = ($$add (z ()) (x y)
  . x = \z -> $$add y z
  . y = 0
  . z = \ -> $$add (one ()) y)
. add3 = \x -> \y -> \z -> $$add x ($$add y z)
. binding_captures = (0
  . y = 1
  . x = \ -> (x . x = \ -> y))