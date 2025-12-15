Lam

. main () = 0
-- Syntax
. zero = \ -> 0
. one  = \x -> 1
. inc  = \x -> $$add x 1
. const = \x y -> x
-- Application
. three = (id 3 . id = \x -> x)
-- Scoping
. holder = (x y z
  . x = \z -> $$add y z
  . y = 0
  . z = \ -> $$add (one ()) y)
