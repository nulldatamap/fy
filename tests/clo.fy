-- Same as lam.fy, but uses named functions instead
Clo

. main () = zero ()
-- Syntax
. zero () = 0
. one x   = 1
. inc x   = $$add x 1
. constf x y = x
-- Global usage
. inc0 x = inc x
-- Application
. three = (id 3 . id x = x)
-- Scoping/closure
. holder = ($$add (z ()) (x y)
  . x z = $$add y z
  . y = 0
  . z () = $$add (one ()) y)
. add3 x = (add3_ . add3_ y = (add3__ . add3__ z = $$add x ($$add y z)))
. binding_captures = (0
  . y = 1
  . x () = (x . x () = y))
