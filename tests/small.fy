Test
. main () = (binding_captures ()) ()
. binding_captures = (x
  . y = 1
  . x = \ -> (x . x = \ -> y))
-- . binding_captures0 = (x
--   . y = 1
--   . x = (x . x () = y))
