Test
. main () =
  $$add
    ((binding_captures0 ()) ())
    ((binding_captures ()) ())
. binding_captures = (x
  . y = 99
  . x = \z -> (x . x = \z -> y))
. binding_captures0 = (x
  . y = 1
  . x a = (x . x b = y))
