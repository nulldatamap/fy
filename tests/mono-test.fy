MonoTest
: Mono = | Mono int int
: Box a = | Box a
: Outer = | Outer (Box ()) | Huh
: Pair a b = | Pair a b
: FixedPair a = | FixedPair (Pair a int)

. main () = if id true then unbox (box (exchange (Mono/Mono 0 0))) else id (unbox (id gift))
. local_mono () = (wooz 3 . wooz x = x)
. true = $$eq 1 1
. exchange x = 3
. conrete_fixed_pair = FixedPair/FixedPair (Pair/Pair 2 3)
. get_first x = x | FixedPair/FixedPair (Pair/Pair v _) -> v
. gift = box 11
. box x = Box/Box x
. unbox x = x | Box/Box v -> v
. id x = x
