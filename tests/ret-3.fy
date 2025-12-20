RetThree
: MyRecord = | Cool int int
: MyEnum = | Red | Green | Blue
: MyTagged = | Wow int | None
: MyCType = $$ctype int

. main () = if $$eq 2 3
            then three
            else MyTagged/Wow 3 | MyTagged/Wow x -> x
                                | _ -> 3
. one = 1
. two = 2
. addem x y = $$add x y
. three = $$add one two
