Rec
: Tree a = | Leaf a
           | Branch (Tree a) (Tree a)
: LRTree a = | Leaf a
             | Branch (Left a) (Right a)
: Right a = | R (LRTree a)
: Left a = | L (LRTree a)

. main () = $$add (center (into_lrtree example)) (size example)
. example = Tree/Branch (Tree/Branch (Tree/Branch (Tree/Leaf 0) (Tree/Leaf 1)) (Tree/Leaf 2)) (Tree/Leaf 3)

. into_lrtree t = t
  | Tree/Leaf x -> LRTree/Leaf x
  | Tree/Branch l r -> LRTree/Branch (Left/L (into_lrtree l))
                                     (Right/R (into_lrtree r))

. size t = t | Tree/Leaf _ -> 1
             | Tree/Branch l r -> $$add (size l) (size r)

. center t = t | LRTree/Leaf _ -> 1
               | LRTree/Branch l r -> $$add (left l) (right r)
. left t = t | Left/L l -> center l
. right t = t | Right/R r -> center r
