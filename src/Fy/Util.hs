module Fy.Util
  ( partitionWith )
  where

partitionWith :: (a -> Either b c) -> [a] -> ([b], [c])
partitionWith _ [] = ([],[])
partitionWith f (x:xs) =
  case f x of
    Left  b -> (b:bs, cs)
    Right c -> (bs, c:cs)
  where
    (bs,cs) = partitionWith f xs
