
open_at_end :: [a] -> ([a] -> [a])
open_at_end [] = id
open_at_end (x:xs) = \