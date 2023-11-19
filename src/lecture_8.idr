module Lecture_8

%default total

import Data.Nat

concatTree: Tree a -> Tree a -> Tree a
concatTree t Empty = t
concatTree t (Leaf n) = Node n Empty t
concatTree t (Node n l r) = Node n (concatTree l r) t

count: Tree a -> Nat 
count Empty = 0
count (Leaf _) = 1
count (Node _ l r) = 1 + count l + count r 

-- sentence for checking the correctness of the programs "count" and "concatTree"
countofConcatTree: (l, r: Tree a) -> coount (concatTree l r) = count l + count r 
countofConcatTree t Empty = rewrite plusCommutative (count t) 0 in Refl 
countofConcatTree t (Leaf x) = rewrite plusCommutative (count t) 1 in Refl
countofConcatTree t (Node x y z) = do
    let u = plusCommutative (count t) (1 + count r + count l)
    rewrite u 
    rewrite countofConcatTree l r 
    Refl 

-- a /\ b          ~ (a,b)
-- a \/ b          ~ Either a b
-- a => b          ~ a -> b
-- A (a : T) (P a) ~ (a : T) -> P a 
-- E (a : T) (P a) ~ (a : T ** P a)
-- T               ~ ()
-- F               ~ Void

Not: Type -> Type 
Not p = p -> Void 

-- !( a /\ b ) = !a \/ !b
-- (!( a /\ b ) => !a \/ !b) /\ (!( a /\ b ) <= !a \/ !b)
dm1: ( Not (a,b) -> Either (Not a) (Not b),  Either (Not a) (Not b) -> Not (a,b))
dm1 = do 
    let l = 
    let r = \e, p => the Void $ case e of 
                        Left x => x $ fst p
                        Right x => x $ snd p
    (l, r)


-- !( a \/ b ) = !a /\ !b
