module Lecture_9

%default total

lemma : (xs: _) -> (x: _) -> (ys: _) -> length (xs ++ x :: ys) = length(x :: xs ++ ys)
lemma [] z ys = Refl
lemma (x::xs) z ys = cong S $ lemma xs z ys

lengthAppend: (xs, ys: List a) -> length(xs ++ ys) = length(xs) + length(ys) 
lengthAppend [] ys = Refl 
lengthAppend (x::xs) ys = cong S $ lengthAppend xs ys --cong S ... -> rewrite ... in Refl

-- amount of elements in tree is equal to amount elements in list, 
--which was made from the tree
countToListLength : (tree: _) count tree = length (toList tree)
countToListLength Empty = Refl
countToListLength (Leaf x) = Refl
countToListLength (Node x l r) = do
    rewrite lemma (toList l) x (toList r)
    cong S $ do 
        rewrite  legthAppend (toList l) (toList r)
        cong2 plus (countToListLength l) (countToListLength r)

--Another way of prooving countToListAppend 
--countToListLength (Node x l r) = do
--    rewrite lemma (toList l) x (toList r)
--    rewrite lengthAppend (toList l) (toList r)
--    rewrite countToListLength l
--    rewrite countToListLength r
--    Refl

lteTransitive: (n, m, k : Nat) -> n 'LTE' m -> m 'LTE' k -> n 'LTE' k
lteTransitive 0 m k nm mk = LTEZero
lteTransitive (S n) (S m) (S k) (LTESucc nm) (LTESucc mk) = LTESucc $ lteTransitive n m k nm mk

lteAntiReflexive : (n,m : Nat) -> (n 'LTE' m) -> (m 'LTE' n) -> n=m
lteAntiReflexive 0 m LTEZero LTEZero = Refl
lteAntiReflexive (S n) (S m) (LTESucc nm) (LTESucc mn) = cong S lteAntiReflexive n m nm mn 

ltTransitive : (n, m, k : Nat) -> n 'LT' m -> m 'LT' k -> n 'LT' k
ltTransitive 0 (S m) (S k) (LTESucc nm) (LTESucc mn) = LTESucc LTEZero
ltTransitive (S n) (S m) (S k) (LTESucc nm) (LTESucc mn) = LTESucc $ ltTransitive n m k nm mk 

ltAntiSimmetric : (n,m : Nat) -> (n 'LT' m) -> Not (m 'LT' n)
ltAntiSimmetric n m nm mn = do
    let u = ltTransitive _ _ _ nm mn
    case u of 
        LTEZero impossible
        
--ltAntiSimmetric (S n) (S m) (LTESucc nm) (LTESucc mn) = ltAntiSimmetric n m nm mn