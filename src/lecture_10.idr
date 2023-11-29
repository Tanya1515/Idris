module Lecture_10

dec45: Dec (4 'LTE' 5)
dec45= Yes $ LTESucc $ LTESucc $ LTESucc $ LTESucc LTEZero 

dec54_func : LTE (S n) n -> Void
dec54_func LTEZero impossible 
dec54_func (LTESucc x) dec54_func x

dec54: Dec (5 'LTE' 4)
dec54= No $ dec54_func

elementExists : (xs : List a) -> (f : a -> Bool) -> Dec (x : a ** So $ f x, 
                                (idx : Fin (length xs) ** index' xs idx = x))
elementExists [] f = No $ \case (x ** (_, (FZ ** _))) impossible 
elementExists (x :: xs) f = case decSo f x of 
                                Yes fx => Yes (x ** (Oh, (0 ** Refl)))
                                No nfx = case elementExists xs f of 
                                    Yes (x' ** (sofx, (idx ** idxGood))) => Yes (x' ** (sofx, (FS idx ** idxGood)))
                                    No nfx' => No $ \case 
                                            (x' ** (sofx, (FZ ** idxGood))) => nfx $ rewrite indexGood in sofx
                                            (x' ** (sofx, (FS idx ** idxGood))) => nfx' (x' ** (sofx, (idx ** idxGood)))


sprintfImpl: List Char -> (ty: Type ** ty)
sprintfImpl [] = (String ** "")
sprintfImpl ('%' :: 'd' :: xs) = (integer -> fst $ sprintfImpl xs ** \n => show n ++ snd sprintfImpl xs)
sprintfImpl (x :: xs) =

sprintf: (str : String) -> fst $ sprintfImpl $ unpack str
sprintf str = snd $ SprintfImpl $ unpack str
