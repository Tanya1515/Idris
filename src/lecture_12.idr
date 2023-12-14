module Lecture_12

import Data.Maybe
import Data.List

%default total

namespace Stack

  public export
  interface Stack a s where
    emptySt  : s
    push     : a -> s -> s
    pop      : s -> Maybe (s, a)
    toListSt : s -> List a

    0 toListEmpty : toListSt emptySt = []
    0 toListPush  : (st : s) -> (x : a) -> toListSt (push x st) = x :: toListSt st
    0 toListPop   : (st : s) -> IsJust (pop st) =>
                    let popd = fromJust $ pop st in
                    toListSt st = snd popd :: toListSt (fst popd)

    0 popEmptyCorrect   : pop emptySt = Nothing

    0 popPushCorrectVal : (st : s) -> (x : a) -> (map Builtin.snd $ pop $ push x st) = Just x
    0 popPushCorrectSt  : (st : s) -> (x : a) -> (map (toListSt . Builtin.fst) $ pop $ push x st) = Just (toListSt st)

namespace Queue

  public export
  interface Queue a q where
    emptyQ  : q
    enqueue : a -> q -> q
    dequeue : q -> Maybe (q, a)
    toListQ : q -> List a

    0 toListEmpty   : toListQ emptyQ = []
    0 toListEnqueue : (qu : q) -> (x : a) -> toListQ (enqueue x qu) = toListQ qu ++ [x]
    0 toListDequeue : (qu : q) -> IsJust (dequeue qu) =>
                      let deq = fromJust $ dequeue qu in
                      toListQ qu = snd deq :: toListQ (fst deq)

    0 dequeueEmptyCorrect : dequeue emptyQ = Nothing

    0 dequeueEnqueueIsJust : (qu : q) -> (x : a) -> IsJust $ dequeue $ enqueue x qu

-----------------------------------

Stack a (List a) where
  emptySt = []
  push = (::)
  pop []      = Nothing
  pop (x::xs) = Just (xs, x)
  toListSt = id

  toListEmpty = Refl
  toListPush st x = Refl
  toListPop (x::xs) = Refl

  popEmptyCorrect = Refl
  popPushCorrectVal st x = Refl
  popPushCorrectSt st x = Refl

Queue a (List a) where
  emptyQ = []
  enqueue x qu = qu ++ [x]
  dequeue []      = Nothing
  dequeue (x::xs) = Just (xs, x)
  toListQ = id

  toListEmpty = Refl
  toListEnqueue qu x = Refl
  toListDequeue (x::xs) = Refl

  dequeueEmptyCorrect = Refl
  dequeueEnqueueIsJust []      x = ItIsJust
  dequeueEnqueueIsJust (x::xs) y = ItIsJust

monadLawMaybe : (x : a) -> (f : a -> Maybe b) -> pure x >>= f = f x
monadLawMaybe x f = Refl