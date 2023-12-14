module Lecture_4 

--Полиморфизм

{-
    Бенджамин Пирс, "Типы в языках программирования":

    Термин “полиморфизм” обозначает семейство различных механизмов,
    позволяющих использовать один и тот же участок программы
    с различными типами в различных контекстах.
-}

{-
    List Nat, List Char, List Int - это типы.
    А что такое List?
-}
    ListNat : Type
    ListNat = List Nat

    ListChar : Type
    ListChar = List Char

    ListInt : Type
    ListInt = List Int

    mkList : Type -> Type
    mkList a = List a
--

{-
    List - это конструктор типов. Функция, которая принимает
    на вход тип и возвращает тип.
    Nil и (::) - это конструкторы значений, тоже функции. Какие у них типы?
    
    Полная форма определения типа:
-}
  namespace Prelude'
    data List : Type -> Type where
      Nil  :                List a
      (::) : a -> List a -> List a
--

{-
    a - это неявный (implicit - в фигурных скобках) параметр, значение которого подбирает компилятор:
-}
  namespace Prelude''
    data List' : Type -> Type where
      Nil' : {0 a : Type}                 -> List' a
      (::) : {0 a : Type} -> a -> List' a -> List' a

    l : List' Nat
    l = Nil'
--
-- Необходимо объявить функцию, которая вставляет заданный элемент
--на заданную позицию (с 0) в заданном списке, возвращает полученный список.
-- Если в списке меньше элементов, то новый элемент добавляется в конец

AddElementToPos : a -> Nat -> List a -> List a
AddElementToPos elem pos [] = [elem]
AddElementToPos elem Z list =  elem :: list  //:: разделяем списое на две части - first :: tail
AddElementToPos elem (S pos) (first : tail) = h :: AddElementToPos elem pos hs

-- :r - перезагрузка
-- :s - поиск функции (по сигнатуре), пример: :s (a,b) -> a

-- Пары
data Pair a b = MkPair a b

yy : (Nat,Char) -- определение пары
yy = (4, '&')

-- Полиморфные функции для пар
-- Необходимо определить функции fst, snd, которые возвращают соответсвенно первый и второй элемент
-- заданной пары, а также функцию swap, которая меняет местами элементы в паре

fst : (a,b) -> a
fst (x,_) = x

snd : (a,b) -> b
snd (_,y) = y

swap : (a,b) -> (b,a)
swap (x,y) = (y,x)

-- Определить функцию, которая возвращает список, элементами которого являются пары
-- соответствующих элементов двух заданных списков.
-- Длина результирующего списка равна минимуму из длин исходных списков

CreateList : List a -> List b -> List (a,b)
CreateList [] _ = []
CreateList _ [] = []
CreateList (x :: tail_x) (y :: tail_y) = (x,y) :: CreateList tail_x tail_y

carry: ((a,b) -> c) -> (a->b->c)
carry f = \x y => f (x,y)

-- Функция, которая фильтрует элементы списка и возвращает новый список
%hide Prelude.Types.List.filter
namespace Filter
   filter : (a -> Bool) -> List a -> List a
   filter p [] = []
   filter p (x :: xs) =
       case p x of
           True => x :: filter p xs
           False => filter p xs


   count : (a -> Bool) -> List a -> Nat
   count p xs = length@ (filter p xs)


-- Count можно переписать
count : (a -> Bool) -> List a -> Nat 
count p xs = (length . (filter p)) xs --где (.) -> (b -> c) -> (a -> c) -> (a -> c)

compareNat Nat -> Nat -> Bool
compareNat (S m) (S n) = compareNat m n
compareNat (S _) Z = True 
compareNat Z (S _) = False
compareNat Z Z = True

CutList : List  -> Nat -> List  
CutList _ Z -> []
CutList (elem : l) (S amount_elem) =
	case compareNat length(l) amount_elem of
		True => elem : CutList l amount_elem
		False => []Z

-- Объявите и определите функцию, которая принимает на вход функцию f : a -> b`
-- и список элементов типа `a, а возвращает список элементов типа b, которые 
-- получены применением функции f к соответствующим элементам исходного списка.

makeList : (a -> b) -> List a -> List b
makeList f [] = []
makeList f (x :: xs) = f x :: makeList f xs