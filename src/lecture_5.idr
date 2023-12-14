module Lecture_5

%default total

--interface Show a where 
--    show : a -> String 
%hide Show

{-
    Задача: Определить функции, преобразующие в строку
    значения типа Bool, Char, Nat, List a.
-}

showBool : Bool -> String
  showBool True  = "True"
  showBool False = "False"

  showChar : Char -> String
  showChar c = pack [ c ]
  
  div10 : Nat -> Nat
  div10 $ S $ S $ S $ S $ S $ S $ S $ S $ S $ S n = 1 + div10 n
  div10 n = 0

  mod10 : Nat -> Nat
  mod10 $ S $ S $ S $ S $ S $ S $ S $ S $ S $ S n = mod10 n
  mod10 n = n

-- fuel уменьшается медленнее, чем само число
  showNat' : Nat -> Nat -> String
  showNat' (S fuel) =
    \case
      0 => "0"
      1 => "1"
      2 => "2"
      3 => "3"
      4 => "4"
      5 => "5"
      6 => "6"
      7 => "7"
      8 => "8"
      9 => "9"
      n => (showNat' fuel (div10 n)) ++ (showNat' fuel (mod10 n))
  showNat' 0 = const ""

  showNat n = showNat' n n
--

-- Интерфейс определяет требования к типу.
  interface Show a where
    show : a -> String

  showList' : Show a => List a -> String
  showList' [] = ""
  showList' [x] = show x
  showList' (x1::x2::xs) = (show x1) ++ "," ++ showList' (x2::xs)

  showList : Show a => List a -> String
  showList xs = "[" ++ (showList' xs) ++ "]"

-- Тип реализует эти требования.
Show Bool where 
    show = showBool

Show Char where 
    show = showChar

Show Nat where 
    show = showNat

(Show a) Show (List a) where 
    -- show : List a -> String
    show = showList 

{-
    Задание:
      Реализовать функцию, которая по значению и списку значений этого же типа
      возвращает True, если это значение присутствует в списке, False - иначе.
-}

-- check if a is in list 
contains : (Eq a) => a -> List a -> Bool
contains y [] = False
-- contains y (x :: xs) = case y == x of
--                        True => True    
--                        False => contains y xs
contains y (x :: xs) = y == x || contains y xs

%hide Eq

interface Eq a where 
    (==) : a -> a -> Bool
    (/=) : a -> a -> Bool 

x == y = not (x /= y)   -- default
x /= y = not (x == y)   -- default

{-
    Для реализаций этого интерфейса ожидается выполнение следующих законов:
      - Рефлексивность: x == x = True для любого x.
      - Симметричность: x == y = y == x для любых x и y.
      - Транзитивность: Если x == y = True и y == z = True, то x == z = True.
      - (/=) это отрицание (==): x == y = not (x /= y) для любых x и y.

    Законы не всегда могут быть формально доказаны.
    Даже если доказательство возможно, оно может оказаться весьма трудоемким. 
-}

{-
    Расширение интерфейсов.

    Любой тип с порядком должен поддерживать и сравнение на равенство.
-}

  %hide Ordering
  %hide Ord

  data Ordering = LT | EQ | GT

  interface Ord a where
    compare : a -> a -> Ordering
--

-- interfaces can be implemented for several types 
%hide Cast 

interface Cast fr to where 
    cast : fr -> to

{-
    Ограничения - это не какая-то новая сущность, а тоже типы.
    Значения этих типов - факты.
    Предоставление значения такого типа при вызове функции означает
    факт поддержки ограничения типом.

    Вместо ограничения в сигнатуру функции можно добавить
    неявный автоматический параметр `e`,
    значение которого будет подбираться компилятором из контекста.
    `a`- тоже неявный параметр, но не автоматический,
    вычисляется из самой сигнатуры и места вызова.  
-}
  contains' : {a : Type} -> {auto e : Eq a} -> a -> List a -> Bool
  contains' _ [] = False
  contains' e (x :: xs) = e == x || contains' e xs
--








