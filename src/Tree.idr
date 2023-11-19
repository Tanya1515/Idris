module Tree

%default total

data Tree : Type -> Type where 
    Nil :  Tree a
    Leaf : a -> Tree a
    Node : a -> Tree a -> Tree a -> Tree a


contains: (Ord a) => a -> Tree a -> Bool 
contains y Nil = False
contains y (Leaf x) = x == y 
contains y (Node x left right)  = 
    case compare y x then 
        EQ => True
        LT => contains left y
        GT => contains right y 

insert : (Ord a) => a -> Tree a -> Tree a
insert y Nil = Leaf y
insert y (Leaf x) = 
    GT => Node y (Leaf x) Nil 
    EQ => t
    LT => Node x (Leaf y) Nil 
insert y (Node x left right) =
    case compare y x of
    LT => Node x (insert left y) right
    EQ => t
    GT => Node y left (insert right x)
    

t = Node 10 (Leaf 7) (Leaf 11)

{-
    Задание:
      Объявите и определите функцию, которая принимает на вход функцию f : a -> b
      и список элементов типа a, а возвращает список элементов типа b,
      которые получены применением функции f к соответствующим элементам исходного списка.
-}
  mapList : (a -> b) -> List a -> List b
  mapList f [] = []
  mapList f (x::xs) = f x :: mapList f xs
--

{-
    Задание:
      Определить функцию mapTree с почти такой же сигнатурой, как для List.
-}
mapTree : (a -> b) -> Tree a -> Tree b
mapTree f Nil = Nil 
mapTree f (Leaf x) = Leaf (f x)
mapTree f (Node x left right) = Node (f x) (mapTree f left) (mapTree f right)

toList : Tree a -> List a
  toList Empty               = []
  toList (Leaf x)            = [x]
  toList (Node x left right) = toList left ++ [x] ++ toList right

-- как описать требование к контейнеру поддерживать функцию map?
$hide Functor 

interface Functor (m: Type -> Type) where 
    map : (a -> b) -> m a -> m b 

Functor Tree where
   map = mapTree
   
{-
    На map можно смотреть как на трансформер функции элемента в функцию контейнера.
    (a -> b) -> (f a -> f b)

    Это подчеркивается синтаксисом:
    f  $  x - применение функции к значению
    f <$> t - применение функции к контейнеру
    <$> - это инфиксная версия map
-}
