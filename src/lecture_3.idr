module Lecture_3

%default total

--Необходимо упордочить дни рождения по месяцу и дню, независимо от года.
data Month = Jan | Feb | Mar | Apr | May | Jun | Jul | Aug | Sept | Oct | Nov | Dec

Year  = Nat

data Day = MkDay Nat

--функция, которая принимает на вход Nat и ограничивает количество дней в месяце
mkDay : Nat -> Month -> Year -> Day
mkDay d m y = MkDay d

mkDate : Nat -> Month -> Year -> Date
mkDate d m y = MkDate (MkDay d m y) m y  -- Mkdate - название конструктора
data Date = MkDate Day Month Year

-- в данном случае SingleElem Date - список из одного элемента Empty - пустой список
myBday : Date
myBDay = MkDate (MkDay 22) Aug 1974

data ListDate = Prepend Date ListDate | Empty

-- создание списка
-- $ - замена скобок
bdays = Prepend myBDay
           $ Prepend (mkDate 31 Dec 1980)
               $ Prepend (mkDate 13 Jun 2015)
                  $ Prepend (mkDate 30 Dec 1980) Empty 

-- функция, которая сравнивает два натуральных числа
compareNat : Nat -> Nat -> Ordering
compareNat (S m) (S n) = compareNat m n
compareNat (S _) Z = GT //_ - замена m
compareNat Z (S _) = LT //_ - замена n
compareNat Z Z = EQ

-- ставим в соответствие месяцу натуральное число
monthToNat : Month -> Nat
monthToNat Jan = 1
monthToNat Feb = 2
...

-- другой способ поставить в соответствие месяцу настуральное число
monthToNat : Month -> Nat
monthToNat =
   \case
       Jan => 1
       Feb => 2
       Mar => 3
       Apr => 4
       May => 5
       Jun => 6
       Jul => 7
       Aug => 8
       Sept => 9
       Oct => 10
       Nov => 11
       Dec => 12


-- функция, которая сравнивает месяцы
compareMonth : Month -> Month -> Ordering
compareMonth m n = compareNat (monthToNat m) (monthToNat n)

-- функция, которая сравнивает две даты
compareInYear : Date -> Date -> Ordering
compareInYear (MkDate (MkDay d1) m1 _) (MkDate (MkDay d2) m2 _) =
   case (compareMonth m1 m2) of
       EQ => compareNat d1 d2
       r => r -- универсальная подстановка, что бы функция не выдала, тоже самое мы и вернем
      
-- функция, которая вставляет элемент в уже отсортированный список
insertinSorted : Date -> ListDate -> ListDate
insertinSorted d_in ds_all@(Prepend d_tek ds) =
   case compareInYear d_in d_tek of
       LT => Prepend d_in ds_all
       EQ => Prepend d_in ds_all
       GT => Prepend d_tek $ insertinSorted d_in ds
insertinSorted d Empty = Prepend d Empty


-- функция, сортирует список
sortInYear : ListDate -> ListDate
sortInYear Empty = Empty
sortInYear (Prepend d ds) = insertinSorted d (sortInYear ds)
  
-- новый тип данных, который объявляет три случай: строго меньше, равно, строго больше 
data Ordering = LT | EQ | GT -- - присутствует в библиотеке

-- функция, которая принимает год и возвращает еще один год
nextYear : Year -> Year
nextYear y = S y
