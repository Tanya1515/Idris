module Lecture_11

data OpenMode = R | W | RW

data Canread : OpenMode -> Type where
RCanRead : CanRead R 
RWCanRead : CanRead RW

data CanWrite : OpenMode -> Type where 
WCanWrite : CanWrite W 
RWCanWrite : CanWrite RW

data LP : Type -> Type -> Type where 
    (M) : (1 _ : a) -> b -> LP a b

Functor (LP a) where 
    map f (x M y) = x M f y

-- 1 - promise to use the argument oly 1 time 
interface FileAPI m where 
    OpenFile : OpenMode -> Type

    openFile: (path : String) -> (mode : OpenFile) -> m $ LP (OpenFile mode) ()
    readFile: CanRead mode -> (1 _ :  OpenFile mode ) -> m $ LP (OpenFile mode) String 
    writeFile: CanWrite mode -> (1 _ : OpenFile mode ) -> m $ LP (OpenFile mode) String 

    closeFile -> OpenFile mode -> m ()

somwWork : Monad m => FileAPI m => HasIO m => m ()
someWork = do 
    file M () <- openFile "some-file" R 
    file M str <- readFile file 
    putStrLn str
    putStrLn str
    closeFile file

    
