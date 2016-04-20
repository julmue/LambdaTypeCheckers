{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
data Absurd

data Term a where
    Top  :: Term ()
    Bot  :: Term Absurd
    B    :: Bool -> Term Bool
    I    :: Int -> Term Int
    C    :: Char -> Term Char
    S    :: String -> Term String
    P    :: Term a -> Term b -> Term (a,b)
    PL   :: Term (a,b) -> Term a
    PR   :: Term (a,b) -> Term b
    IL   :: Term a -> Term (Either a b)
    IR   :: Term b -> Term (Either a b)
    CA   :: Term (Either a b) -> Term (a -> c) -> Term (b -> c) -> Term c
    V    :: a -> Term a
    A    :: Term (a -> b) -> Term a -> Term b
    L    :: a -> Term b -> Term (a -> b)

