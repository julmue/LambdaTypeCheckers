import Data.List (elemIndex, nub)

infixl 7 :@
infixl 9 :&
infix 0 :::

type Name = String
data Term
    = U
    | B Bool
    | I Int
    | C Char
    | S String
    | Term :& Term
    | ProjL Term
    | ProjR Term
    | InjL Term Type
    | InjR Term Type
    | Case Term Term Term
    | Tup [Term]
    | ProjTup Int Term
    | Rec [(Name,Term)]
    | ProjRec Name Term
    | Var [(Name,Term)]
    | ProjVar Name Term
    | V Name
    | Term :@ Term
    | L Name Type Term
    | Term ::: Type
    deriving (Show, Eq)

infixl 8 :*
infixl 7 :+
infixr 6 :->

data Type =
      Unit
    | Zero
    | Bool
    | Int
    | Char
    | String
    | Tuple [Type]
    | Record [(String,Type)]
    | Variant [(String, Type)]
    | Type :* Type
    | Type :+ Type
    | Type :-> Type
    deriving (Show, Eq)

type Context = [(Name, Type)]

data Error =
      NotInContext String Context
    | DomainMismatch Term Term
    | NoFunction Term
    | NoPair Term
    | NoSum Type
    | NoTuple Term
    | NoRecord Term
    | NoVariant Term
    | OutOfBounds Int [Term]
    | MultiDefs [(String,Term)]
    | NoIdentifier String [(String,Term)]
    | WrongTyping Term Type
    | WrongAscription Term Type
    | DefaultError
    deriving Show

-- -----------------------------------------------------------
-- typing relation

typeOf :: Context -> Term -> Either Error Type
typeOf ctx U = Right Unit
typeOf ctx (V n) = case lookup n ctx of
    Just t -> Right t
    Nothing -> Left (NotInContext n ctx)
typeOf ctx (f :@ a) = do
    f_ <- typeOf ctx f
    a_ <- typeOf ctx a
    case f_ of
        (dom_ :-> cod_) -> if dom_ == a_
                           then Right cod_
                           else Left (DomainMismatch f a)
        _ -> Left (NoFunction f)
typeOf ctx (L v t b) = (t :->) <$> typeOf ctx' b
  where
    ctx' = (v, t) : ctx
typeOf ctx (l :& r) = (:*) <$> typeOf ctx l <*> typeOf ctx r
typeOf cxt (ProjL p) = do
    p_ <- typeOf cxt p
    case p_ of
        l_ :* _ -> Right l_
        _ -> Left (NoPair p)
typeOf cxt (ProjR p) = do
    p_ <- typeOf cxt p
    case p_ of
        _ :* l_ -> Right l_
        _ -> Left (NoPair p)
typeOf ctx (InjL il s_) = case s_ of
    (l_ :+ r_) -> do
        il_ <- typeOf ctx il
        if l_ == il_ then Right il_ else Left (WrongTyping il s_)
    _ -> Left (NoSum s_)
typeOf ctx (InjR ir s_) = case s_ of
    (l_ :+ r_) -> do
        ir_ <- typeOf ctx ir
        if r_ == ir_ then Right ir_ else Left (WrongTyping ir s_)
    _ -> Left (NoSum s_)
typeOf ctx (Tup ts) = fmap Tuple . sequence . fmap (typeOf ctx) $ ts
typeOf ctx (ProjTup i t) = case t of
    Tup ts -> if length ts < i
              then typeOf ctx (ts !! i)
              else Left (OutOfBounds i ts)
    _ -> Left (NoTuple t)
typeOf ctx (Rec defs) = if unique defs then buildType Record ctx defs else Left (MultiDefs defs)
typeOf ctx (ProjRec s r) = case r of
    (Rec defs) -> either Left (typeOf ctx) $ getTerm s defs
    _ -> Left (NoRecord r)
typeOf ctx (Var defs) = if unique defs then buildType Variant ctx defs else Left (MultiDefs defs)
typeOf ctx (ProjVar s v) = case v of
    (Var defs) -> either Left (typeOf ctx) $ getTerm s defs
    _ -> Left (NoVariant v)
typeOf ctx (t ::: a_) = do
     t_ <- typeOf ctx t
     if t_ == a_ then Right t_ else Left (WrongAscription t a_)

getTerm :: String -> [(String, Term)] -> Either Error Term
getTerm n defs = case n `lookup` defs of
    Just t -> Right t
    Nothing -> Left (NoIdentifier n defs)

buildType :: ([(String, Type)] -> Type) -> Context -> [(String, Term)] -> Either Error Type
buildType con ctx = fmap con . sequence . fmap (sequence . fmap (typeOf ctx))

unique :: Eq a => [a] -> Bool
unique l = length l == length (nub l)

-- ---------------------------------------------------------------
-- helper functions

tauto :: Term -> Either Error Type
tauto = typeOf []
