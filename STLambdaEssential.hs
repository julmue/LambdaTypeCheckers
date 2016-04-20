module STLambdaEssential where

infixl 7 :@
infixl 9 :&
infix 0 :::

data Term
    = U                         -- U    : Unit
    -- Product
      -- introduction rule
    | Term :& Term
      -- elimination rules
    | ProjL Term                -- PL   : Pair a b -> a (left projection)
    | ProjR Term                -- RR   : Pair a b -> b (right projection)
    -- Sum
      -- introduction rules
    | InjL Term Type            -- IL   : a -> Sum a b (left injection)
    | InjR Term Type            -- IR   : b -> Sum a b (right injection)
      -- elimination rule (case of)
    | Case Term Term Term
    -- Lambda Calculus
    | V String                  -- V      (variable)
    | Term :@ Term              -- :@     (application)
    | L String Type Term        -- L      (abstraction)
    -- Ascriptions
    | Term ::: Type             -- (:::)  (ascription
    deriving (Show, Eq)

infixl 8 :*
infixl 7 :+
infixr 6 :->

data Type =
      Unit                      -- aka "The Truth" aka "Verum" aka "Top"
    | Zero                      -- aka "The False" aka "Falsum" aka "Bottom"
    | Type :* Type              -- Product type
    | Type :+ Type              -- Sum type
    | Type :-> Type             -- Arrow type (aka Exponentials; infinite type family)
    | P                         -- uninterpreted base types
    | Q
    | R
    | S
    | T
    deriving (Show, Eq)

type Name = String

type Context = [(Name, Type)]

data Error =
      NotInContext String Context
    | DomainMismatch Term Term
    | NoFunction Term
    | NoPair Term
    | NoSum Type
    | WrongTyping Term Type
    | WrongAscription Term Type
    | DefaultError
    deriving Show

-- -----------------------------------------------------------
-- typing relation

typeOf :: Context -> Term -> Either Error Type
-- unit
typeOf ctx U = Right Unit
-- variables
typeOf ctx (V n) = case lookup n ctx of
    Just t -> Right t
    Nothing -> Left (NotInContext n ctx)
-- application
typeOf ctx (f :@ a) = do
    f_ <- typeOf ctx f
    a_ <- typeOf ctx a
    case f_ of
        (dom_ :-> cod_) -> if dom_ == a_
                           then Right cod_
                           else Left (DomainMismatch f a)
        _ -> Left (NoFunction f)
-- abstraction
typeOf ctx (L v t b) = (t :->) <$> typeOf ctx' b
  where
    ctx' = (v, t) : ctx
-- product
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
-- sum
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
-- ascription
typeOf ctx (t ::: a_) = do
     t_ <- typeOf ctx t
     if t_ == a_ then Right t_ else Left (WrongAscription t a_)

-- ---------------------------------------------------------------
-- helper functions
tauto :: Term -> Either Error Type
tauto = typeOf []
