{-# LANGUAGE DeriveFunctor #-}

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad
type Name = String  -- x ∈ Name
data Exp            -- e
  = Var Name        --   ::= x
  | App Exp Exp     --    |  e1 e2
  | Lam Name Exp    --    |  λx.e

-- |
-- >>> takeD 10000 $ eval Map.empty omega
-- Nothing
omega :: Exp
omega = Lam "x" (Var "x" `App` Var "x") `App` Lam "y" (Var "y" `App` Var "y")

-- |
-- >>> takeD 10000 $ eval Map.empty idid
-- Just Fun
-- >>> eval Map.empty idid
-- Step (Ret Fun)
idid :: Exp
idid = Lam "x" (Var "x") `App` Lam "y" (Var "y")

data T a = Ret !a | Step (T a) deriving (Show, Functor)
data Value = Fun (D -> D) | Stuck
type D = T Value
instance Show Value where
  show Fun{} = "Fun"
  show Stuck = "Stuck"

instance Applicative T where
  pure = Ret
  (<*>) = ap
instance Monad T where
  Ret a  >>= k = k a
  Step d >>= k = Step (d >>= k)

diverge :: D
diverge = Step diverge

takeD :: Int -> T a -> Maybe a
takeD _ (Ret a)  = Just a
takeD 0 _        = Nothing
takeD n (Step d) = takeD (n-1) d

eval :: Map Name D -> Exp -> D
eval env (Var x) = case Map.lookup x env of
  Just d  -> d
  Nothing -> return Stuck
eval env (Lam x e) = return (Fun (\d -> eval (Map.insert x (Step d) env) e))
eval env (App e1 e2) = eval env e1 >>= \v -> case v of
  Fun f -> f (eval env e2)
  _     -> return Stuck

