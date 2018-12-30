import Strictness
import Control.Monad

a, b, c, d, e, f, g :: Expr
(a:b:c:d:e:f:g:_) = map (Var . (:[])) ['a'..]

exprs :: [Expr]
exprs =
  [ If a b c
  , If a b b
  , If a (App f b) (App f c)
  , App (Lam "b" b) a
  , Let (NonRec ("f", Lam "b" b)) (App f b)
  , Let (Rec [("f", Lam "b" (App f b))]) (App f a)
  , Let (Rec [("f", Lam "b" (If b c (App f b)))]) (App f a)
  ]


main = forM_ exprs $ \e -> do
  print e
  print (analyse e)
  putStrLn "--------"
