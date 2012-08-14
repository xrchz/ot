module OpenTheory.Name (Name(Name),Component,name,nsMin,logNamespace,logComponent) where
import Control.Monad.State (evalState,get,put)

type Component = String

type Namespace = [Component]

newtype Name = Name (Namespace, Component)
  deriving (Eq, Ord)

name :: Namespace -> Component -> Name
name = curry Name

nsMin :: Component -> Name
nsMin = name []

logComponent :: Monad m => (String -> m ()) -> Component -> m ()
logComponent lr = lc where
  lc [] = return ()
  lc (x:xs) = do
    if elem x ".\"\\" then lr "\\" else return ()
    lr [x]
    lc xs

logNamespace :: Monad m => (String -> m ()) -> Namespace -> m ()
logNamespace lr = ln where
  ln [] = return ()
  ln (c:ns) = do
    lc c
    lr "."
    ln ns
  lc = logComponent lr

instance Show Name where
  show (Name (_,n)) = evalState c "" where
    c = (logComponent l n) >> get
    l s2 = get >>= (\s1 -> put (s1 ++ s2))
