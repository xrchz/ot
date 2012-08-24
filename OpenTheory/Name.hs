-- |
-- Module      : $Header$
-- Copyright   : 2012, Ramana Kumar
-- License     : GPL
-- 
-- Maintainer  : ramana@xrchz.net
-- Stability   : experimental
-- Portability : portable
-- 
-- OpenTheory names (used to name constants and variables).
module OpenTheory.Name (
  Name(Name), Namespace(Namespace), Component(Component),
  name, namespace,
  nsMin) where
import Text.Read (Read(readPrec))
import Text.ParserCombinators.ReadPrec (lift,readPrec_to_P,minPrec)
import Text.ParserCombinators.ReadP (many,char,satisfy,(<++),endBy,eof)

newtype Component = Component String
  deriving (Eq, Ord)

newtype Namespace = Namespace [Component]
  deriving (Eq, Ord)

-- |
-- Names consist of a namespace and a base component.
-- For example the true boolean constant is named by @Data.Bool.T@.
-- Here, @Data.Bool@ is the namespace, and @T@ is the base component.
newtype Name = Name (Namespace, Component)
  deriving (Eq, Ord)

-- |A convenience function for creating names.
name :: Namespace -> String -> Name
name ns s = Name (ns, Component s)

-- |A convenience function for creating namespaces.
namespace :: [String] -> Namespace
namespace = Namespace . map Component

-- |Generates a name in the @min@ (empty) namespace.
nsMin :: String -> Name
nsMin = name (namespace [])

escaped :: Char -> Bool
escaped = flip elem ".\'\\"

instance Show Component where
  showsPrec _ (Component s) = showStr s where
    showStr [] = id
    showStr (x:xs) = escape . showChar x . showStr xs where
      escape = if escaped x then showChar '\\' else id

instance Read Component where
  readPrec = lift readString >>= return . Component where
    readString = many $ (char '\\' >> satisfy escaped) <++ satisfy (not . escaped)

instance Show Namespace where
  showsPrec _ (Namespace []) = id
  showsPrec d (Namespace (c:cs)) =
    showsPrec d c . showChar '.' . showsPrec d (Namespace cs)

instance Read Namespace where
  readPrec = lift readComponents >>= return . Namespace where
    readComponents = endBy (readPrec_to_P readPrec minPrec) (char '.')

instance Show Name where
  showsPrec d (Name (ns,c)) = showsPrec d ns . showsPrec d c

instance Read Name where
  readPrec = lift $ do
    ns <- readPrec_to_P readPrec minPrec
    c <- readPrec_to_P readPrec minPrec
    eof
    return $ Name (ns,c)
