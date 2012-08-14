import qualified Data.Map as Map (empty)
import Data.Set (fromList)
import Control.Monad.State (liftIO,evalStateT)
import System.IO (stdin,stdout)
import Prelude hiding (map)
import OpenTheory.Proof (Proof(Axiom,EqMp))
import OpenTheory.Object (Object(OThm))
import OpenTheory.Read (ReadState(ReadState),readArticle,defaultHandler,thmsOnEOF,putStack)
import qualified OpenTheory.Read as R (ReadState(..))
import OpenTheory.Write (WriteState(WriteState),logThm)
import qualified OpenTheory.Write as W (WriteState(..))

main :: IO ()
main = evalStateT m rs where
  m = do
    thms <- readArticle (\h c s -> putStack $ (OThm $ Axiom (fromList h) c) : s) defaultHandler thmsOnEOF
    liftIO $ evalStateT (output thms) ws where
      ws = WriteState {W.handle=stdout, W.map=Map.empty}
      output [th1,th2] = logThm (EqMp th1 th2)
      output ls = error ("got bad thms: "++show ls)
  rs = ReadState {R.handle=stdin, R.map=Map.empty, R.stack=[], R.thms=[]}
