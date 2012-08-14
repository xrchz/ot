import qualified Data.Map as Map (empty)
import Control.Monad.State (evalStateT)
import System.IO (stdin,stdout)
import OpenTheory.Proof (Proof(EqMp))
import OpenTheory.Read (RM,ReadState(ReadState),readArticle,defaultAxiom,defaultHandler,thmsOnEOF)
import qualified OpenTheory.Read as R (ReadState(..))
import OpenTheory.Write (WM,WriteState(WriteState),logThm)
import qualified OpenTheory.Write as W (WriteState(..))
import Prelude hiding (map,read)

read :: RM [Proof]
read = readArticle defaultAxiom defaultHandler thmsOnEOF

write :: [Proof] -> WM ()
write [th1,th2] = logThm $ (EqMp th1 th2)
write ls = error ("got bad thms: "++show ls)

main :: IO ()
main = do
  let rs = ReadState {R.handle=stdin, R.map=Map.empty, R.stack=[], R.thms=[]}
  thms <- evalStateT read rs
  let ws = WriteState {W.handle=stdout, W.map=Map.empty}
  evalStateT (write thms) ws
