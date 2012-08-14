import qualified Data.Map as Map (empty)
import Data.Set (fromList)
import Control.Monad.State (evalStateT)
import System.IO (Handle,stdin,stdout,hClose)
import System.IO (openFile,IOMode(..))
import OpenTheory.Proof (Proof(Axiom,EqMp))
import OpenTheory.Object (Object(OThm))
import OpenTheory.Read (RM,ReadState(ReadState),readArticle,defaultHandler,thmsOnEOF,putStack)
import qualified OpenTheory.Read as R (ReadState(..))
import OpenTheory.Write (WM,WriteState(WriteState),logThm)
import qualified OpenTheory.Write as W (WriteState(..))
import Prelude hiding (map,read)

getInput :: IO Handle
-- getInput = return stdin
getInput = openFile "/tmp/demo1.art" ReadMode
getOutput :: IO Handle
-- getOutput = return stdout
getOutput = openFile "/tmp/demo2.art" WriteMode

read :: RM [Proof]
read = readArticle (\h c s -> putStack $ (OThm $ Axiom (fromList h) c) : s) defaultHandler thmsOnEOF

write :: [Proof] -> WM ()
write [th1,th2] = logThm $ (EqMp th1 th2)
write ls = error ("got bad thms: "++show ls)

main :: IO ()
main = do

  inp <- getInput
  let rs = ReadState {R.handle=inp, R.map=Map.empty, R.stack=[], R.thms=[]}
  thms <- evalStateT read rs
  hClose inp

  out <- getOutput
  let ws = WriteState {W.handle=out, W.map=Map.empty}
  evalStateT (write thms) ws
  hClose out
