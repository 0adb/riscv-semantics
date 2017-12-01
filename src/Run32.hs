module Main where
import System.IO
import System.Environment
import System.Exit
import Data.Int
import Data.Word
import Utility
import Program
import Minimal32
import MMIO
import qualified CSRField as Field
import CSRFile
import Decode
import Execute32
import Control.Monad.Trans
import Control.Monad.State
import qualified Data.Map as S
import Debug.Trace

processLine :: String -> [Word8] -> [Word8]
processLine ('@':xs) l = l ++ take (4*(read ("0x" ++ xs) :: Int) - (length l)) (repeat 0)
processLine s l = l ++ splitWord (read ("0x" ++ s) :: Word32)

readHexFile :: Handle -> [Word8] -> IO [Word8]
readHexFile h l = do
  s <- hGetLine h
  done <- hIsEOF h
  if (null s)
    then return l
    else if done
         then return $ processLine s l
         else readHexFile h (processLine s l)

checkInterrupt :: IO Bool
checkInterrupt = do
  ready <- hReady stdin
  if ready then do
    c <- hLookAhead stdin
    if c == '!' then do
      _ <- getChar
      _ <- getChar
      return True
    else return False
  else return False

helper :: IOState Minimal32 Int32
helper = do
  pc <- getPC
  inst <- loadWord pc
  if inst == 0x6f -- Stop on infinite loop instruction.
    then do
        cycles <- getCSRField Field.MCycle
        trace ("Cycles: " ++ show cycles) (return ())
        instret <- getCSRField Field.MInstRet
        trace ("Insts: " ++ show instret) (return ())
        getRegister 10
    else do
    setPC (pc + 4)
    size <- getXLEN
    execute (decode size $ fromIntegral inst)
    interrupt <- liftIO checkInterrupt
    if interrupt then do
      -- Signal interrupt by setting MEIP high.
      setCSRField Field.MEIP 1
    else return ()
    step
    helper

runProgram :: Minimal32 -> IO (Int32, Minimal32)
runProgram = runStateT helper

runFile :: String -> IO Int32
runFile f = do
  h <- openFile f ReadMode
  m <- readHexFile h []
  let c = Minimal32 { registers = (take 31 $ repeat 0), csrs = (resetCSRFile 32), pc = 0x200, nextPC = 0,
                      mem = S.fromList $ zip [0..] (m ++ (take (65520 - length m) $ repeat (0::Word8))) } in
    fmap fst $ runProgram c

main :: IO ()
main = do
  file:_ <- getArgs
  retval <- runFile file
  exitWith (if retval == 0 then ExitSuccess else ExitFailure $ fromIntegral retval)
