{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Minimal32 where
import Program
import Utility
import CSRFile
import qualified CSRField as Field
import qualified Memory as M
import MapMemory()
import Data.Int
import Data.Word
import qualified Data.Map as S
import Control.Monad.State

data Minimal32 = Minimal32 { registers :: [Int32], csrs :: CSRFile, pc :: Int32,
                             nextPC :: Int32, mem :: S.Map Int Word8 }
               deriving (Show)

type MState = State Minimal32

type LoadFunc = MState Int32
type StoreFunc = Int32 -> MState ()

instance (Show LoadFunc) where
  show _ = "<loadfunc>"
instance (Show StoreFunc) where
  show _ = "<storefunc>"

getMTime :: LoadFunc
getMTime = fmap fromIntegral (getCSRField Field.MCycle)

-- Ignore writes to mtime.
setMTime :: StoreFunc
setMTime _ = return ()

-- Addresses for mtime/mtimecmp chosen for Spike compatibility.
mmioTable :: S.Map MachineInt (LoadFunc, StoreFunc)
mmioTable = S.fromList [(0x200bff8, (getMTime, setMTime))]
mtimecmp_addr = 0x2004000

wrapLoad :: (Integral a, Integral r, Integral r') => (S.Map Int Word8 -> a -> r) -> (a -> MState r')
wrapLoad loadFunc addr = state $ \comp -> (fromIntegral $ loadFunc (mem comp) addr, comp)
wrapStore :: (Integral a, Integral v, Integral v') => (S.Map Int Word8 -> a -> v -> S.Map Int Word8) -> (a -> v' -> MState ())
wrapStore storeFunc addr val = state $ \comp -> ((), comp { mem = storeFunc (mem comp) addr (fromIntegral val) })

instance RiscvProgram MState Int32 Word32 where
  getXLEN = return 32
  getRegister reg = state $ \comp -> (if reg == 0 then 0 else (registers comp) !! (fromIntegral reg-1), comp)
  setRegister reg val = state $ \comp -> ((), if reg == 0 then comp else comp { registers = setIndex (fromIntegral reg-1) (fromIntegral val) (registers comp) })
  getPC = state $ \comp -> (pc comp, comp)
  setPC val = state $ \comp -> ((), comp { nextPC = fromIntegral val })
  step = do
    -- Post interrupt if mtime >= mtimecmp
    mtime <- getMTime
    mtimecmp <- loadWord mtimecmp_addr
    setCSRField Field.MTIP (fromEnum (mtime >= mtimecmp))
    -- Check for interrupts before updating PC.
    mie <- getCSRField Field.MIE
    meie <- getCSRField Field.MEIE
    meip <- getCSRField Field.MEIP
    mtie <- getCSRField Field.MTIE
    mtip <- getCSRField Field.MTIP
    nPC <- state $ \comp -> (nextPC comp, comp)
    fPC <- (if (mie > 0 && ((meie > 0 && meip > 0) || (mtie > 0 && mtip > 0))) then do
              -- Disable interrupts
              setCSRField Field.MIE 0
              if (meie > 0 && meip > 0) then do
                -- Remove pending external interrupt
                setCSRField Field.MEIP 0
                setCSRField Field.MCauseCode 11 -- Machine external interrupt.
              else if (mtie > 0 && mtip > 0) then
                setCSRField Field.MCauseCode 7 -- Machine timer interrupt.
              else return ()
              -- Save the PC of the next (unexecuted) instruction.
              setCSRField Field.MEPC nPC
              trapPC <- getCSRField Field.MTVecBase
              return (fromIntegral trapPC * 4)
            else return nPC)
    state $ \comp -> ((), comp { pc = fPC })
  -- Wrap Memory instance:
  loadByte = wrapLoad M.loadByte
  loadHalf = wrapLoad M.loadHalf
  loadWord = wrapLoad M.loadWord
  storeByte = wrapStore M.storeByte
  storeHalf = wrapStore M.storeHalf
  storeWord = wrapStore M.storeWord
  -- CSRs:
  getCSRField field = state $ \comp -> (getField field (csrs comp), comp)
  setCSRField field val = state $ \comp -> ((), comp { csrs = setField field (fromIntegral val) (csrs comp) })
  -- Unimplemented:
  loadDouble _ = return 0
  storeDouble _ _ = return ()