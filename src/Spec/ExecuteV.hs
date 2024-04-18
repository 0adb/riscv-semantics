{-# LANGUAGE ScopedTypeVariables #-}
module Spec.ExecuteV where
import Spec.Decode
import Spec.Machine
import Utility.Utility
import Spec.VirtualMemory
import Data.Bits hiding (Xor, And, Or)
import Data.Int
import Data.Word
import Control.Monad
import Prelude


execute :: forall p t. (RiscvMachine p t) => InstructionV -> p ()