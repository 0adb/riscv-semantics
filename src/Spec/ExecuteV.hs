{-# LANGUAGE ScopedTypeVariables, BinaryLiterals #-}
module Spec.ExecuteV where
import Spec.Decode
import Spec.Machine
import Utility.Utility
import Spec.VirtualMemory
import Data.Bits hiding (Xor, And, Or)
import Data.Int
import Data.Word
import Data.Bool
import Data.Maybe
import Control.Monad
import Prelude
import qualified Spec.CSRField as Field

translateSEW :: MachineInt -> Maybe Int64
translateSEW 0b000 = Just 3
translateSEW 0b001 = Just 4
translateSEW 0b010 = Just 5
translateSEW 0b011 = Just 6
translateSEW _ = Nothing

translateLMUL :: MachineInt -> Maybe Int64
translateLMUL 0b101 = Just (-3)
translateLMUL 0b110 = Just (-2)
translateLMUL 0b111 = Just (-1)
translateLMUL 0b000 = Just 0
translateLMUL 0b001 = Just 1
translateLMUL 0b010 = Just 2
translateLMUL 0b011 = Just 3
translateLMUL _ = Nothing


legalSEW :: MachineInt -> MachineInt -> MachineInt -> Bool
-- We are checking that vsew (bits) <= vlmul * vlenb * 8 (everything in bits)
-- which in this case is (2 raised to (pow2SEW) <= 2 raised to (pow2LMUL) times vlenb times 8)
legalSEW vsew vlmul vlenb =
    fromMaybe False $ do
        pow2SEW <- translateSEW vsew
        pow2LMUL <- translateLMUL vlmul
        return (2 ^ pow2SEW <= ((2 ^ pow2LMUL) * vlenb * 8))


consistentRatio :: MachineInt -> MachineInt -> MachineInt -> MachineInt -> Bool
consistentRatio vlmul vsew vlmul' vsew' =
    fromMaybe False $ do
        pow2SEW <- translateSEW vsew
        pow2LMUL <- translateLMUL vlmul
        pow2SEW' <- translateSEW vsew'
        pow2LMUL' <- translateLMUL vlmul'
        return (pow2SEW - pow2LMUL == pow2SEW' - pow2LMUL')

-- If invalid VLMUL or VSEW, will return 0, which for general intents and purposes should be
-- okay.
computeVLMAX :: MachineInt -> MachineInt -> MachineInt -> MachineInt
computeVLMAX vlmul vsew vlenb =
    fromMaybe 0 $ do
        pow2SEW <- translateSEW vsew
        pow2LMUL <- translateLMUL vlmul
        if pow2LMUL < pow2SEW
            then return (8 * vlenb * (2 ^ (pow2LMUL - pow2SEW)))
            else return 0


executeVset :: forall p t. (RiscvMachine p t) => Bool -> MachineInt -> MachineInt -> Register -> p ()
executeVset noRatioCheck avl vtypei rd = do
    vlmul_old <- getCSRField Field.VLMul
    vsew_old <- getCSRField Field.VSEW
    vlenb <- getCSRField Field.VLenB
    setCSRField Field.VLMul vlmul
    setCSRField Field.VSEW vsew
    setCSRField Field.VMA vma
    setCSRField Field.VTA vta
    let vill = (if (legalSEW vsew vlmul vlenb && 
                    (noRatioCheck
                     || (consistentRatio vlmul_old vsew_old vlmul vsew))
                   ) then 0b0 else 0b1) 
        vlmax = computeVLMAX vlmul vsew vlenb 
        vl = if avl <= vlmax  then avl else vl in
        do
          setCSRField Field.VL vl
          setCSRField Field.VStart 0b0
          setCSRField Field.VIll vill
          unless (rd == 0b0) (setRegister rd vl)
    where
        vlmul = (bitSlice vtypei 0 3)
        vsew = (bitSlice vtypei 3 6)
        vta = (bitSlice vtypei 6 7)
        vma = (bitSlice vtypei 7 8)

execute :: forall p t. (RiscvMachine p t) => InstructionV -> p ()

execute (Vsetvli rd rs1 vtypei) = 
    do
        old_vl <- getCSRField Field.VL
        if rs1 != 0b00000 
            then
                do
                    avl <- getRegister rs1
                    executeVset False avl vtypei
            else
                if rd != 0b00000
                    then executeVset False (maxBound :: MachineInt) vtypei
                    else executeVset True old_vl vtypei  

execute (Vsetvl rd rs1 rs2) = 
    do
        vtypei <- getRegister rs2
        old_vl <- getCSRField Field.VL
        if rs1 != 0b00000 
            then
                do
                    avl <- getRegister rs1
                    executeVset False avl vtypei 
                else
                    if rd != 0b00000
                        then executeVset False (maxBound :: MachineInt) vtypei
                        else executeVset True old_vl vtypei
     


execute (Vsetivli rd uimm vtypei) = executeVset False uimm vtypei

execute Vle width vd rs1 vm = setVRegister 0 [0]
execute Vse width vd rs1 vm = setVRegister 0 [0]
execute Vlr vd rs1 nf = setVRegister 0 [0]
execute Vsr vs3 rs1 nf = setVRegister 0 [0]
