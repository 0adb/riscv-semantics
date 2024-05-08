{-# LANGUAGE ScopedTypeVariables #-}
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

translateSEW :: MachineInt -> Maybe Int64
translateSEW 0b000 = Just 3
translateSEW 0b001 = Just 4
translateSEW 0b010 = Just 5
translateSEW 0b011 = Just 6
translateSEW _ = Nothing

translateLMUL :: MachineInt -> Maybe Int64
translateLMUL 0b101 = Just -3
translateLMUL 0b110 = Just -2
translateLMUL 0b111 = Just -1
translateLMUL 0b000 = Just 0
translateLMUL 0b001 = Just 1
translateLMUL 0b010 = Just 2
translateLMUL 0b011 = Just 3
translateLMUL _ = Nothing


legalSEW :: MachineInt -> MachineInt -> MachineInt -> Bool 
-- We are checking that vsew (bits) <= vlmul * vlenb * 8 (everything in bits)
-- which in this case is (2 raised to (pow2SEW) <= 2 raised to (pow2LMUL) times vlenb times 8)
legalSEW vsew vlmul vlenb = 
    fromMaybe False 
        { do
            {
                pow2SEW <- translateSEW vsew
                pow2LMUL <- translateLMUL vlmul
                return (2 ^ pow2SEW <= ((2 ^ pow2LMUL) * vlenb * 8))
            }
        }


consistentRatio :: MachineInt -> MachineInt -> MachineInt -> MachineInt -> Bool 
consistentRatio vlmul vsew vlmul' vsew' = 
    fromMaybe False 
        { do
            {
                pow2SEW <- translateSEW vsew
                pow2LMUL <- translateLMUL vlmul 
                pow2SEW' <- translateSEW vsew'
                pow2LMUL' <- translateLMUL vlmul'
                return (pow2SEW - pow2LMUL == pow2SEW' - pow2LMUL') 
            }
        }

-- If invalid, will return 0, which for general intents and purposes should be
-- okay.
computeVLMAX :: MachineInt -> MachineInt -> MachineInt -> MachineInt
computeVLMAX vlmul vsew vlenb =
    fromMaybe 0 
    {
        do 
        {
            pow2SEW <- translateSEW vsew
            pow2LMUL <- translateLMUL vlmul
            if pow2LMUL < pow2SEW
                then return (8 * vlenb * (2 ^ (pow2LMUL - pow2SEW)))   
                else return 0 
        }
    }

execute :: forall p t. (RiscvMachine p t) => InstructionV -> p ()

execute Vsetvli rd rs1 vtypei = do
    vlmul_old <- getCSRField Field.VLMul
    vsew_old <- getCSRField Field.VSEW
    vlenb <- getCSRField Field.VLenB
    setCSRField Field.VLMul vlmul
    setCSRField Field.VSEW vsew
    setCSRField Field.VMA vma
    setCSRField Field.VTA vta
    if rs1 != 0b00000 
        then
            setCSRField Field.VIll (if (legalSEW vsew vlmul vlenb) then 0b0 else 0b1)
            avl <- getRegister rs1
            if 
                avl <= computeVLMAX vlmul vsew vlenb
            then
                setRegister rd avl
                setCSRField Field.VL avl
                setCSRField Field.VStart 0b0
            else
                setRegister rd (computeVLMAX vlmul vsew vlenb)
                setCSRField Field.VL (computeVLMAX vlmul vsew vlenb)
                setCSRField Field.VStart 0b0
            -- Technically, the extension is less specified than this
            -- on setting VL (the number of vector elements consumed per operation). 
            -- This choice is more or less arbitrary within
            -- conditions in spec.
            -- Also I'm realizing as I write this that I am not 
            -- truncating to the size of the register. Should I be?
        else if rd != 0b00000
            then
                setCSRField Field.VIll (if (legalSEW vsew vlmul vlenb) then 0b0 else 0b1)
                setRegister rd (computeVLMAX vlmul vsew vlenb)
                setCSRField Field.VL (computeVLMAX vlmul vsew vlenb)
                setCSRField Field.VStart 0b0
            else 
                if ((legalSEW vsew vlmul vlenb) && (consistentRatio vlmul_old vsew_old vlmul vsew))
                then 
                    setCSRField Field.VIll 0b0
                    setCSRField Field.VStart 0b0
                else 
                    setCSRField Field.VIll 0b1
                    setRegister rd 0b0
                    setCSRField Field.VL 0b0
                    setCSRField Field.VStart 0b0
    where
        vlmul = (bitSlice vtypei 0 3)
        vsew = (bitSlice vtypei 3 6)
        vta = (bitSlice vtypei 6 7)
        vma = (bitSlice vtypei 7 8)


execute Vle width vd rs1 vm = setVRegister 0 [0]
execute Vse width vd rs1 vm = setVRegister 0 [0]
execute Vlr vd rs1 nf = setVRegister 0 [0]
execute Vsr vs3 rs1 nf = setVRegister 0 [0]