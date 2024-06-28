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

translateSEW :: forall t. (MachineWidth t) => t -> Maybe Int
translateSEW 0b000 = Just 3
translateSEW 0b001 = Just 4
translateSEW 0b010 = Just 5
translateSEW 0b011 = Just 6
translateSEW _ = Nothing

translateLMUL :: forall t. (MachineWidth t) => t -> Maybe Int
translateLMUL 0b101 = Just (-3)
translateLMUL 0b110 = Just (-2)
translateLMUL 0b111 = Just (-1)
translateLMUL 0b000 = Just (0)
translateLMUL 0b001 = Just 1
translateLMUL 0b010 = Just 2
translateLMUL 0b011 = Just 3
translateLMUL _ = Nothing



translateWidth :: forall t. (MachineWidth t) => t -> Maybe Int
translateWidth 0b000 = Just 8
translateWidth 0b101 = Just 16
translateWidth 0b110 = Just 32
translateWidth 0b111 = Just 64
translateWidth _ = Nothing

translateNumFields :: MachineInt -> Maybe Int
translateNumFields 0b000 = Just 1
translateNumFields 0b001 = Just 2
translateNumFields 0b010 = Just 3
translateNumFields 0b011 = Just 4
translateNumFields 0b100 = Just 5
translateNumFields 0b101 = Just 6
translateNumFields 0b110 = Just 7
translateNumFields 0b111 = Just 8
translateNumFields _  = Nothing


legalSEW :: forall t. (MachineWidth t) => t -> t -> t -> Bool
-- We are checking that vsew (bits) <= vlmul * vlenb * 8 (everything in bits)
-- which in this case is (2 raised to (pow2SEW) <= 2 raised to (pow2LMUL) times vlenb times 8)
legalSEW vsew vlmul vlenb =
    fromMaybe False $ do
        pow2SEW <- translateSEW vsew
        pow2LMUL <- translateLMUL vlmul
        return (2 ^ pow2SEW <= ((2 ^ pow2LMUL) * vlenb * 8))

consistentRatio :: forall t. (MachineWidth t) => t -> t-> t -> t -> Bool
consistentRatio vlmul vsew vlmul' vsew' =
    fromMaybe False $ do
        pow2SEW <- translateSEW vsew
        pow2LMUL <- translateLMUL vlmul
        pow2SEW' <- translateSEW vsew'
        pow2LMUL' <- translateLMUL vlmul'
        return (pow2SEW - pow2LMUL == pow2SEW' - pow2LMUL')

-- If invalid VLMUL or VSEW, will return 0, which for general intents and purposes should be
-- okay.
computeVLMAX ::  forall t. (MachineWidth t) => t -> t -> t -> Int
computeVLMAX vlmul vsew vlenb =
    fromMaybe 0 $ do
        pow2SEW <- translateSEW vsew
        pow2LMUL <- translateLMUL vlmul
        if pow2LMUL < pow2SEW
            then return (8 * (fromIntegral vlenb) * (2 ^ (pow2LMUL - pow2SEW)))
            else return 0

computeMaxTail :: forall t. (MachineWidth t) => t -> t -> t -> Int
computeMaxTail vlmul vlenb vsew =
    fromMaybe 0 $ do
        pow2SEW <- translateSEW vsew
        pow2LMUL <- translateLMUL vlmul
        let tail =
              8 * (fromIntegral vlenb) * (2 ^ ((if pow2LMUL < 0 then 0 else pow2LMUL) - pow2SEW)) in if tail >= 1
           then return tail
           else return 0


executeVset :: forall p t. (RiscvMachine p t) => Bool -> t -> t -> Register -> p ()
executeVset noRatioCheck avl vtypei rd = do
    vlmul_old <- getCSRField Field.VLMul
    vsew_old <- getCSRField Field.VSEW
    vlenb <- getCSRField Field.VLenB
    setCSRField Field.VLMul vlmul
    setCSRField Field.VSEW vsew
    setCSRField Field.VMA vma
    setCSRField Field.VTA vta
    let vill = (if (legalSEW vsew vlmul (fromImm vlenb) && 
                    (noRatioCheck
                     || (consistentRatio (fromImm vlmul_old) (fromImm vsew_old) vlmul vsew))
                   ) then 0b0 else 0b1) 
        vlmax = computeVLMAX vlmul vsew (fromImm vlenb) 
        vl = fromIntegral (if (fromIntegral avl) <= vlmax then (fromIntegral avl) else vlmax) in
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


-- eew should be passed as # of bytes
-- underlying assumption: element requested is actually in the register
-- (to consider, if, say, accessing a register group of multiple registers)
getVRegisterElement :: forall p t. (RiscvMachine p t) => t -> VRegister -> t -> p [Int8]
getVRegisterElement eew baseReg eltIndex =
  if (and [(eew /= 1), (eew /= 2), (eew /= 4), (eew /= 8)])
  then
    raiseException 0 2 -- isInterrupt and exceptionCode arbitrary
  else
    do
      vlenb <- getCSRField Field.VLenB
      vregValue <- getVRegister baseReg
      let value = take (fromIntegral eew) (drop (fromIntegral (eltIndex * eew)) vregValue) in
        if (length value) == (fromIntegral eew)
        then return value
        else raiseException 0 2 
      
  
setVRegisterElement :: forall p t. (RiscvMachine p t) => t -> VRegister -> t -> [Int8] -> p ()
setVRegisterElement eew baseReg eltIndex value =
  if (and [(eew /= 1), (eew /= 2), (eew /= 4), (eew /= 8)])
  then
    raiseException 0 2 -- isInterrupt and exceptionCode arbitrary
  else
    do
      vlenb <- getCSRField Field.VLenB
      vregValue <- getVRegister baseReg
      let newVregValue =
            (take (fromIntegral (eltIndex * eew)) vregValue) ++
            (value) ++
            (drop (fromIntegral ((eltIndex + 1) * eew)) vregValue) in
        if (length newVregValue) == (length vregValue)
        then setVRegister baseReg newVregValue
        else raiseException 0 2

loadUntranslatedBytes :: forall p t. (RiscvMachine p t) => t -> Int -> p [Int8]
loadUntranslatedBytes memAddr numBytes = forM [0..numBytes-1] (\i ->
                                                                 do
                                                                   addr <- (translate Load 1 (memAddr + (fromIntegral i)))
                                                                   loadByte Execute addr)
                                         
storeUntranslatedBytes :: forall p t. (RiscvMachine p t) => t -> [Int8] -> p ()
storeUntranslatedBytes memAddr value = forM_ [0..(length value)-1] (\i ->
                                                                 do
                                                                   addr <- (translate Store 1 (memAddr + (fromIntegral i)))
                                                                   storeByte Execute addr (value !! i))     

testVectorBit :: [Int8] -> Int -> Bool
testVectorBit vregValue posn = testBit (vregValue !! (posn `div` 8)) (posn `mod` 8)

execute :: forall p t. (RiscvMachine p t) => InstructionV -> p ()

execute (Vsetvli rd rs1 vtypei) = 
    do
        old_vl <- getCSRField Field.VL
        if rs1 /= 0b00000 
            then
                do
                    avl <- getRegister rs1
                    executeVset False avl (fromImm vtypei) rd
            else
                if rd /= 0b00000
                -- unsure if maxBound would remain correct for wider MachineWidths
                    then executeVset False (fromImm (maxBound :: MachineInt)) (fromImm vtypei) rd
                    else executeVset True (fromImm old_vl) (fromImm vtypei) rd 

execute (Vsetvl rd rs1 rs2) = 
    do
        vtypei <- getRegister rs2
        old_vl <- getCSRField Field.VL
        if rs1 /= 0b00000 
            then
                do
                    avl <- getRegister rs1
                    executeVset False avl vtypei rd
                else
                    if rd /= 0b00000
                        then executeVset False (fromImm (maxBound :: MachineInt)) vtypei rd
                        else executeVset True (fromImm old_vl) vtypei rd
     


execute (Vsetivli rd uimm vtypei) = executeVset False (fromImm uimm) (fromImm vtypei) rd



execute (Vle width vd rs1 vm) = 
  do
    vstart <- getCSRField Field.VStart
    vlmul <- getCSRField Field.VLMul 
    vlenb <- getCSRField Field.VLenB
    vl <- getCSRField Field.VL
    vma <- getCSRField Field.VMA
    vta <- getCSRField Field.VTA
    vmask <- getVRegister 0
    let eew = fromMaybe 8 (translateWidth width) 
        maxTail = computeMaxTail vlmul vlenb (fromIntegral eew) 
        eltsPerVReg = (vlenb * 8) `div` (fromIntegral eew)
      in
      do
        forM_ [vstart..(vl-1)]
          (\i -> 
            let realVd = vd + (fromIntegral (i `div` eltsPerVReg))
                realEltIdx = (i `mod` eltsPerVReg)
            in
              do
             
                 baseMem <- getRegister rs1
                 mem <- loadUntranslatedBytes (baseMem + (fromImm (i * (fromIntegral (eew `div` 8)))))  (eew `div` 8)
                 when (vm == 0b1 || (testVectorBit vmask (fromIntegral i))) (setVRegisterElement (fromImm (fromIntegral (eew `div` 8))) (fromImm (fromIntegral realVd)) (fromImm (fromIntegral realEltIdx)) mem) 
                 when (vm == 0b0 && (not (testVectorBit vmask (fromIntegral i))) && (vma == 0b1)) (setVRegisterElement (fromImm (fromIntegral (eew `div` 8))) (fromImm (fromIntegral realVd)) (fromImm (fromIntegral realEltIdx)) (replicate (eew `div` 8) (complement (zeroBits :: Int8)) ))
          )
        when (vta == 0b1)
            (forM_ [vl..(fromIntegral (maxTail-1))]
                  (\i ->
                    let realVd = vd + (fromIntegral (i `div` eltsPerVReg))
                        realEltIdx = (i `mod` eltsPerVReg)
                    in  (setVRegisterElement (fromImm (fromIntegral (eew `div` 8))) (fromImm (fromIntegral realVd)) (fromImm (fromIntegral realEltIdx)) (replicate (eew `div` 8) (complement (zeroBits :: Int8))))))
        setCSRField Field.VStart 0b0
          
                                
execute (Vse width vd rs1 vm) =
  
  do
    vstart <- getCSRField Field.VStart
    vlmul <- getCSRField Field.VLMul 
    vlenb <- getCSRField Field.VLenB
    vl <- getCSRField Field.VL
    vma <- getCSRField Field.VMA
    vta <- getCSRField Field.VTA
    vmask <- getVRegister 0
    let eew = fromMaybe 8 (translateWidth width) 
        maxTail = computeMaxTail vlmul vlenb (fromIntegral eew) 
        eltsPerVReg = (vlenb * 8) `div` (fromIntegral eew)
      in
      do
        forM_ [vstart..(vl-1)]
          (\i -> 
            let realVd = vd + (fromIntegral (i `div` eltsPerVReg))
                realEltIdx = (i `mod` eltsPerVReg)
            in
              do
                 baseMem <- getRegister rs1
                 value <- getVRegisterElement (fromImm (fromIntegral (eew `div` 8))) (fromImm (fromIntegral realVd)) (fromImm (fromIntegral realEltIdx))
                 storeUntranslatedBytes (baseMem + (fromImm (i * (fromIntegral (eew `div` 8)))))  value
                
          )
        setCSRField Field.VStart 0b0
        
execute (Vlr vd rs1 nf) =
  let
    numFields = fromMaybe 9 $ translateNumFields nf in
  do
    vlenb <- getCSRField Field.VLenB
    when (((numFields == 1) || (numFields == 2) || (numFields == 4) || (numFields == 8)) && ((fromIntegral vd) `mod` numFields == 0))
      (forM_ [0..(numFields-1)]
      (\i ->
         do
           baseMem <- getRegister rs1
           mem <- loadUntranslatedBytes (baseMem + (fromImm (vlenb * (fromIntegral i)))) (fromIntegral vlenb)
           setVRegister (vd + (fromIntegral i)) mem
           ))
execute (Vsr vs3 rs1 nf) =
  let
    numFields = fromMaybe 9 $ translateNumFields nf in
  do
    vlenb <- getCSRField Field.VLenB
    when (((numFields == 1) || (numFields == 2) || (numFields == 4) || (numFields == 8)) && ((fromIntegral vs3) `mod` numFields == 0))
      (forM_ [0..(numFields-1)]
      (\i ->
         do
           baseMem <- getRegister rs1
           value <- getVRegister (vs3 + (fromIntegral i))
           storeUntranslatedBytes (baseMem + fromImm (vlenb * (fromIntegral i))) value
           ))
