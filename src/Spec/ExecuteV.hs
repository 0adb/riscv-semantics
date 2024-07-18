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
import Debug.Trace

take_machineInt :: forall t. MachineInt -> [t] -> [t]
take_machineInt i l = take (fromIntegral i) l

drop_machineInt :: forall t. MachineInt -> [t] -> [t]
drop_machineInt i l = drop (fromIntegral i) l

replicate_machineInt :: forall t. MachineInt -> t -> [t]
replicate_machineInt c v = replicate (fromIntegral c) v

zeroToExclusive_machineInt :: forall t. (MachineWidth t) => MachineInt -> [t]
zeroToExclusive_machineInt max = map  (fromImm) [0..(max-1)]

length_machineInt :: forall t. [t] -> MachineInt
length_machineInt l = (fromIntegral (length l))

maybeIndex_machineInt :: forall t. [t] -> MachineInt -> Maybe t
maybeIndex_machineInt l idx = if (length_machineInt l > idx) then (Just (l !! (fromIntegral idx))) else Nothing

testBit_machineInt :: forall a. Bits a => a -> MachineInt -> Bool
testBit_machineInt b idx = testBit b (fromIntegral idx)

int8_toWord8 :: Int8 -> Word8
int8_toWord8 n = (fromIntegral:: Int8 -> Word8) n

word8_toInt8 :: Word8 -> Int8
word8_toInt8 n = (fromIntegral:: Word8 -> Int8) n


translateLMUL :: forall t. (MachineWidth t) => t -> Maybe MachineInt
translateLMUL 0b101 = Just (-3)
translateLMUL 0b110 = Just (-2)
translateLMUL 0b111 = Just (-1)
translateLMUL 0b000 = Just (0)
translateLMUL 0b001 = Just 1
translateLMUL 0b010 = Just 2
translateLMUL 0b011 = Just 3
translateLMUL _ = Nothing



translateWidth_Vtype :: forall t. (MachineWidth t) => t -> Maybe MachineInt
translateWidth_Vtype 0b000 = Just 3
translateWidth_Vtype 0b001 = Just 4
translateWidth_Vtype 0b010 = Just 5
translateWidth_Vtype 0b011 = Just 6
translateWidth_Vtype _ = Nothing

translateWidth_Inst :: forall t. (MachineWidth t) => t -> Maybe MachineInt
translateWidth_Inst 0b000 = Just 3
translateWidth_Inst 0b101 = Just 4
translateWidth_Inst 0b110 = Just 5
translateWidth_Inst 0b111 = Just 6
translateWidth_Inst _ = Nothing

translateNumFields :: MachineInt -> Maybe MachineInt
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
        pow2SEW <- translateWidth_Vtype vsew
        pow2LMUL <- translateLMUL vlmul
        trace ("pow2SEW " ++ show pow2SEW ++ " pow2LMUL "  ++ show pow2LMUL)$ (return (2 ^ pow2SEW <= ((2 ^ pow2LMUL) * vlenb * 8)))

consistentRatio :: forall t. (MachineWidth t) => t -> t-> t -> t -> Bool
consistentRatio vlmul vsew vlmul' vsew' =
    fromMaybe False $ do
        pow2SEW <- translateWidth_Vtype vsew
        pow2LMUL <- translateLMUL vlmul
        pow2SEW' <- translateWidth_Vtype vsew'
        pow2LMUL' <- translateLMUL vlmul'
        return (pow2SEW - pow2LMUL == pow2SEW' - pow2LMUL')

-- If invalid VLMUL or VSEW, will return 0, which for general intents and purposes should be
-- okay.
-- Not implementing here the restriction that LMUL < SEW_min/ELEN is undefined behavior. 
computeVLMAX ::  forall t. (MachineWidth t) => t -> t -> t -> t
computeVLMAX vlmul vsew vlenb =
  fromMaybe 0 $ do
        pow2SEW <- translateWidth_Vtype vsew
        pow2LMUL <- translateLMUL vlmul
        (let exp = 3 + pow2LMUL - pow2SEW in
            if exp >= 0 then
              return (vlenb * (2 ^ (exp)))
            else
              return (vlenb `div` (2 ^ (-exp))))

computeMaxTail :: forall t. (MachineWidth t) => t -> t -> t -> t
computeMaxTail vlmul vlenb vsew =
    fromMaybe 0 $ do
        pow2SEW <- translateWidth_Vtype vsew
        pow2LMUL <- translateLMUL vlmul
        let tail =
              8 * ( vlenb) * (2 ^ ((if pow2LMUL < 0 then 0 else pow2LMUL) - pow2SEW)) in if tail >= 1
           then return tail
           else return 0


executeVset :: forall p t. (RiscvMachine p t) => Bool -> t -> t -> Register -> p ()
executeVset noRatioCheck avl vtypei rd = do
    vlmul_old <- getCSRField Field.VLMul
    vsew_old <- getCSRField Field.VSEW
    vlenb <- getCSRField Field.VLenB
    trace ("no Ratio Check " ++ show noRatioCheck) $ setCSRField Field.VLMul vlmul
    setCSRField Field.VSEW vsew
    setCSRField Field.VMA vma
    setCSRField Field.VTA vta
    
    let vill = (if (legalSEW vsew vlmul (fromImm vlenb) && 
                    (noRatioCheck
                     || (consistentRatio (fromImm vlmul_old) (fromImm vsew_old) vlmul vsew))
                   ) then 0b0 else 0b1) 
        vlmax = computeVLMAX vlmul vsew (fromImm vlenb) 
        vl =  (if ( avl) <= vlmax then ( avl) else vlmax) in
        do
          trace ("vl set, avl and vlmax are " ++ show (fromIntegral vl) ++ " " ++ show (fromIntegral avl) ++ " " ++ show (fromIntegral vlmax)) $ setCSRField Field.VL vl 
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
getVRegisterElement :: forall p t. (RiscvMachine p t) => MachineInt -> VRegister -> MachineInt -> p [Int8]
getVRegisterElement eew baseReg eltIndex =
  if (and [(eew /= 1), (eew /= 2), (eew /= 4), (eew /= 8)])
  then
    raiseException 0 2 -- isInterrupt and exceptionCode arbitrary
  else
    do
      vlenb <- getCSRField Field.VLenB
      vregValue <- getVRegister baseReg
      let value = take_machineInt ( eew) (drop_machineInt ( (eltIndex * eew)) vregValue) in
        if (length_machineInt value) == ( eew)
        then (trace ("value loaded from vregister: " ++ show value ++ "at vregister " ++ show baseReg ++ " elt idx " ++ show eltIndex)) $ return value
        else raiseException 0 2 
      
  
setVRegisterElement :: forall p t. (RiscvMachine p t) => MachineInt -> VRegister -> MachineInt -> [Int8] -> p ()
setVRegisterElement eew baseReg eltIndex value =
  ((trace ("eew, baseReg, eltIndex, value: " ++ show eew ++ " " ++ show baseReg ++ " " ++ show eltIndex ++ " " ++ show value)) $ (
  if (and [(eew /= 1), (eew /= 2), (eew /= 4), (eew /= 8)])
  then
    raiseException 0 2 -- isInterrupt and exceptionCode arbitrary
  else
    do
      vlenb <- getCSRField Field.VLenB
      vregValue <- getVRegister baseReg
      let newVregValue =
            (take_machineInt ( (eltIndex * eew)) vregValue) ++
            (value) ++
            (drop_machineInt ( ((eltIndex + 1) * eew)) vregValue) in
        if (length newVregValue) == (length vregValue)
        then (trace ("value stored to vregister: " ++ show newVregValue ++ " at register idx " ++ show baseReg)) $ (setVRegister baseReg newVregValue)
        else raiseException 0 2))

loadUntranslatedBytes :: forall p t. (RiscvMachine p t) => t -> MachineInt -> p [Int8]
loadUntranslatedBytes memAddr numBytes = (trace ("memAddr, numBytes " ++ show (fromIntegral memAddr) ++ " " ++ show (fromIntegral numBytes)) ) $ (forM (zeroToExclusive_machineInt numBytes) (\i ->
                                                                 do
                                                                   addr <- (translate Load 1 (memAddr + (fromImm i)))
                                                                   trace ("loading from address" ++ show (fromIntegral addr)) $ loadByte Execute addr))
                                         
storeUntranslatedBytes :: forall p t. (RiscvMachine p t) => t -> [Int8] -> p ()
storeUntranslatedBytes memAddr value = forM_ (zeroToExclusive_machineInt (length_machineInt value)) (\i ->
                                                                 do
                                                                   addr <- (translate Store 1 (memAddr + (fromImm i)))
                                                                   trace ("storing at address " ++ (show (fromIntegral addr)) ++ " the value " ++ show value ++ " and index " ++ show i) $ (storeByte Execute addr (fromMaybe 0 (maybeIndex_machineInt value i)))
                                                                                                    ) 


testVectorBit :: [Int8] -> MachineInt -> Bool
testVectorBit vregValue posn = testBit_machineInt
                               (fromMaybe 0
                                (maybeIndex_machineInt vregValue  (posn `div` 8)))
                               ((posn `mod` 8))

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
    let eew = 2 ^ (fromMaybe 8 (translateWidth_Inst width))
        maxTail = computeMaxTail vlmul vlenb (eew) 
        eltsPerVReg = (vlenb * 8) `div` (eew)
      in
      do
        (trace ("vstart " ++ show (fromIntegral vstart) ++ " vl " ++ show (fromIntegral vl))) $ (forM_ [vstart..(vl-1)]
          (\i ->
            let realVd = vd + ( (i `div` eltsPerVReg))
                realEltIdx = (i `mod` eltsPerVReg)
            in
              (trace ("real vd, real elt idx " ++ show realVd ++ " " ++ show realEltIdx))
              $ (do
             
                 baseMem <- getRegister rs1
                 mem <- loadUntranslatedBytes (baseMem + (fromImm (i * (eew `div` 8))))  (eew `div` 8)
                 when (vm == 0b1 || (testVectorBit vmask ( i)))  ((trace "got to this spot") $ (setVRegisterElement (fromImm ( (eew `div` 8))) (fromImm ( realVd)) (fromImm ( realEltIdx)) mem))
                 when (vm == 0b0 && (not (testVectorBit vmask ( i))) && (vma == 0b1)) (setVRegisterElement (fromImm ( (eew `div` 8))) (fromImm ( realVd)) (fromImm ( realEltIdx)) (replicate_machineInt (eew `div` 8) (complement (zeroBits :: Int8)) ))
                 ((trace ("mem loaded " ++ show mem)) $ (setCSRField Field.VStart i)))
          ))
        when (vta == 0b1)
            (forM_ [vl..( (maxTail-1))]
                  (\i ->
                    let realVd = vd + ( (i `div` eltsPerVReg))
                        realEltIdx = (i `mod` eltsPerVReg)

                    in  (setVRegisterElement (fromImm ( (eew `div` 8))) (fromImm ( realVd)) (fromImm ( realEltIdx)) (replicate_machineInt (eew `div` 8) (complement (zeroBits :: Int8))))))
        setCSRField Field.VStart 0b0
                  

--   Vaddvv { vd :: VRegister, vs1 :: VRegister, vs2 :: VRegister, vm :: MachineInt } |
execute (Vaddvv vd vs1 vs2 vm) =
  do
    vstart <- getCSRField Field.VStart
    vlmul <- getCSRField Field.VLMul 
    vlenb <- getCSRField Field.VLenB
    vl <- getCSRField Field.VL
    vma <- getCSRField Field.VMA
    vta <- getCSRField Field.VTA
    vsew <- getCSRField Field.VSEW
    vmask <- getVRegister 0

    let eew = 2 ^ (fromMaybe 0 (translateWidth_Vtype vsew)) 
        maxTail = computeMaxTail vlmul vlenb (eew) 
        eltsPerVReg = (vlenb * 8) `div` (eew)
      in
      do
        forM_ [vstart..(vl-1)]
          (\i ->
             do
               let
                 realVd = vd + ( (i `div` eltsPerVReg))
                 realVs1 = vs1 + ( (i `div` eltsPerVReg))
                 realVs2 = vs2 + ( (i `div` eltsPerVReg))
                 realEltIdx = (i `mod` eltsPerVReg)
               vs1value <- getVRegisterElement (fromImm (eew `div` 8)) (fromImm ( realVs1)) (fromImm ( realEltIdx))
               vs2value <- getVRegisterElement (fromImm (eew `div` 8)) (fromImm ( realVs2)) (fromImm ( realEltIdx))
               let
                 vs1Element :: MachineInt = (combineBytes (map int8_toWord8 vs1value))
                 vs2Element :: MachineInt = (combineBytes (map int8_toWord8 vs2value))
                 vdElement = vs1Element + vs2Element
               (trace ("vs1, vs2, vd vaddvv values" ++ show (fromIntegral vs1Element) ++ " " ++ show (fromIntegral vs2Element) ++ " " ++ show (fromIntegral vdElement)) $ (setCSRField Field.VStart i))
               when (vm == 0b1 || (testVectorBit vmask i)) (setVRegisterElement (fromImm (eew `div` 8)) (fromImm (realVd)) (fromImm ( realEltIdx)) (map word8_toInt8 (splitBytes (eew) vdElement)))
               when (vm == 0b0 && (not (testVectorBit vmask i) && (vma == 0b1))) (setVRegisterElement (fromImm ( (eew `div` 8))) (fromImm ( realVd)) (fromImm ( realEltIdx)) (replicate_machineInt (eew `div` 8) (complement (zeroBits :: Int8))))
               setCSRField Field.VStart i
          )
        when (vta == 0b1) (forM_ [vl..(maxTail-1)]
                           (\i ->
                              let realVd = vd + ( (i `div` eltsPerVReg))
                                  realEltIdx = (i `mod` eltsPerVReg)
                              in do
                                setVRegisterElement (fromImm ( (eew `div` 8))) (fromImm ( realVd)) (fromImm ( realEltIdx)) (replicate_machineInt (eew `div` 8) (complement (zeroBits :: Int8)))))
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
    let eew = 2 ^ (fromMaybe 8 (translateWidth_Inst width)) 
        maxTail = computeMaxTail vlmul vlenb (eew) 
        eltsPerVReg = (vlenb * 8) `div` (eew)
      in
      do
        forM_ [vstart..(vl-1)]
          (\i -> 
            let realVd = vd + ( (i `div` eltsPerVReg))
                realEltIdx = (i `mod` eltsPerVReg)
            in
              do
                 baseMem <- getRegister rs1
                 value <- getVRegisterElement (fromImm ( (eew `div` 8))) (fromImm ( realVd)) (fromImm ( realEltIdx))
                 storeUntranslatedBytes (baseMem + (fromImm (i * ( (eew `div` 8)))))  value
                 setCSRField Field.VStart i
          )
        setCSRField Field.VStart 0b0
        
execute (Vlr vd rs1 nf) =
  let
    numFields = fromMaybe 9 $ translateNumFields nf in
  do
    vlenb <- getCSRField Field.VLenB
    when (((numFields == 1) || (numFields == 2) || (numFields == 4) || (numFields == 8)) && (( vd) `mod` numFields == 0))
      (forM_ [0..(numFields-1)]
      (\i ->
         do
           baseMem <- getRegister rs1
           mem <- loadUntranslatedBytes (baseMem + (fromImm (vlenb * ( i)))) ( vlenb)
           (trace ("setting vreg " ++ (show (vd + i)) ++ " with values " ++ (show mem))) $ setVRegister (vd + (i)) mem
           ))
execute (Vsr vs3 rs1 nf) =
  let
    numFields = fromMaybe 9 $ translateNumFields nf in
  do
    vlenb <- getCSRField Field.VLenB
    when (((numFields == 1) || (numFields == 2) || (numFields == 4) || (numFields == 8)) && (( vs3) `mod` numFields == 0))
      (forM_ [0..(numFields-1)]
      (\i ->
         do
           baseMem <- getRegister rs1
           value <- getVRegister (vs3 + ( i))
           (trace ("getting vreg " ++ (show (vs3 + i)) ++ " with values " ++ (show value))) $ storeUntranslatedBytes (baseMem + fromImm (vlenb * ( i))) value
           ))

