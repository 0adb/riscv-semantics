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

index_machineInt :: forall t. [t] -> MachineInt -> t
index_machineInt l idx = (l !! (fromIntegral idx))

testBit_machineInt :: forall a. Bits a => a -> MachineInt -> Bool
testBit_machineInt b idx = testBit b (fromIntegral idx)

int8_toWord8 :: Int8 -> Word8
int8_toWord8 n = (fromIntegral:: Int8 -> Word8) n

word8_toInt8 :: Word8 -> Int8
word8_toInt8 n = (fromIntegral:: Word8 -> Int8) n


translateLMUL :: MachineInt -> Maybe MachineInt
translateLMUL enc = dec
  where
    dec
      | enc == 0b101 = Just (-3)
      | enc == 0b110 = Just (-2)
      | enc == 0b111 = Just (-1)
      | enc == 0b000 = Just (0)
      | enc == 0b001 = Just 1
      | enc == 0b010 = Just 2
      | enc == 0b011 = Just 3
      | True = Nothing



translateWidth_Vtype :: MachineInt -> Maybe MachineInt
translateWidth_Vtype enc = dec
  where
    dec
      | enc==0b000 = Just 3
      | enc==0b001 = Just 4
      | enc==0b010 = Just 5
      | enc==0b011 = Just 6
      | True = Nothing



translateWidth_Inst :: MachineInt -> Maybe MachineInt
translateWidth_Inst enc = dec
  where
    dec
      | enc==0b000 = Just 3
      | enc==0b101 = Just 4
      | enc==0b110 = Just 5
      | enc==0b111 = Just 6
      | True = Nothing
      
translateNumFields :: MachineInt -> Maybe MachineInt
translateNumFields enc = dec
  where
    dec
      | enc == 0b000 = Just 1
      | enc == 0b001 = Just 2
      | enc == 0b010 = Just 3
      | enc == 0b011 = Just 4
      | enc == 0b100 = Just 5
      | enc == 0b101 = Just 6
      | enc == 0b110 = Just 7
      | enc == 0b111 = Just 8
      | True  = Nothing


legalSEW ::  MachineInt -> MachineInt -> MachineInt -> Bool
-- We are checking that vsew (bits) <= vlmul * vlenb * 8 (everything in bits)
-- which in this case is (2 raised to (pow2SEW) <= 2 raised to (pow2LMUL) times vlenb times 8)
legalSEW vsew vlmul vlenb =
    fromMaybe False $ do
        pow2SEW <- translateWidth_Vtype vsew
        pow2LMUL <- translateLMUL vlmul
        (return (2 ^ pow2SEW <= ((2 ^ pow2LMUL) * vlenb * 8)))

consistentRatio :: MachineInt -> MachineInt -> MachineInt -> MachineInt -> Bool
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
computeVLMAX ::  MachineInt -> MachineInt -> MachineInt -> MachineInt
computeVLMAX vlmul vsew vlenb =
  fromMaybe 0 $ do
        pow2SEW <- translateWidth_Vtype vsew
        pow2LMUL <- translateLMUL vlmul
        (let exp = 3 + pow2LMUL - pow2SEW in
            if exp >= 0 then
              return (vlenb * (2 ^ (exp)))
            else
              return (vlenb `quot` (2 ^ (-exp))))

computeMaxTail :: MachineInt -> MachineInt ->  MachineInt -> MachineInt
computeMaxTail vlmul vlenb vsew =
    fromMaybe 0 $ do
        pow2SEW <- translateWidth_Vtype vsew
        pow2LMUL <- translateLMUL vlmul
        let tail =
              8 * ( vlenb) * (2 ^ ((if pow2LMUL < 0 then 0 else pow2LMUL) - pow2SEW)) in if tail >= 1
           then return tail
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
        vl =  (if ( avl) <= vlmax then ( avl) else vlmax) in
        do
          setCSRField Field.VL vl 
          setCSRField Field.VStart 0b0
          setCSRField Field.VIll vill
          unless (rd == 0b0) (setRegister rd (fromImm vl))
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
  if (eew == 1 || eew == 2 || eew == 4 || eew == 8)
  then
    do
      vlenb <- getCSRField Field.VLenB
      vregValue <- getVRegister baseReg
      let value = take_machineInt ( eew) (drop_machineInt ( (eltIndex * eew)) vregValue) in
        if (length_machineInt value) == ( eew)
        then return value
        else raiseException 0 2
  else
    raiseException 0 2
      
  
setVRegisterElement :: forall p t. (RiscvMachine p t) => MachineInt -> VRegister -> MachineInt -> [Int8] -> p ()
setVRegisterElement eew baseReg eltIndex value =
  if (eew == 1 || eew == 2 || eew == 4 || eew == 8)
  then
    do
      vlenb <- getCSRField Field.VLenB
      vregValue <- getVRegister baseReg
      let newVregValue =
            (take_machineInt ( (eltIndex * eew)) vregValue) ++
            (value) ++
            (drop_machineInt ( ((eltIndex + 1) * eew)) vregValue) in
        if (length_machineInt newVregValue) == (length_machineInt vregValue)
        then  (setVRegister baseReg newVregValue)
        else raiseException 0 2
   else raiseException 0 2


translateOffsetAddr :: forall t. MachineWidth t => t -> MachineInt -> t
translateOffsetAddr memAddr i = memAddr + (fromImm i)

loadUntranslatedBytes :: forall p t. (RiscvMachine p t) => t -> MachineInt -> p [Int8]
loadUntranslatedBytes memAddr numBytes =  (forM (zeroToExclusive_machineInt numBytes) (\i ->
                                                                 do
                                                                   addr <- (translate Load 1 (translateOffsetAddr memAddr i))
                                                                   loadByte Execute addr))
                                         
storeUntranslatedBytes :: forall p t. (RiscvMachine p t) => t -> [Int8] -> p ()
storeUntranslatedBytes memAddr value = forM_ (zeroToExclusive_machineInt (length_machineInt value))
                                       (\i ->
                                           do
                                             addr <- translate Store 1 (translateOffsetAddr memAddr i)
                                             (storeByte Execute addr ((index_machineInt value i)))
                                       ) 


testVectorBit :: [Int8] -> MachineInt -> Bool
testVectorBit vregValue posn = testBit_machineInt
                               (
                                (index_machineInt vregValue  (posn `quot` 8)))
                               ((posn `rem` 8))

execute :: forall p t. (RiscvMachine p t) => InstructionV -> p ()

execute (Vsetvli rd rs1 vtypei) =
    do
        old_vl <- getCSRField Field.VL
        if rs1 /= 0b00000 
            then
                do
                    avl <- getRegister rs1
                    executeVset False (regToInt64 avl) vtypei rd
            else
                if rd /= 0b00000 
                    then executeVset False (regToInt64 (maxSigned :: t)) vtypei rd
                    else executeVset True (regToInt64 (maxSigned :: t)) vtypei rd 

execute (Vsetvl rd rs1 rs2) = 
    do
        vtypei <- getRegister rs2
        old_vl <- getCSRField Field.VL
        if rs1 /= 0b00000 
            then
                do
                    avl <- getRegister rs1
                    executeVset False (regToInt64 avl) (regToInt64 vtypei) rd
                else
                    if rd /= 0b00000
                        then executeVset False (regToInt64 (maxSigned :: t)) (regToInt64 vtypei) rd
                        else executeVset True old_vl (regToInt64 vtypei) rd
     


execute (Vsetivli rd uimm vtypei) = executeVset False uimm vtypei rd



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
        eltsPerVReg = (vlenb * 8) `quot` (eew)
    do
       forM_ [vstart..(vl-1)]
          (\i ->
            let realVd = vd + (i `quot` eltsPerVReg)
                realEltIdx = (i `rem` eltsPerVReg)
            in do             
               baseMem <- getRegister rs1
               mem <- loadUntranslatedBytes (translateOffsetAddr baseMem (i * (eew `quot` 8)))  (eew `quot` 8)
               when (vm == 0b1 || (testVectorBit vmask ( i)))  (setVRegisterElement (eew `quot` 8) realVd realEltIdx mem)
               when (vm == 0b0 && (not (testVectorBit vmask ( i))) && (vma == 0b1)) (setVRegisterElement (eew `quot` 8) realVd realEltIdx (replicate_machineInt (eew `quot` 8) (complement (zeroBits)) ))
               setCSRField Field.VStart i
          )
       when (vta == 0b1)
         (forM_ [vl..( (maxTail-1))]
           (\i ->
               let realVd = vd + ( (i `quot` eltsPerVReg))
                   realEltIdx = (i `rem` eltsPerVReg)
               in  (setVRegisterElement (eew `quot` 8) realVd realEltIdx (replicate_machineInt (eew `quot` 8) (complement (zeroBits))))))
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
        eltsPerVReg = (vlenb * 8) `quot` (eew)
      in
      do
        forM_ [vstart..(vl-1)]
          (\i ->
             do
               let
                 realVd = vd + ( (i `quot` eltsPerVReg))
                 realVs1 = vs1 + ( (i `quot` eltsPerVReg))
                 realVs2 = vs2 + ( (i `quot` eltsPerVReg))
                 realEltIdx = (i `rem` eltsPerVReg)
               vs1value <- getVRegisterElement (eew `quot` 8) realVs1 realEltIdx
               vs2value <- getVRegisterElement (eew `quot` 8) realVs2 realEltIdx
               let
                 vs1Element = ((combineBytes :: [Word8] -> MachineInt) (map int8_toWord8 vs1value))
                 vs2Element = ((combineBytes :: [Word8] -> MachineInt) (map int8_toWord8 vs2value))
                 vdElement = vs1Element + vs2Element
               ( (setCSRField Field.VStart i))
               when (vm == 0b1 || (testVectorBit vmask i)) (setVRegisterElement (eew `quot` 8) realVd realEltIdx (map word8_toInt8 (splitBytes (eew) vdElement)))
               when (vm == 0b0 && (not (testVectorBit vmask i) && (vma == 0b1))) (setVRegisterElement (eew `quot` 8) realVd realEltIdx (replicate_machineInt (eew `quot` 8) (complement (zeroBits))))
               setCSRField Field.VStart i
          )
        when (vta == 0b1) (forM_ [vl..(maxTail-1)]
                           (\i ->
                              let realVd = vd + ( (i `quot` eltsPerVReg))
                                  realEltIdx = (i `rem` eltsPerVReg)
                              in do
                                setVRegisterElement (eew `quot` 8) realVd realEltIdx (replicate_machineInt (eew `quot` 8) (complement (zeroBits)))))
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
        eltsPerVReg = (vlenb * 8) `quot` (eew)
      in
      do
        forM_ [vstart..(vl-1)]
          (\i -> 
            let realVd = vd + ( (i `quot` eltsPerVReg))
                realEltIdx = (i `rem` eltsPerVReg)
            in
              do
                 baseMem <- getRegister rs1
                 value <- getVRegisterElement (eew `quot` 8) realVd realEltIdx
                 storeUntranslatedBytes (translateOffsetAddr baseMem (i * (eew `quot` 8)))  value
                 setCSRField Field.VStart i
          )
        setCSRField Field.VStart 0b0
        
execute (Vlr vd rs1 nf) =
  let
    numFields = fromMaybe 9 $ translateNumFields nf in
  do
    vlenb <- getCSRField Field.VLenB
    when (((numFields == 1) || (numFields == 2) || (numFields == 4) || (numFields == 8)) && (( vd) `rem` numFields == 0))
      (forM_ [0..(numFields-1)]
      (\i ->
         do
           baseMem <- getRegister rs1
           mem <- loadUntranslatedBytes  (translateOffsetAddr baseMem (i * (vlenb))) ( vlenb)
           setVRegister (vd + (i)) mem
           ))
execute (Vsr vs3 rs1 nf) =
  let
    numFields = fromMaybe 9 $ translateNumFields nf in
  do
    vlenb <- getCSRField Field.VLenB
    when (((numFields == 1) || (numFields == 2) || (numFields == 4) || (numFields == 8)) && (( vs3) `rem` numFields == 0))
      (forM_ [0..(numFields-1)]
      (\i ->
         do
           baseMem <- getRegister rs1
           value <- getVRegister (vs3 + ( i))
           storeUntranslatedBytes   (translateOffsetAddr baseMem (i * (vlenb)))  value
           ))


execute inst = error $ "dispatch bug: " ++ show inst
