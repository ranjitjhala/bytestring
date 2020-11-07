
{-# LANGUAGE MagicHash #-}

{-@ LIQUID "--compile-spec" @-}

module Data.LiquidPtr where 

import qualified GHC.Ptr
import qualified GHC.ForeignPtr
import qualified Foreign.Storable
import qualified Foreign.ForeignPtr
import           GHC.Base (Addr#)

{-@ embed GHC.Ptr.Ptr * as int @-}

{-@ predicate PtrEnd  P = ((pbase P) + (plen (pbase P))) @-}

{-@ predicate PtrSize P = ((PtrEnd P) - P) @-}

{-@ predicate PtrValid P = ((pbase P) <= P && 0 < PtrSize P) @-}

{-@ type PtrOk a = {p:Ptr a | PtrValid p} @-}
{-@ type Ptr0 a N = {p:Ptr a | p = pbase p && plen p = N} @-}
{-@ type PtrMid a L R = {p:Ptr a | pbase p == pbase L && L <= p && p <= R } @-}

{-@ ignore withForeignPtr @-}
{-@ withForeignPtr ::  fp:(GHC.ForeignPtr.ForeignPtr a) -> ((Ptr0 a (fplen fp)) -> IO b) -> IO b @-}
withForeignPtr :: GHC.ForeignPtr.ForeignPtr a -> (GHC.Ptr.Ptr a -> IO b) -> IO b
withForeignPtr = Foreign.ForeignPtr.withForeignPtr

-- predicate PValid P N         = ((0 <= N) && (N < (plen P)))
--
-- Foreign.Storable.peekByteOff :: (Foreign.Storable.Storable a)
--                              => forall b. p:(GHC.Ptr.Ptr b)
--                              -> {v:GHC.Types.Int | (PValid p v)}
--                              -> (GHC.Types.IO a)
--
-- Foreign.Storable.pokeByteOff :: (Foreign.Storable.Storable a)
--                              => forall b. p:(GHC.Ptr.Ptr b)
--                              -> {v:GHC.Types.Int | (PValid p v)}
--                              -> a
--                              -> GHC.Types.IO ()

{-@ peek :: (Foreign.Storable.Storable a) => PtrOk a -> IO a @-}
peek :: (Foreign.Storable.Storable a) => GHC.Ptr.Ptr a -> IO a
peek     = Foreign.Storable.peek

{-@ poke :: (Foreign.Storable.Storable a) => PtrOk a -> a -> IO () @-}
poke :: (Foreign.Storable.Storable a) => GHC.Ptr.Ptr a -> a -> IO ()
poke     = Foreign.Storable.poke
-- 

{-@ castPtr :: p:_ -> {q:_ | q = p} @-}
castPtr :: GHC.Ptr.Ptr a -> GHC.Ptr.Ptr b
castPtr  = GHC.Ptr.castPtr

{-@ plusPtr :: p:GHC.Ptr.Ptr a -> off:Int -> {v:(Ptr b) | v = p + off && pbase v = pbase p} @-}
plusPtr :: GHC.Ptr.Ptr a -> Int -> GHC.Ptr.Ptr b
plusPtr  = GHC.Ptr.plusPtr

{-@ minusPtr :: q:(Ptr a) -> {p:(Ptr b) | pbase p == pbase q} -> {v:Nat | v == q - p } @-}
minusPtr :: GHC.Ptr.Ptr a -> GHC.Ptr.Ptr b -> Int
minusPtr = GHC.Ptr.minusPtr

{-@ mkPtr :: addr:_-> {v:_ | pbase v = v && plen v = addrLen addr && plen v >= 0} @-}
mkPtr :: Addr# -> GHC.Ptr.Ptr a
mkPtr = GHC.Ptr.Ptr


{-@ plusForeignPtr :: p:ForeignPtrV a -> {off:Nat | off <= fplen p} -> 
                              {q:ForeignPtrV b | fplen q = fplen p - off}  
  @-}
plusForeignPtr :: GHC.ForeignPtr.ForeignPtr a -> Int -> GHC.ForeignPtr.ForeignPtr b
plusForeignPtr = GHC.ForeignPtr.plusForeignPtr