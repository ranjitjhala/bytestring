
## Bytestring

[ 1 of 20] Data.ByteString.Builder.Prim.Internal
[ 2 of 20] Data.ByteString.Builder.Prim.Internal.Floating
[ 3 of 20] Data.ByteString.Builder.Prim.Internal.UncheckedShifts
[ 4 of 20] Data.ByteString.Builder.Prim.Binary
[ 5 of 20] >> Data.ByteString.Internal
[ 6 of 20] >> Data.ByteString.Lazy.Internal
[ 7 of 20] Data.ByteString.Short.Internal
  * TODO lots of stuff with funky arrays that we have no specs for

[ 8 of 20] Data.ByteString.Short
[ 9 of 20] >> Data.ByteString.Unsafe

[10 of 20] >> Data.ByteString 
[11 of 20] >> Data.ByteString.Lazy
[12 of 20] >> Data.ByteString.Lazy.Char8
[13 of 20] >> Data.ByteString.Char8
[14 of 20] Data.ByteString.Builder.Prim.Internal.Base16
[15 of 20] Data.ByteString.Builder.Prim.ASCII
[16 of 20] Data.ByteString.Builder.Internal
[17 of 20] Data.ByteString.Builder.Prim
[18 of 20] Data.ByteString.Builder.Extra
[19 of 20] Data.ByteString.Builder.ASCII
[20 of 20] Data.ByteString.Builder


## 11/1

- Rename to `bytestring-lh` to avoid circular package dependencies
- Rename macros `MIN_VERSION_base` to `MIN_VERSION_liquid_base`
- Expose `GHC.Prim` in `liquid-ghc-prim`
- *Builds without plugin*
- Yay, first errors in `Data/ByteString/Builder/Prim/Internal.hs`

## 11/4

- First errors in `Data/ByteString/Internal.hs`

```haskell
instance Data ByteString where
  gfoldl f z txt = z packBytes `f` unpackBytes txt
  toConstr _     = error "Data.ByteString.ByteString.toConstr"
  gunfold _ _    = error "Data.ByteString.ByteString.gunfold"
  dataTypeOf _   = mkNoRepType "Data.ByteString.ByteString"
```

- add `cpp-options: -DLIQUID` so we can hack various type definitions

- Write LIQUID (no UNPACK / !annot) versions of `FixedPrim a` and `BoundedPrim a` 
  o.w. errors of the form `The types for the wrapper and worker data constructors cannot be merged`

- Refined versions of `FixedPrim` and `BoundedPrim` and we're off onto `Data.Bytestring.Internal`

## 11/5

- ERROR in unsafePackLen (poke) --> unsafeCreate --> create 


--

## 11/14

- needs fancy absref `Data.ByteString.Lazy.Internal.packBytes` -> `S.packUptoLenBytes` --> `createUptoN'` 
- cannot associate `lbsLen` with B.Lazy.Internal.Bytestring -- ODD crash with `len` ?
- ghcid swallows up `Termination Error` fix the printout
- STOP: `Lazy.Internal.toStrict` which is super fun, and like `Internal.concat`

```haskell
data Box = B Int

{-@ measure bVal @-}
bVal :: Box -> Int
bVal (B n) = n

{-@ mkBox :: forall <p :: Int -> Bool, q :: Box -> Bool>. 
                { n :: Int <p> |- {b : Box | bVal b = n} <: {b: Box<q> | True}}
                (() -> IO (Int<p>)) -> IO (Box<q>)
  @-}
mkBox :: (() -> IO Int) -> IO Box
mkBox f = do
    n <- f ()
    return (B n)

{-@ test :: k:Int -> IO ({b:Box | k < bVal b}) @-}
test :: Int -> IO Box
test k = mkBox (\_ -> return (k + 100))
```