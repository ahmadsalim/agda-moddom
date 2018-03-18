module Domains.Concrete where

{-# NO_POSITIVITY_CHECK #-}
record Fix (F : Set -> Set) : Set where
  constructor in-f
  field
    out-f : F (Fix F)
