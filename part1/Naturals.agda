module plfa.part1.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- import Agda.Builtin.Equality as Eq
-- open Eq using (_≡_; refl)

import Relation.Binary.PropositionalEquality as Eq
