module Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ (suc m) = n * (n ^ m)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc (⟨⟩ O) = ⟨⟩ I
inc ⟨⟩ =  ⟨⟩ I
inc (⟨⟩ I) = ⟨⟩ I O
inc (m O) = m I
inc (m I) = (inc m) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from′ : ℕ → Bin → ℕ
from′ _ ⟨⟩ = 0
from′ n (m O) = from′ (n + 1) m
from′ n (m I) = 2 ^ n + from′ (n + 1) m

from : Bin → ℕ
from = from′ 0

-- Incrementing something with a zero at the end always gives something with a one
inc-zero : ∀ (m : Bin) → inc (m O) ≡ m I
inc-zero ⟨⟩ = refl
inc-zero (m O) = refl
inc-zero (m I) = refl

-- inc corresponds to suc over from
suc-inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
suc-inc ⟨⟩ = suc-inc (⟨⟩ O)
suc-inc (⟨⟩ O) = refl
suc-inc (m O) rewrite inc-zero m = refl
suc-inc (m I) = {!!}

-- from and to are isomorphisms between ℕ and Bin
from-to : ∀ (m : ℕ) → (from (to m)) ≡ m
from-to 0 = refl
from-to (suc m) rewrite suc-inc (to m) | from-to m = refl

_ : to 0 ≡ ⟨⟩ O
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

_ : from (⟨⟩ O) ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl
