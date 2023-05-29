-- {-# OPTIONS --exact-split #-}

module parma-day1 where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

three = succ (succ (succ zero))

_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b = succ (a + b)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

+-example =
  begin 3 + 4
  ≡⟨⟩ succ (succ (succ zero)) + succ (succ (succ (succ zero)))
  ≡⟨⟩ succ (succ (succ zero) + succ (succ (succ (succ zero))))
  ≡⟨⟩ succ (succ (succ zero + succ (succ (succ (succ zero)))))
  ≡⟨⟩ succ (succ (succ (zero + succ (succ (succ (succ zero))))))
  ≡⟨⟩ succ (succ (succ (succ (succ (succ (succ zero))))))
  ≡⟨⟩ 7 ∎

_*_ : ℕ → ℕ → ℕ
zero     * n = zero
(succ m) * n = n + (m * n)

_^_ : ℕ → ℕ → ℕ
m ^ 0        = 1
m ^ (succ n) = m * (m ^ n)

_∸_ : ℕ → ℕ → ℕ
n      ∸ zero   = zero
zero   ∸ succ n = zero
succ m ∸ succ n = m ∸ n

infixl 6  _+_  _∸_
infixl 7  _*_

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

_ : inc (⟨⟩) ≡ ⟨⟩ I
_ = refl

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = refl

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (succ n) = inc (to n)

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

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = from b * 2
from (b I) = from b * 2 + 1

_ : from (⟨⟩) ≡ 0
_ = refl

_ : from (⟨⟩ O) ≡ 0
_ = refl

_ : from (⟨⟩ O O) ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl

_ : from (⟨⟩ O O I O O) ≡ 4
_ = refl
