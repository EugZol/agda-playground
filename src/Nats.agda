{-# OPTIONS --safe #-}

open import Prelude
open import Data.Nat.Base using (ℕ; _+_; _·_)

data Bin : Type where
  ⟨⟩ : Bin
  _𝟘 : Bin → Bin
  _𝟙 : Bin → Bin
  remove-o : ⟨⟩ ＝ ⟨⟩ 𝟘

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ 𝟙
inc (x 𝟘) = x 𝟙
inc (x 𝟙) = (inc x) 𝟘
inc (remove-o i) = ⟨⟩ 𝟙

to : ℕ → Bin
to zero = ⟨⟩ 𝟘
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (x 𝟘) = (from x) · 2
from (x 𝟙) = suc ((from x) · 2)
from (remove-o i) = zero

inc-is-suc : ∀ (x : Bin) → from (inc x) ＝ suc (from x)
inc-is-suc ⟨⟩ = refl
inc-is-suc (x 𝟘) = refl
inc-is-suc (x 𝟙) =
  (from (inc (x 𝟙)))
    =⟨⟩
  from ((inc x) 𝟘)
    =⟨⟩
  ⌜ from (inc x) ⌝ · 2
    =⟨ ap! (inc-is-suc x) ⟩
  (suc (from x) · 2)
    ∎
inc-is-suc (remove-o i) = refl

from-to-ext : ∀ (x : ℕ) → from (to x) ＝ x
from-to-ext zero = refl
from-to-ext (suc x) =
  from (to (suc x))
    =⟨⟩
  from (inc (to x))
    =⟨ inc-is-suc (to x) ⟩
  suc (⌜ from (to x) ⌝ )
    =⟨ ap! (from-to-ext x) ⟩
  suc x
    ∎

from-to : from ∘ to ＝ id
from-to = ext from-to-ext

to-2n=to-n-0 : ∀ (n : ℕ) → to (n · 2) ＝ (to n) 𝟘
to-2n=to-n-0 zero = ap _𝟘 remove-o
to-2n=to-n-0 (suc n) =
  inc (inc (⌜ to (n · 2) ⌝))
    =⟨ ap! (to-2n=to-n-0 n) ⟩
  inc (inc ((to n) 𝟘))
    ∎

to-from-ext : ∀ (b : Bin) → to (from b) ＝ b
to-from-ext ⟨⟩ = sym remove-o
to-from-ext (b 𝟘) =
  to (from b · 2)
    =⟨ to-2n=to-n-0 (from b) ⟩
  ⌜ to (from b) ⌝ 𝟘
    =⟨ ap! (to-from-ext b) ⟩
  b 𝟘
    ∎
to-from-ext (b 𝟙) =
  inc (⌜ to (from b · 2) ⌝)
    =⟨ ap! (to-2n=to-n-0 (from b)) ⟩
  inc ((to (from b)) 𝟘)
    =⟨⟩
  ⌜ to (from b) ⌝ 𝟙
    =⟨ ap! (to-from-ext b) ⟩
  b 𝟙
    ∎
to-from-ext (remove-o i) = {!   !}

to-from : to ∘ from ＝ id
to-from = ext to-from-ext

ℕ-bin-iso : ℕ ≅ Bin
ℕ-bin-iso = make-iso to from (make-inverses to-from from-to)

ℕ-bin-equiv : ℕ ≃ Bin
ℕ-bin-equiv = ≅→≃ ℕ-bin-iso
-- ℕ-bin-equiv = to , qinv→is-equiv (make-qinv from (make-inverses to-from from-to))
-- ℕ-bin-equiv = to , is-biinv→is-equiv (make-is-biinv from from-to from to-from)
