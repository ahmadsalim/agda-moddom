module Util where

open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

weakenF : ∀ {n} → Fin n → Fin (suc n)
weakenF zero = zero
weakenF (suc x) = suc (weakenF x)

strengthenF : ∀ {n} (x : Fin (suc n)) → x ≢ fromℕ n → Fin n
strengthenF {zero} zero notlast = ⊥-elim (notlast refl)
strengthenF {zero} (suc ()) notlast
strengthenF {suc n} zero notlast = zero
strengthenF {suc n} (suc x) notlast = suc (strengthenF x (λ d → notlast (cong suc d)))

_≟F_ : ∀ {n} (x y : Fin n) → Dec (x ≡ y)
_≟F_ {zero} () y
_≟F_ {suc n} zero zero = yes refl
_≟F_ {suc n} zero (suc y) = no (λ ())
_≟F_ {suc n} (suc x) zero = no (λ ())
_≟F_ {suc n} (suc x) (suc y) with (x ≟F y)
_≟F_ {suc n} (suc x) (suc .x) | yes refl = yes refl
_≟F_ {suc n} (suc x) (suc y) | no x≢y = no (λ { refl → x≢y refl })
