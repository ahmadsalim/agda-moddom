{-# OPTIONS --injective-type-constructors #-}
module Util where

open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H
open import Size
open import Category.Monad
open import Data.Vec using (Vec; _++_; _∷_)

weakenF : ∀ {n} → Fin n → Fin (suc n)
weakenF zero = zero
weakenF (suc x) = suc (weakenF x)

strengthenF : ∀ {n} (x : Fin (suc n)) → x ≢ fromℕ n → Fin n
strengthenF {zero} zero notlast = ⊥-elim (notlast refl)
strengthenF {zero} (suc ()) notlast
strengthenF {suc n} zero notlast = zero
strengthenF {suc n} (suc x) notlast = suc (strengthenF x (λ d → notlast (P.cong suc d)))

_≟F_ : ∀ {n} (x y : Fin n) → Dec (x ≡ y)
_≟F_ {zero} () y
_≟F_ {suc n} zero zero = yes refl
_≟F_ {suc n} zero (suc y) = no (λ ())
_≟F_ {suc n} (suc x) zero = no (λ ())
_≟F_ {suc n} (suc x) (suc y) with (x ≟F y)
_≟F_ {suc n} (suc x) (suc .x) | yes refl = yes refl
_≟F_ {suc n} (suc x) (suc y) | no x≢y = no (λ { refl → x≢y refl })

-- Based on https://arxiv.org/pdf/1406.2059.pdf

mutual
  data Delay (i : Size) (A : Set) : Set where
    now : A -> Delay i A
    later : InfDelay i A -> Delay i A

  record InfDelay (i : Size) (A : Set) : Set where
    coinductive
    field
      force : {j : Size< i} -> Delay j A
open InfDelay

module Delays where
  mutual
    _>>=_ : forall {i A B} -> Delay i A -> (A -> Delay i B) -> Delay i B
    now x >>= f = f x
    later x >>= f = later (x >>=i f)

    _>>=i_ : forall {i A B} -> InfDelay i A -> (A -> Delay i B) -> InfDelay i B
    force (di >>=i f) = force di >>= f

instance
  delayMonad : forall {i} -> RawMonad (Delay i)
  delayMonad = record { return = now ; _>>=_ = Delays._>>=_ }

::-inj1 : forall {al} {n} {m} {A : Set al} {x y : A} {xs : Vec A n} {ys : Vec A m} -> (x ∷ xs) ≅ (y ∷ ys) -> x ≅ y
::-inj1 refl = refl

::-inj2 : forall {al} {n} {m} {A : Set al} {x y : A} {xs : Vec A n} {ys : Vec A m} -> (x ∷ xs) ≅ (y ∷ ys) -> xs ≅ ys
::-inj2 refl = refl
