module Domains.Abstract where

open import Data.Unit renaming (⊤ to Unit)
open import Data.Bool renaming (_∧_ to _and_; _∨_ to _or_)
open import Data.Product renaming (_×_ to _**_; Σ to Sigma; proj₁ to proj1; proj₂ to proj2)
open import Data.Empty renaming (⊥ to Empty; ⊥-elim to magic)
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)
open import Relation.Nullary
open import Category.Monad
open import Coinduction renaming (♯_ to delay; ∞ to Inf; ♭ to force)
import Data.Nat as Nat renaming (ℕ to Nat)
import Data.Conat as CoNat renaming (Coℕ to CoNat)
import Level renaming (_⊔_ to _lub_)

open import Util

record IsLattice {al} (A : Set al) : Set (Level.suc al) where
  field
    _<=_ : A -> A -> Set
    _glb_ _lub_ : A -> A -> A
    bot top : A

  _~_ : A -> A -> Set
  _~_ a b = a <= b ** b <= a

  _!~_ : A -> A -> Set
  _!~_ a b = a ~ b -> Empty

  _>=_ : A -> A -> Set
  _>=_ a b = b <= a

  -- We need this for operations that somehow depend on bot
  field
    <=-reflexive : forall a -> a <= a
    is-bot : (a : A) -> Dec (a <= bot)

record IsDecLattice (A : Set) : Set1 where
  field
    {{islattice}} : IsLattice A
  open IsLattice islattice public
  field
    _<=?_ : (a1 a2 : A) -> Dec (a1 <= a2)

  _~?_  : (a1 a2 : A) -> Dec (a1 ~ a2)
  a1 ~? a2 with (a1 <=? a2)
  a1 ~? a2 | yes a1<=a2 with (a2 <=? a1)
  a1 ~? a2 | yes a1<=a2 | yes a2<=a1 = yes (a1<=a2 , a2<=a1)
  a1 ~? a2 | yes a1<=a2 | no contra = no (\ { (a1<=a2 , a2<=a1) -> contra a2<=a1 })
  a1 ~? a2 | no contra = no (\ { (a1<=a2 , a2<=a1) -> contra a1<=a2 })

module Lattice {A : Set} {{L : IsDecLattice A}} where
  private
    module L = IsDecLattice L

  mutual
    fix' : forall {i} -> A -> (f : A -> A) -> Delay i (Sigma A (\ a -> a L.~ f a))
    fix' p f with (p L.~? f p)
    fix' p f | yes p~fp = now (p , p~fp)
    fix' p f | no p<>fp = later (fix'i p f)

    fix'i : forall {i} -> A -> (f : A -> A) -> InfDelay i (Sigma A (\ a -> a L.~ f a))
    InfDelay.force (fix'i p f) = fix' p f

  fix : forall {i} -> (f : A -> A) -> Delay i (Sigma A (\ a -> a L.~ f a))
  fix f = fix' L.bot f

instance
  BoolLat : IsLattice (Bool -> Bool)
  BoolLat = record
            { _<=_ = Bool<=
            ; _glb_ = \ f g x -> f x and g x
            ; _lub_ = \ f g x -> f x or g x
            ; bot = \ _ -> false
            ; top = \ _ -> true
            ; <=-reflexive = \ f x Tfx → Tfx
            ; is-bot = Bool-is-bot
            }
          where Bool<= : (Bool -> Bool) -> (Bool -> Bool) -> Set
                Bool<= f g = (x : Bool) -> T (f x) -> T (g x)

                Bool-is-bot : (f : Bool -> Bool) -> Dec (Bool<= f (\ _ -> false))
                Bool-is-bot f with f true | inspect f true
                Bool-is-bot f | false | [ eq ] with f false | inspect f false
                Bool-is-bot f | false | [ eq ] | false | [ eq2 ] = yes f-is-bot
                  where f-is-bot : (x : Bool) -> T (f x) -> Empty
                        f-is-bot false Tfx rewrite eq2 = Tfx
                        f-is-bot true Tfx rewrite eq = Tfx
                Bool-is-bot f | false | [ eq ] | true | [ eq2 ] = no f-is-not-bot
                  where f-is-not-bot : ((x : Bool) -> T (f x) -> Empty) -> Empty
                        f-is-not-bot f-is-bot = f-is-bot false (subst (\ x -> T x) (sym eq2) tt)
                Bool-is-bot f | true | [ eq ] = no f-is-not-bot
                  where f-is-not-bot : ((x : Bool) -> T (f x) -> Empty) -> Empty
                        f-is-not-bot f-is-bot = f-is-bot true (subst (\ x -> T x) (sym eq) tt)

  BoolDecLat : IsDecLattice (Bool -> Bool)
  BoolDecLat = record { _<=?_ = Bool<=? }
    where open IsLattice BoolLat
          Bool<=? : (f g : Bool -> Bool) -> Dec (f <= g)
          Bool<=? f g with f true | inspect f true | g true | inspect g true
          Bool<=? f g | false | [ eq ] | q | [ eq2 ] with f false | inspect f false | g false | inspect g false
          Bool<=? f g | false | [ eq ] | q | [ eq2 ] | false | [ eq3 ] | qq | [ eq4 ] = yes f<=g
            where f<=g : (x : Bool) -> T (f x) -> T (g x)
                  f<=g false rewrite eq3 = \ ()
                  f<=g true rewrite eq = \ ()
          Bool<=? f g | false | [ eq ] | q | [ eq2 ] | true | [ eq3 ] | false | [ eq4 ] =
            no (\ f<=g -> subst (λ x → T x) eq4 (f<=g false (subst (\ x -> T x) (sym eq3) tt)))
          Bool<=? f g | false | [ eq ] | q | [ eq2 ] | true | [ eq3 ] | true | [ eq4 ] = yes f<=g
            where f<=g : (x : Bool) -> T (f x) -> T (g x)
                  f<=g false rewrite eq3 | eq4 = \ x -> x
                  f<=g true rewrite eq = \ ()
          Bool<=? f g | true | [ eq ] | false | [ eq2 ] = no (\ f<=g -> subst (\ x -> T x) eq2 (f<=g true (subst (\ x -> T x) (sym eq) tt)))
          Bool<=? f g | true | [ eq ] | true | [ eq2 ] with f false | inspect f false | g false | inspect g false
          Bool<=? f g | true | [ eq ] | true | [ eq2 ] | false | [ eq3 ] | q | [ eq4 ] = yes f<=g
            where f<=g : (x : Bool) -> T (f x) -> T (g x)
                  f<=g false rewrite eq3 = \ ()
                  f<=g true rewrite eq | eq2 = \ x -> x
          Bool<=? f g | true | [ eq ] | true | [ eq2 ] | true | [ eq3 ] | false | [ eq4 ] =
             no (\ f<=g -> subst (\ x -> T x) eq4 (f<=g false (subst (\ x -> T x) (sym eq3) tt)))
          Bool<=? f g | true | [ eq ] | true | [ eq2 ] | true | [ eq3 ] | true | [ eq4 ] = yes f<=g
            where f<=g : (x : Bool) -> T (f x) -> T (g x)
                  f<=g false rewrite eq3 | eq4 = \ x -> x
                  f<=g true rewrite eq | eq2 = \ x -> x

data Sign : Set where
  sgnbot sgn+ sgn0 sgn- sgntop : Sign

data Sign<= : Sign -> Sign -> Set where
  sgnbot-all : forall a -> Sign<= sgnbot a
  sgn+-self   : Sign<= sgn+ sgn+
  sgn0-self   : Sign<= sgn0 sgn0
  sgn--self   : Sign<= sgn- sgn-
  sgntop-all : forall a -> Sign<= a sgntop

instance
  SignLat : IsLattice Sign
  SignLat = record
            { _<=_ = Sign<=
            ; _glb_ = Sign-glb
            ; _lub_ = Sign-lub
            ; bot = sgnbot
            ; top = sgntop
            ; <=-reflexive = Sign<=-reflexive
            ; is-bot = Sign-is-bot
            }
    where Sign-glb : Sign -> Sign -> Sign
          Sign-glb sgnbot y = sgnbot
          Sign-glb sgn+ sgnbot = sgnbot
          Sign-glb sgn+ sgn+ = sgn+
          Sign-glb sgn+ sgn0 = sgnbot
          Sign-glb sgn+ sgn- = sgnbot
          Sign-glb sgn+ sgntop = sgn+
          Sign-glb sgn0 sgnbot = sgnbot
          Sign-glb sgn0 sgn+ = sgnbot
          Sign-glb sgn0 sgn0 = sgn0
          Sign-glb sgn0 sgn- = sgnbot
          Sign-glb sgn0 sgntop = sgn0
          Sign-glb sgn- sgnbot = sgnbot
          Sign-glb sgn- sgn+ = sgnbot
          Sign-glb sgn- sgn0 = sgnbot
          Sign-glb sgn- sgn- = sgn-
          Sign-glb sgn- sgntop = sgn-
          Sign-glb sgntop y = y

          Sign-lub : Sign -> Sign -> Sign
          Sign-lub sgnbot y = y
          Sign-lub sgn+ sgnbot = sgn+
          Sign-lub sgn+ sgn+ = sgn+
          Sign-lub sgn+ sgn0 = sgntop
          Sign-lub sgn+ sgn- = sgntop
          Sign-lub sgn+ sgntop = sgntop
          Sign-lub sgn0 sgnbot = sgn0
          Sign-lub sgn0 sgn+ = sgntop
          Sign-lub sgn0 sgn0 = sgn0
          Sign-lub sgn0 sgn- = sgntop
          Sign-lub sgn0 sgntop = sgntop
          Sign-lub sgn- sgnbot = sgn-
          Sign-lub sgn- sgn+ = sgntop
          Sign-lub sgn- sgn0 = sgntop
          Sign-lub sgn- sgn- = sgn-
          Sign-lub sgn- sgntop = sgntop
          Sign-lub sgntop y = sgntop

          Sign<=-reflexive : forall a -> Sign<= a a
          Sign<=-reflexive sgnbot = sgnbot-all sgnbot
          Sign<=-reflexive sgn+ = sgn+-self
          Sign<=-reflexive sgn0 = sgn0-self
          Sign<=-reflexive sgn- = sgn--self
          Sign<=-reflexive sgntop = sgntop-all sgntop

          Sign-is-bot : forall x -> Dec (Sign<= x sgnbot)
          Sign-is-bot sgnbot = yes (sgnbot-all sgnbot)
          Sign-is-bot sgn+ = no (\ ())
          Sign-is-bot sgn0 = no (\ ())
          Sign-is-bot sgn- = no (\ ())
          Sign-is-bot sgntop = no (\ ())

  SignDecLat : IsDecLattice Sign
  SignDecLat = record { _<=?_ = Sign<=? }
    where open IsLattice SignLat
          Sign<=? : (s1 s2 : Sign) -> Dec (s1 <= s2)
          Sign<=? sgnbot s2 = yes (sgnbot-all s2)
          Sign<=? sgn+ sgnbot = no (\ ())
          Sign<=? sgn+ sgn+ = yes sgn+-self
          Sign<=? sgn+ sgn0 = no (\ ())
          Sign<=? sgn+ sgn- = no (\ ())
          Sign<=? sgn+ sgntop = yes (sgntop-all sgn+)
          Sign<=? sgn0 sgnbot = no (\ ())
          Sign<=? sgn0 sgn+ = no (\ ())
          Sign<=? sgn0 sgn0 = yes sgn0-self
          Sign<=? sgn0 sgn- = no (\ ())
          Sign<=? sgn0 sgntop = yes (sgntop-all sgn0)
          Sign<=? sgn- sgnbot = no (\ ())
          Sign<=? sgn- sgn+ = no (\ ())
          Sign<=? sgn- sgn0 = no (\ ())
          Sign<=? sgn- sgn- = yes sgn--self
          Sign<=? sgn- sgntop = yes (sgntop-all sgn-)
          Sign<=? sgntop sgnbot = no (\ ())
          Sign<=? sgntop sgn+ = no (\ ())
          Sign<=? sgntop sgn0 = no (\ ())
          Sign<=? sgntop sgn- = no (\ ())
          Sign<=? sgntop sgntop = yes (sgntop-all sgntop)

instance
  ProdLat : forall {al bl} {A : Set al} {B : Set bl} {{LA : IsLattice A}} {{LB : IsLattice B}} -> IsLattice (A ** B)
  ProdLat {_} {_} {A} {B} {{LA}} {{LB}} =
          record { _<=_ = Prod<=
                  ; _glb_ = \ { (a1 , b1) (a2 , b2) -> a1 LA.glb a2 , b1 LB.glb b2 }
                  ; _lub_ =  \ { (a1 , b1) (a2 , b2) -> a1 LA.lub a2 , b1 LB.lub b2 }
                  ; bot = LA.bot , LB.bot
                  ; top = LA.top , LB.top
                  ; <=-reflexive = \ { (a , b) -> LA.<=-reflexive a , LB.<=-reflexive b }
                  ; is-bot = Prod-is-bot
                  }
    where
      module LA = IsLattice LA
      module LB = IsLattice LB
      Prod<= : A ** B -> A ** B -> Set
      Prod<= (a1 , b1) (a2 , b2) = a1 LA.<= a2 ** b1 LB.<= b2

      Prod-is-bot : (ab : A ** B) -> Dec (Prod<= ab (LA.bot , LB.bot))
      Prod-is-bot (a , b) with (LA.is-bot a)
      Prod-is-bot (a , b) | yes p with (LB.is-bot b)
      Prod-is-bot (a , b) | yes p | yes p2 = yes (p , p2)
      Prod-is-bot (a , b) | yes p | no contra = no (\ z -> contra (proj2 z))
      Prod-is-bot (a , b) | no contra = no (\ z -> contra (proj1 z))

-- TODO how to enforce invariants
-- I am not sure how to enforce invariant without unicity and still preserving size
record _*O*_ {al} {bl} (A : Set al) (B : Set bl) : Set (al Level.lub bl) where
  constructor _,_
  field
    fst : A
    snd : B

open _*O*_

module CoalescedProduct {al} {bl} {A : Set al} {B : Set bl} {{LA : IsLattice A}} {{LB : IsLattice B}} where
  private
    module LA = IsLattice LA
    module LB = IsLattice LB

  bot : A *O* B
  bot = LA.bot , LB.bot

  _,,_ : A -> B -> A *O* B
  _,,_ a b with (LA.is-bot a)
  _,,_ a b | yes p = bot
  _,,_ a b | no _ with (LB.is-bot b)
  _,,_ a b | no _ | yes p = bot
  _,,_ a b | no notbota | no notbotb = a , b

instance
  CoalescedProdLat : forall {al} {bl} {A : Set al} {B : Set bl} {{LA : IsLattice A}} {{LB : IsLattice B}} -> IsLattice (A *O* B)
  CoalescedProdLat {_} {_} {A} {B} {{LA}} {{LB}} =
                          record
                          { _<=_ = CoalescedProd<=
                          ; _glb_ = \ ab1 ab2 -> (fst ab1 LA.glb fst ab2) ,, (snd ab1 LB.glb snd ab2)
                          ; _lub_ = \ ab1 ab2 -> (fst ab1 LA.lub fst ab2) ,, (snd ab1 LB.lub snd ab2)
                          ; bot = bot
                          ; top = LA.top ,, LB.top
                          ; <=-reflexive = CoalescedProd<=-reflexive
                          ; is-bot = CoalescedProd-is-bot
                          }
    where
      module LA = IsLattice LA
      module LB = IsLattice LB
      open CoalescedProduct {{LA}} {{LB}}
      CoalescedProd<= : A *O* B -> A *O* B -> Set
      CoalescedProd<= (a1 , b1) (a2 , b2) = a1 LA.<= a2 ** b1 LB.<= b2

      CoalescedProd<=-reflexive : (ab : A *O* B) → CoalescedProd<= ab ab
      CoalescedProd<=-reflexive (a , b) = LA.<=-reflexive a , LB.<=-reflexive b

      CoalescedProd-is-bot : (ab : A *O* B) → Dec (CoalescedProd<= ab bot)
      CoalescedProd-is-bot ab with LA.is-bot (fst ab) | LB.is-bot (snd ab)
      CoalescedProd-is-bot ab | yes p | yes p2 = yes (p , p2)
      CoalescedProd-is-bot ab | yes p | no contra = no (\ z -> contra (proj2 z))
      CoalescedProd-is-bot ab | no contra | p2 = no (\ z -> contra (proj1 z))

{-# NO_POSITIVITY_CHECK #-}
data Fix# {fl} (F# : Set fl -> Set fl) : CoNat.CoNat -> Set fl where
  in-top : Fix# F# CoNat.zero
  in-f# : forall {infn} -> F# (Inf (Fix# F# (force infn))) -> Fix# F# (CoNat.suc (infn))

out-f# : forall {infn} {F# : Set -> Set} -> Fix# F# (CoNat.suc infn) -> F# (Inf (Fix# F# (force infn)))
out-f# (in-f# f#) = f#

{-# TERMINATING #-}
Fix#-Lattice : {n : CoNat.CoNat} {F# : Set -> Set} {{LF# : forall {X#} -> IsLattice X# -> IsLattice (F# X#)}} -> IsLattice (Inf (Fix# F# n))
Fix#-Lattice {CoNat.zero} {F#} {{LF#}} = record
                                             { _<=_ = \ _ _ -> Unit
                                             ; _glb_ =  \ _ _ -> delay in-top
                                             ; _lub_ =  \ _ _ -> delay in-top
                                             ; bot = delay in-top
                                             ; top = delay in-top
                                             ; <=-reflexive = \ _ -> tt
                                             ; is-bot = \ _ -> yes tt
                                             }
Fix#-Lattice {CoNat.suc n} {F#} {{LF#}} = record
                                              { _<=_ = Fix#<=
                                              ; _glb_ = {!!}
                                              ; _lub_ = {!!}
                                              ; bot = {!!}
                                              ; top = {!!}
                                              ; <=-reflexive = {!!}
                                              ; is-bot = {!!}
                                              }
  where module LF# = IsLattice (LF# (Fix#-Lattice {force n} {F#} {{LF#}}))
        Fix#<= : Inf (Fix# F# (CoNat.suc n)) -> Inf (Fix# F# (CoNat.suc n)) -> Set
        Fix#<= f#1 f#2 = out-f# (force f#1) LF#.<= (out-f# (force f#2))

        Fix#<=-reflexive : (f# : Inf (Fix# F# (CoNat.suc n))) -> Fix#<= f# f#
        Fix#<=-reflexive f# = LF#.<=-reflexive (out-f# (force f#))

        Fix#-is-bot : (f# : Inf (Fix# F# (CoNat.suc n))) -> Dec (Fix#<= f# (delay (in-f# LF#.bot)))
        Fix#-is-bot f# with (LF#.is-bot (out-f# (force f#)))
        Fix#-is-bot f# | yes p = yes p
        Fix#-is-bot f# | no notp = no notp
