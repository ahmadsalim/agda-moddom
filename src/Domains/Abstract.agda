module Domains.Abstract where

open import Data.Unit renaming (⊤ to Unit)
open import Data.Bool renaming (_∧_ to _and_; _∨_ to _or_)
open import Data.Product renaming (_×_ to _**_; Σ to Sigma; proj₁ to proj1; proj₂ to proj2)
open import Data.Sum renaming (_⊎_ to Either; inj₁ to inj1; inj₂ to inj2)
open import Data.Empty renaming (⊥ to Empty; ⊥-elim to magic)
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec renaming (map′ to map')
open import Category.Monad
open import Coinduction renaming (♯_ to delay; ∞ to Inf; ♭ to force)
import Data.Nat as Nat renaming (ℕ to Nat)
import Level renaming (_⊔_ to _lub_)
open import Category.Functor

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

record IsDecLattice {al} (A : Set al) {{islattice : IsLattice A}} : Set (Level.suc al) where
  open IsLattice islattice public
  field
    _<=?_ : (a1 a2 : A) -> Dec (a1 <= a2)

  _~?_  : (a1 a2 : A) -> Dec (a1 ~ a2)
  a1 ~? a2 with (a1 <=? a2)
  a1 ~? a2 | yes a1<=a2 with (a2 <=? a1)
  a1 ~? a2 | yes a1<=a2 | yes a2<=a1 = yes (a1<=a2 , a2<=a1)
  a1 ~? a2 | yes a1<=a2 | no contra = no (\ { (a1<=a2 , a2<=a1) -> contra a2<=a1 })
  a1 ~? a2 | no contra = no (\ { (a1<=a2 , a2<=a1) -> contra a1<=a2 })

module Lattice {A : Set} {{L : IsLattice A}} {{DL : IsDecLattice A}} where
  private
    module DL = IsDecLattice DL

  mutual
    fix' : forall {i} -> A -> (f : A -> A) -> Delay i (Sigma A (\ a -> a DL.~ f a))
    fix' p f with (p DL.~? f p)
    fix' p f | yes p~fp = now (p , p~fp)
    fix' p f | no p<>fp = later (fix'i p f)

    fix'i : forall {i} -> A -> (f : A -> A) -> InfDelay i (Sigma A (\ a -> a DL.~ f a))
    InfDelay.force (fix'i p f) = fix' p f

  fix : forall {i} -> (f : A -> A) -> Delay i (Sigma A (\ a -> a DL.~ f a))
  fix f = fix' DL.bot f

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
  ProdFunctor1 : forall {al bl} {A : Set al} -> RawFunctor {al Level.lub bl} (A **_)
  ProdFunctor1 = record { _<$>_ = \ { f (a , b) -> (a , f b) } }

  ProdFunctor2 : forall {al bl} {B : Set bl} -> RawFunctor {al Level.lub bl} (_** B)
  ProdFunctor2 = record { _<$>_ = \ { f (a , b) -> (f a , b) } }

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

instance
  ProdDecLat : forall {al bl} {A : Set al} {B : Set bl}
               {{LA : IsLattice A}} {{LB : IsLattice B}}
               {{DLA : IsDecLattice A}} {{DLB : IsDecLattice B}} -> IsDecLattice (A ** B)
  ProdDecLat {_} {_} {A} {B} {{LA}} {{LB}} {{DLA}} {{DLB}} = record { _<=?_ = Prod<=? }
    where open IsDecLattice {{...}}
          Prod<=? : (ab1 ab2 : A ** B) -> Dec (ab1 <= ab2)
          Prod<=? (a1 , b1) (a2 , b2) with (a1 <=? a2)
          Prod<=? (a1 , b1) (a2 , b2) | yes a1<=a2 with (b1 <=? b2)
          Prod<=? (a1 , b1) (a2 , b2) | yes a1<=a2 | yes b1<=b2 = yes (a1<=a2 , b1<=b2)
          Prod<=? (a1 , b1) (a2 , b2) | yes a1<=a2 | no contra = no (\ { (a1<=a2 , b1<=b2) -> contra b1<=b2 })
          Prod<=? (a1 , b1) (a2 , b2) | no contra = no (\ { (a1<=a2 , b1<=b2) -> contra a1<=a2 })

-- How to enforce invariants as first class instead of relying on module system
abstract
  record _*O*_ {al} {bl} (A : Set al) (B : Set bl) : Set (al Level.lub bl) where
    constructor _,_
    field
      proj1 : A
      proj2 : B

open _*O*_

module _ {al} {bl} {A : Set al} {B : Set bl} {{LA : IsLattice A}} {{LB : IsLattice B}} where
  open IsLattice {{...}}

  abstract
    *O*-bot : A *O* B
    *O*-bot = bot , bot

    _,,_ : A -> B -> A *O* B
    _,,_ a b with (is-bot a)
    _,,_ a b | yes p = *O*-bot
    _,,_ a b | no _ with (is-bot b)
    _,,_ a b | no _ | yes p = *O*-bot
    _,,_ a b | no notbota | no notbotb = a , b

    fst : A *O* B -> A
    fst (a , b) = a

    snd : A *O* B -> B
    snd (a , b) = b

    fst-red : forall {a b} (anotbot : (a <= bot) -> Empty) (bnotbot : (b <= bot) -> Empty) -> fst (a ,, b) == a
    fst-red {a} {b} anotbot bnotbot with (is-bot a)
    fst-red {a} {b} anotbot bnotbot | yes p = magic (anotbot p)
    fst-red {a} {b} anotbot bnotbot | no _ with (is-bot b)
    fst-red {a} {b} anotbot bnotbot | no _ | yes p = magic (bnotbot p)
    fst-red {a} {b} anotbot bnotbot | no _ | no _ = refl

    snd-red : forall {a b} (anotbot : (a <= bot) -> Empty) (bnotbot : (b <= bot) -> Empty) -> snd (a ,, b) == b
    snd-red {a} {b} anotbot bnotbot with (is-bot a)
    snd-red {a} {b} anotbot bnotbot | yes p = magic (anotbot p)
    snd-red {a} {b} anotbot bnotbot | no _ with (is-bot b)
    snd-red {a} {b} anotbot bnotbot | no _ | yes p = magic (bnotbot p)
    snd-red {a} {b} anotbot bnotbot | no _ | no _ = refl

    fst-bot : forall {a b} (aorbbot : Either (a <= bot) (b <= bot)) -> fst (a ,, b) == bot
    fst-bot {a} {b} aorbbot with (is-bot a)
    fst-bot {a} {b} aorbbot | yes _ = refl
    fst-bot {a} {b} (inj1 abot) | no anotbot = magic (anotbot abot)
    fst-bot {a} {b} (inj2 bbot) | no anotbot with (is-bot b)
    fst-bot {a} {b} (inj2 bbot) | no anotbot | yes _ = refl
    fst-bot {a} {b} (inj2 bbot) | no anotbot | no bnotbot = magic (bnotbot bbot)

    snd-bot : forall {a b} (aorbbot : Either (a <= bot) (b <= bot)) -> snd (a ,, b) == bot
    snd-bot {a} {b} aorbbot with (is-bot a)
    snd-bot {a} {b} aorbbot | yes _ = refl
    snd-bot {a} {b} (inj1 abot) | no anotbot = magic (anotbot abot)
    snd-bot {a} {b} (inj2 bbot) | no anotbot with (is-bot b)
    snd-bot {a} {b} (inj2 bbot) | no anotbot | yes _ = refl
    snd-bot {a} {b} (inj2 bbot) | no anotbot | no bnotbot = magic (bnotbot bbot)

    instance
      CoalescedProdLat : IsLattice (A *O* B)
      CoalescedProdLat = record
                        { _<=_ = CoalescedProd<=
                        ; _glb_ = \ ab1 ab2 -> (proj1 ab1 glb proj1 ab2) ,, (proj2 ab1 glb proj2 ab2)
                        ; _lub_ = \ ab1 ab2 -> (proj1 ab1 lub proj1 ab2) ,, (proj2 ab1 lub proj2 ab2)
                        ; bot = *O*-bot
                        ; top = top ,, top
                        ; <=-reflexive = CoalescedProd<=-reflexive
                        ; is-bot = CoalescedProd-is-bot
                        }
        where
          CoalescedProd<= : A *O* B -> A *O* B -> Set
          CoalescedProd<= (a1 , b1) (a2 , b2) = a1 <= a2 ** b1 <= b2

          CoalescedProd<=-reflexive : (ab : A *O* B) → CoalescedProd<= ab ab
          CoalescedProd<=-reflexive (a , b) = <=-reflexive a , <=-reflexive b

          CoalescedProd-is-bot : (ab : A *O* B) → Dec (CoalescedProd<= ab *O*-bot)
          CoalescedProd-is-bot ab with is-bot (proj1 ab) | is-bot (proj2 ab)
          CoalescedProd-is-bot ab | yes p | yes p2 = yes (p , p2)
          CoalescedProd-is-bot ab | yes p | no contra = no (\ z -> contra (proj2 z))
          CoalescedProd-is-bot ab | no contra | p2 = no (\ z -> contra (proj1 z))

    instance
      CoalescedProdDecLat : {{DLA : IsDecLattice A}} {{DLB : IsDecLattice B}} -> IsDecLattice (A *O* B)
      CoalescedProdDecLat = record { _<=?_ = CProd<=? }
        where open IsDecLattice {{...}}
              CProd<=? : (ab1 ab2 : A *O* B) -> Dec (IsLattice._<=_ CoalescedProdLat ab1 ab2)
              CProd<=? (a1 , b1) (a2 , b2) with (a1 <=? a2)
              CProd<=? (a1 , b1) (a2 , b2) | yes a1<=a2 with (b1 <=? b2)
              CProd<=? (a1 , b1) (a2 , b2) | yes a1<=a2 | yes b1<=b2 = yes (a1<=a2 , b1<=b2)
              CProd<=? (a1 , b1) (a2 , b2) | yes a1<=a2 | no contra = no (\ { (a1<=a2 , b1<=b2) -> contra b1<=b2 })
              CProd<=? (a1 , b1) (a2 , b2) | no contra = no (\ { (a1<=a2 , b1<=b2) -> contra a1<=a2 })

{-# NO_POSITIVITY_CHECK #-}
data Fix# {fl} (F# : Set fl -> Set fl) : Nat.Nat -> Set fl where
  in-top : Fix# F# Nat.zero
  in-f# : forall {n} -> F# (Fix# F# n) -> Fix# F# (Nat.suc n)

instance
  Fix#-Lat : forall {fl n} {F# : Set fl -> Set fl} {{LF# : forall {X#} -> IsLattice X# -> IsLattice (F# X#)}} -> IsLattice (Fix# F# n)
  Fix#-Lat {fl} {Nat.zero} {F#} {{LF#}} = record
                                        { _<=_ = \ _ _ -> Unit
                                        ; _glb_ = \ _ _ -> in-top
                                        ; _lub_ = \ _ _ -> in-top
                                        ; bot = in-top
                                        ; top = in-top
                                        ; <=-reflexive = \ _ -> tt
                                        ; is-bot = \ _ -> yes tt
                                        }
  Fix#-Lat {fl} {Nat.suc n} {F#} {{LF#}} = record
                                        { _<=_ = Fix#<=
                                        ; _glb_ = \ { (in-f# f#1) (in-f# f#2) → in-f# (f#1 LF#.glb f#2) }
                                        ; _lub_ = \ { (in-f# f#1) (in-f# f#2) → in-f# (f#1 LF#.lub f#2) }
                                        ; bot = in-f# LF#.bot
                                        ; top = in-f# LF#.top
                                        ; <=-reflexive = Fix#<=-reflexive
                                        ; is-bot = Fix#-is-bot
                                        }
    where module LF# = IsLattice (LF# (Fix#-Lat {n = n} {F# = F#} {{LF#}}))
          Fix#<= : Fix# F# (Nat.suc n) -> Fix# F# (Nat.suc n) -> Set
          Fix#<= (in-f# f#1) (in-f# f#2) = f#1 LF#.<= f#2

          Fix#<=-reflexive : (f# : Fix# F# (Nat.suc n)) -> Fix#<= f# f#
          Fix#<=-reflexive (in-f# f#) = LF#.<=-reflexive f#

          Fix#-is-bot : (f# : Fix# F# (Nat.suc n)) → Dec (Fix#<= f# (in-f# LF#.bot))
          Fix#-is-bot (in-f# f#) = LF#.is-bot f#

  Fix#-DecLat : forall {fl n} {F# : Set fl -> Set fl}
                       {{LF# : forall {X#} -> IsLattice X# -> IsLattice (F# X#)}}
                       {{DLF# : forall {X#} {{LX : IsLattice X#}} -> IsDecLattice X# -> IsDecLattice (F# X#) {{LF# LX}} }}
                       -> IsDecLattice (Fix# F# n) {{Fix#-Lat {{LF#}}}}
  Fix#-DecLat {fl} {Nat.zero} {F#} {{LF#}} {{DF#}} = record { _<=?_ = \ _ _ -> yes tt }
  Fix#-DecLat {fl} {Nat.suc n} {F#} {{LF#}} {{DF#}} = record
                                                            { _<=?_ = \ { (in-f# f#1) (in-f# f#2) -> f#1 DF#.<=? f#2 } }
    where module DF# = IsDecLattice (DF# (Fix#-DecLat {n = n} {F# = F#} {{LF#}} {{DF#}}))
