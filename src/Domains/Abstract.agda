module Domains.Abstract where

open import Data.Unit
open import Data.Bool renaming (_∧_ to _and_; _∨_ to _or_)
open import Data.Product renaming (_×_ to _**_; proj₁ to proj1; proj₂ to proj2)
open import Data.Empty renaming (⊥ to Empty; ⊥-elim to magic)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Coinduction renaming (♯_ to delay; ∞ to Inf; ♭ to force)
import Data.Nat as Nat renaming (ℕ to Nat)

record Lattice : Set1 where
  field
    Carrier : Set
    _<=_ : Carrier -> Carrier -> Set
    _glb_ _lub_ : Carrier -> Carrier -> Carrier
    bot top : Carrier

  _~_ : Carrier -> Carrier -> Set
  _~_ a b = a <= b ** b <= a

  _<>_ : Carrier -> Carrier -> Set
  _<>_ a b = a ~ b -> Empty

  _>_ : Carrier -> Carrier -> Set
  _>_ a b = a <= b -> Empty

  _>=_ : Carrier -> Carrier -> Set
  _>=_ a b = b <= a

  _<_ : Carrier -> Carrier -> Set
  _<_ a b = b > a

  -- We need this for operations that somehow depend on bot
  field
    <=-reflexive : forall a -> a <= a
    is-bot : (a : Carrier) -> Dec (a <= bot)

module Lattices (L : Lattice) where
  private
    module L = Lattice L

  -- Not really fix but what can we do when we don't have decidable equality to compute stuff on infinite values
  fix : (n : Nat.Nat) -> (L.Carrier -> L.Carrier) -> L.Carrier
  fix Nat.zero f = L.bot
  fix (Nat.suc n) f = f (fix n f) L.lub fix n f

BoolLat : Lattice
BoolLat = record
          { Carrier = Bool -> Bool
          ; _<=_ = Bool<=
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
                      f-is-not-bot f-is-bot = f-is-bot false (subst (λ x → T x) (sym eq2) tt)
              Bool-is-bot f | true | [ eq ] = no f-is-not-bot
                where f-is-not-bot : ((x : Bool) -> T (f x) -> Empty) -> Empty
                      f-is-not-bot f-is-bot = f-is-bot true (subst (λ x → T x) (sym eq) tt)

data Sign : Set where
  sgnbot sgn+ sgn0 sgn- sgntop : Sign

data Sign<= : Sign -> Sign -> Set where
  sgnbot-all : forall a -> Sign<= sgnbot a
  sgn+-self   : Sign<= sgn+ sgn+
  sgn0-self   : Sign<= sgn0 sgn0
  sgn--self   : Sign<= sgn- sgn-
  sgntop-all : forall a -> Sign<= a sgntop

SignLat : Lattice
SignLat = record
          { Carrier = Sign
          ; _<=_ = Sign<=
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

ProdLat : Lattice -> Lattice -> Lattice
ProdLat LA LB = record { Carrier = LA.Carrier ** LB.Carrier
                ; _<=_ = Prod<=
                ; _glb_ = \ { (a1 , b1) (a2 , b2) -> a1 LA.glb a2 , b1 LB.glb b2 }
                ; _lub_ =  \ { (a1 , b1) (a2 , b2) -> a1 LA.lub a2 , b1 LB.lub b2 }
                ; bot = LA.bot , LB.bot
                ; top = LA.top , LB.top
                ; <=-reflexive = \ { (a , b) -> LA.<=-reflexive a , LB.<=-reflexive b }
                ; is-bot = Prod-is-bot
                }
  where
    module LA = Lattice LA
    module LB = Lattice LB
    Prod<= : LA.Carrier ** LB.Carrier -> LA.Carrier ** LB.Carrier -> Set
    Prod<= (a1 , b1) (a2 , b2) = a1 LA.<= a2 ** b1 LB.<= b2

    Prod-is-bot : (ab : LA.Carrier ** LB.Carrier) -> Dec (Prod<= ab (LA.bot , LB.bot))
    Prod-is-bot (a , b) with (LA.is-bot a)
    Prod-is-bot (a , b) | yes p with (LB.is-bot b)
    Prod-is-bot (a , b) | yes p | yes p2 = yes (p , p2)
    Prod-is-bot (a , b) | yes p | no contra = no (\ z -> contra (proj2 z))
    Prod-is-bot (a , b) | no contra = no (\ z -> contra (proj1 z))

record _*O*_ (LA : Lattice) (LB : Lattice) : Set where
  constructor coalesced
  private
    module LA = Lattice LA
    module LB = Lattice LB
  field
    fst : LA.Carrier
    snd : LB.Carrier
    fst-bot-snd-bot : fst LA.<= LA.bot -> snd LB.<= LB.bot
    snd-bot-fst-bot : snd LB.<= LB.bot -> fst LA.<= LA.bot

module CoalescedProduct (LA : Lattice) (LB : Lattice) where
  private
    module LA = Lattice LA
    module LB = Lattice LB

  bot : LA *O* LB
  bot = coalesced LA.bot LB.bot (\ _ -> LB.<=-reflexive LB.bot) (\ _ -> LA.<=-reflexive LA.bot)

  _,,_ : LA.Carrier -> LB.Carrier -> LA *O* LB
  _,,_ a b with (LA.is-bot a)
  _,,_ a b | yes p = bot
  _,,_ a b | no ¬p with (LB.is-bot b)
  _,,_ a b | no ¬p | yes p = bot
  _,,_ a b | no notbota | no notbotb = coalesced a b (\ x -> magic (notbota x)) (\ x -> magic (notbotb x))

CoalescedProdLat : Lattice -> Lattice -> Lattice
CoalescedProdLat LA LB = record
                         { Carrier = LA *O* LB
                         ; _<=_ = CoalescedProd<=
                         ; _glb_ = \ { (coalesced a1 b1 _ _) (coalesced a2 b2 _ _) -> (a1 LA.glb a2) ,, (b1 LB.glb b2) }
                         ; _lub_ =  \ { (coalesced a1 b1 _ _) (coalesced a2 b2 _ _) -> (a1 LA.lub a2) ,, (b1 LB.lub b2) }
                         ; bot = bot
                         ; top = LA.top ,, LB.top
                         ; <=-reflexive = CoalescedProd<=-reflexive
                         ; is-bot = CoalescedProd-is-bot
                         }
  where
    module LA = Lattice LA
    module LB = Lattice LB
    open CoalescedProduct LA LB

    CoalescedProd<= : LA *O* LB -> LA *O* LB -> Set
    CoalescedProd<= (coalesced a1 b1 _ _) (coalesced a2 b2 _ _) = a1 LA.<= a2 ** b1 LB.<= b2

    CoalescedProd<=-reflexive : (ab : LA *O* LB) → CoalescedProd<= ab ab
    CoalescedProd<=-reflexive (coalesced a b _ _) = LA.<=-reflexive a , LB.<=-reflexive b

    CoalescedProd-is-bot : (ab : LA *O* LB) → Dec (CoalescedProd<= ab bot)
    CoalescedProd-is-bot (coalesced a b _ _) with (LA.is-bot a)
    CoalescedProd-is-bot (coalesced a b fbsb _) | yes p = yes (p , fbsb p)
    CoalescedProd-is-bot (coalesced a b _ _) | no notbota with (LB.is-bot b)
    CoalescedProd-is-bot (coalesced a b _ sbfb) | no notbota | yes p = yes (sbfb p , p)
    CoalescedProd-is-bot (coalesced a b _ _) | no notbota | no notbotb = no (\ z -> notbota (proj1 z))

mutual
  {-# NO_POSITIVITY_CHECK #-}
  record Fix# (F# : Lattice -> Lattice) : Set where
    constructor in-f#
    field
      out-f# : Lattice.Carrier (F# (Fix#-Lattice F#))

  {-# TERMINATING #-}
  Fix#-Lattice : (Lattice -> Lattice) -> Lattice
  Fix#-Lattice F# = record
                      { Carrier = Inf (Fix# F#)
                      ; _<=_ = Fix#<=
                      ; _glb_ = \ f#1 f#2 -> delay (in-f# (Fix#.out-f# (force f#1) LF#.glb Fix#.out-f# (force f#2)))
                      ; _lub_ = \ f#1 f#2 -> delay (in-f# (Fix#.out-f# (force f#1) LF#.lub Fix#.out-f# (force f#2)))
                      ; bot = delay (in-f# LF#.bot)
                      ; top = delay (in-f# LF#.top)
                      ; <=-reflexive = Fix#<=-reflexive
                      ; is-bot = Fix#-is-bot
                      }
    where module LF# = Lattice (F# (Fix#-Lattice F#))

          Fix#<= : Inf (Fix# F#) -> Inf (Fix# F#) -> Set
          Fix#<= f#1 f#2 = Fix#.out-f# (force f#1) LF#.<= Fix#.out-f# (force f#2)

          Fix#<=-reflexive : (f# : Inf (Fix# F#)) -> Fix#<= f# f#
          Fix#<=-reflexive f# = LF#.<=-reflexive (Fix#.out-f# (force f#))

          Fix#-is-bot : (f# : Inf (Fix# F#)) -> Dec (Fix#<= f# (delay (in-f# LF#.bot)))
          Fix#-is-bot f# with (LF#.is-bot (Fix#.out-f# (force f#)))
          Fix#-is-bot f# | yes p = yes p
          Fix#-is-bot f# | no notp = no notp
