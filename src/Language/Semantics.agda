module Language.Semantics where

open import Data.Integer renaming (ℤ to Integer; _+_ to _+Z_; _*_ to _*Z_; _-_ to _-Z_; suc to isuc;
                                   _≤?_ to _<=?Z_; _≟_ to _~?Z_)
open import Data.Unit renaming (⊤ to Unit)
open import Data.Bool as B2 renaming (Bool to B2)
open import Data.Empty renaming (⊥ to Empty; ⊥-elim to magic)
open import Data.Nat renaming (ℕ to Nat; _+_ to _+N_; _*_ to _*N_)
open import Data.Nat.Properties.Simple
open import Data.Fin renaming (_+_ to _+F_; _-_ to _-F_; _≤_ to _<=F_; _≤?_ to _<=F?_; fromℕ to fromNat)
open import Data.Sum renaming (_⊎_ to Either; inj₁ to inj1; inj₂ to inj2)
open import Data.Product renaming (_×_ to _**_; Σ to Sigma; proj₁ to proj1; proj₂ to proj2)
open import Data.Vec as Vec renaming (_∷_ to _::_)
open import Data.Vec.Properties
open import Relation.Nullary.Decidable as Dec renaming (⌊_⌋ to toBool)
open import Relation.Nullary
open import Relation.Binary.HeterogeneousEquality as P renaming (_≅_ to _=~=_; ≡-to-≅ to ==-to-=~=)
open import Relation.Binary.PropositionalEquality using (refl)
open import Function as F renaming (_∋_ to the)
open import Function.Equality renaming (_⟨$⟩_ to _<$>_)
open import Function.Equivalence renaming (_⇔_ to Equiv)
open import Category.Functor as Functor
import Level

open import Domains.Concrete
open import Domains.Abstract as Abs
open import Language.Rec
open import Util renaming (_≟F_ to _~F?_)

record SemanticOps : Set1 where
  field
    [[_]]t' : forall {n} -> Type' n -> Vec Set n -> Set

  [[_]]t : Type -> Set
  [[_]]t t = [[ t ]]t' []

  field
    I-num : Integer -> [[ Int ]]t

    _-I_ _+I_ _*I_ : [[ Int ]]t -> [[ Int ]]t -> [[ Int ]]t
    _<=I_ _~I_ : [[ Int ]]t -> [[ Int ]]t -> [[ Bool ]]t

    B-tt B-ff : [[ Bool ]]t
    B-if : forall {t} -> [[ Bool ]]t -> [[ t ]]t -> [[ t ]]t -> [[ t ]]t

    P-pair : forall {t s} -> [[ t ]]t -> [[ s ]]t -> [[ t *t s ]]t
    P-fst : forall {t s} ->  [[ t *t s ]]t -> [[ t ]]t
    P-snd : forall {t s} -> [[ t *t s ]]t -> [[ s ]]t

    S-left : forall {t s} -> [[ t ]]t -> [[ t +t s ]]t
    S-right : forall {t s} -> [[ s ]]t -> [[ t +t s ]]t
    S-case : forall {t s w} -> [[ t +t s ]]t -> ([[ t ]]t -> [[ w ]]t)
                                             -> ([[ s ]]t -> [[ w ]]t)
                                             -> [[ w ]]t

    S-abs : forall {t} -> [[ t < Rec t > ]]t -> [[ Rec t ]]t
    S-rep : forall {t} -> [[ Rec t ]]t -> [[ t < Rec t > ]]t

postulate
  believe-me : forall {a} {A : Set a} -> A

module Concrete where
  [[_]]t' : forall {n} -> Type' n -> Vec Set n -> Set
  [[ Int ]]t' As = Integer
  [[ Bool ]]t' As = B2
  [[ Var x ]]t' As = lookup x As
  [[ t *t s ]]t' As = ([[ t ]]t' As) ** ([[ s ]]t' As)
  [[ t +t s ]]t' As = Either ([[ t ]]t' As) ([[ s ]]t' As)
  [[_]]t' {n} (Rec t) As = Fix (\ B -> [[ t ]]t' (B :: As))

  mutual
    fix : forall {i} {A} (f : A -> A) -> Delay i A
    fix f = later (fix' f) Delays.>>= (\ x -> now (f x))

    fix' : forall {i} {A} (f : A -> A) -> InfDelay i A
    InfDelay.force (fix' f) = fix f

  SynSemSub : forall {n As} {Cs : Vec Set (suc n)} (t : Type' (suc n)) (t' : Type' n)
   (CsAs : Cs =~= As ++ Vec.[ [[ t' ]]t' As ])
   -> Equiv ([[ t < t' > ]]t' As) ([[ t ]]t' Cs)
  SynSemSub {n} {As} Int t' CsAs = equivalence F.id F.id
  SynSemSub {n} {As} Bool t' CsAs = equivalence F.id F.id
  SynSemSub {n} {As} (Var x) t' CsAs with (x ~F? fromNat n)
  SynSemSub {n} {As} (Var x) t' CsAs | yes refl =
    equivalence (subst F.id (P.sym (lookup-last {n} {As} CsAs))) (subst F.id (lookup-last {n} {As} CsAs))
    where lookup-last : forall {n} {As : Vec Set n} {B : Set} {Cs : Vec Set (suc n)} (CsAsB : Cs =~= As ++ Vec.[ B ]) -> lookup (fromNat n) Cs =~= B
          lookup-last {zero} {[]} {B} refl = refl
          lookup-last {suc n} {A :: As} {B} {C :: Cs} p = lookup-last {n} {As} {B} {Cs} (::-inj2 p)
  SynSemSub {n} {As} (Var x) t' CsAs | no contra =
    equivalence (subst F.id (lookup-strengthen CsAs)) (subst F.id (P.sym (lookup-strengthen CsAs)))
    where lookup-strengthen : forall {n} {x} {contra} {As : Vec Set n} {B : Set} {Cs : Vec Set (suc n)}
                              (CsAsB : Cs =~= As ++ Vec.[ B ]) -> lookup (strengthenF x contra) As =~= lookup x Cs
          lookup-strengthen {.0} {zero} {contra} {[]} {B} {C :: Cs} p = magic (contra refl)
          lookup-strengthen {.(suc _)} {zero} {contra} {A :: As} {B} {C :: Cs} p = ::-inj1 (P.sym p)
          lookup-strengthen {zero} {suc ()} {contra} {[]} {B} {Cs} p
          lookup-strengthen {suc n} {suc x} {contra} {A :: As} {B} {C :: Cs} p = lookup-strengthen (::-inj2 p)
  SynSemSub {n} {As} (t *t s) t' CsAs =
    equivalence (\ { (tv , sv) -> Equivalence.to (SynSemSub t t' CsAs) <$> tv , Equivalence.to (SynSemSub s t' CsAs) <$> sv })
                (\ { (tv , sv) -> Equivalence.from (SynSemSub t t' CsAs) <$> tv , Equivalence.from (SynSemSub s t' CsAs) <$> sv })
  SynSemSub {n} {As} (t +t s) t' CsAs =
    equivalence (\ { (inj1 tv) -> inj1 (Equivalence.to (SynSemSub t t' CsAs) <$> tv) ; (inj2 sv) -> inj2 (Equivalence.to (SynSemSub s t' CsAs) <$> sv) })
                (\ { (inj1 tv) -> inj1 (Equivalence.from (SynSemSub t t' CsAs) <$> tv) ; (inj2 sv) -> inj2 (Equivalence.from (SynSemSub s t' CsAs) <$> sv) })
  SynSemSub {n} {As} {Cs} (Rec t) t' CsAs =
    {- TODO prove cases -}
    equivalence (\ v -> in-f (Equivalence.to (SynSemSub t (shiftType zero t') believe-me) <$> Fix.out-f v))
                (\ v -> in-f (Equivalence.from (SynSemSub t (shiftType zero t') believe-me) <$> Fix.out-f v))

  ConcreteSemanticOps : SemanticOps
  ConcreteSemanticOps = record
                          { [[_]]t' = [[_]]t'
                          ; I-num = \ n -> n
                          ; _-I_ = _-Z_
                          ; _+I_ = _+Z_
                          ; _*I_ = _*Z_
                          ; _<=I_ = \ n m -> toBool (n <=?Z m)
                          ; _~I_ = \ n m -> toBool (n ~?Z m)
                          ; B-tt = true
                          ; B-ff = false
                          ; B-if = B2.if_then_else_
                          ; P-pair = _,_
                          ; P-fst = proj1
                          ; P-snd = proj2
                          ; S-left = inj1
                          ; S-right = inj2
                          ; S-case = \ v c1 c2 -> case v of \ {
                                            (inj1 x) -> c1 x;
                                            (inj2 y) -> c2 y
                                           }
                          ; S-abs = \ {t} x -> in-f (Equivalence.to (SynSemSub t (Rec t) refl) <$> x)
                          ; S-rep = \ {t} x -> Equivalence.from (SynSemSub t (Rec t) refl) <$> Fix.out-f x
                          }

module Abstract (depth : Nat) where
  [[_]]t' : forall {n} -> Type' n -> Vec Set n -> Set
  [[ Int ]]t' As = Sign
  [[ Bool ]]t' As = B2 -> B2
  [[ Var x ]]t' As = lookup x As
  [[ t *t s ]]t' As = [[ t ]]t' As *O* [[ s ]]t' As
  [[ t +t s ]]t' As = [[ t ]]t' As ** [[ s ]]t' As
  [[ Rec t ]]t' As = Fix# (\ B -> [[ t ]]t' (B :: As)) depth

  [[_]]t : Type -> Set
  [[ t ]]t = [[ t ]]t' []

  lookup-lat : forall {n} (x : Fin n) (AsL : Vec (Sigma Set IsLattice) n) -> IsLattice (lookup x (Vec.map proj1 AsL))
  lookup-lat () []
  lookup-lat zero ((A , LA) :: AsL) = LA
  lookup-lat (suc x) ((A , LA) :: AsL) = lookup-lat x AsL

  TypeLattice' : forall {n} -> (t : Type' n) (AsL : Vec (Sigma Set IsLattice) n) -> IsLattice ([[ t ]]t' (Vec.map proj1 AsL))
  TypeLattice' Int AsL = SignLat
  TypeLattice' Bool AsL = BoolLat
  TypeLattice' (Var x) AsL = lookup-lat x AsL
  TypeLattice' (t *t s) AsL = CoalescedProdLat {{TypeLattice' t AsL}} {{TypeLattice' s AsL}}
  TypeLattice' (t +t s) AsL = ProdLat {{TypeLattice' t AsL}} {{TypeLattice' s AsL}}
  TypeLattice' (Rec t) AsL = Fix#-Lat {{\ {X#} LX# -> TypeLattice' t ((X# , LX#) :: AsL)}}

  instance
    TypeLattice : {t : Type} -> IsLattice ([[ t ]]t)
    TypeLattice {t} = TypeLattice' t []

  lookup-declat : forall {n} (x : Fin n) (AsLDL : Vec (Sigma (Sigma Set IsLattice) (\ { (A , LA) -> IsDecLattice A {{LA}}})) n)
                -> IsDecLattice (lookup x (Vec.map proj1 (Vec.map proj1 AsLDL))) {{lookup-lat x (Vec.map proj1 AsLDL)}}
  lookup-declat () []
  lookup-declat zero (((A , LA) , DLA) :: AsLDL) = DLA
  lookup-declat (suc x) (((A , LA) , DLA) :: AsLDL) = lookup-declat x AsLDL

  TypeDecLattice' : forall {n} (t : Type' n) (AsLDL : Vec (Sigma (Sigma Set IsLattice) (\ { (A , LA) -> IsDecLattice A {{LA}}})) n)
                  -> IsDecLattice ([[ t ]]t' (Vec.map proj1 (Vec.map proj1 AsLDL))) {{TypeLattice' t (Vec.map proj1 AsLDL)}}
  TypeDecLattice' Int AsLDL = SignDecLat
  TypeDecLattice' Bool AsLDL = BoolDecLat
  TypeDecLattice' (Var x) AsLDL = lookup-declat x AsLDL
  TypeDecLattice' (t *t s) AsLDL = CoalescedProdDecLat {{TypeLattice' t (Vec.map proj1 AsLDL)}} {{TypeLattice' s (Vec.map proj1 AsLDL)}}
                                                       {{TypeDecLattice' t AsLDL}} {{TypeDecLattice' s AsLDL}}
  TypeDecLattice' (t +t s) AsLDL = ProdDecLat {{TypeLattice' t (Vec.map proj1 AsLDL)}} {{TypeLattice' s (Vec.map proj1 AsLDL)}}
                                              {{TypeDecLattice' t AsLDL}} {{TypeDecLattice' s AsLDL}}
  TypeDecLattice' (Rec t) AsLDL = Fix#-DecLat {{\ {X#} LX# -> TypeLattice' t ((X# , LX#) :: Vec.map proj1 AsLDL)}}
                                              {{\ {X#} {{LX#}} DLX# -> TypeDecLattice' t (((X# , LX#) , DLX#) :: AsLDL)}}

  instance
    TypeDecLattice : {t : Type} -> IsDecLattice ([[ t ]]t) {{TypeLattice {t}}}
    TypeDecLattice {t} = TypeDecLattice' t []

  SynSemSub : forall {n As} {CsL : Vec (Sigma Set IsLattice) (suc n)} (t : Type' (suc n)) (t' : Type' n)
                     (CsAs : Vec.map proj1 CsL =~= As ++ Vec.[ [[ t' ]]t' As ])
                     -> Equiv ([[ t < t' > ]]t' As) ([[ t ]]t' (Vec.map proj1 CsL))
  SynSemSub {n} {As} {CsL} Int t' CsAs = equivalence F.id F.id
  SynSemSub {n} {As} {CsL} Bool t' CsAs = equivalence F.id F.id
  SynSemSub {n} {As} {CsL} (Var x) t' CsAs with (x ~F? fromNat n)
  SynSemSub {n} {As} {CsL} (Var .(fromNat n)) t' CsAs | yes refl =
    equivalence (subst F.id (P.sym (lookup-last {n} {As} CsAs))) (subst F.id (lookup-last {n} {As} CsAs))
    where lookup-last : forall {n} {As : Vec Set n} {B : Set} {CsL : Vec Set (suc n)} (CsAsB : CsL =~= As ++ Vec.[ B ]) -> lookup (fromNat n) CsL =~= B
          lookup-last {zero} {[]} {B} {.(B :: [])} refl = refl
          lookup-last {suc n} {A :: As} {B} {C :: CsL} CsAsB = lookup-last {n} {As} {B} {CsL} (::-inj2 CsAsB)
  SynSemSub {n} {As} {CsL} (Var x) t' CsAs | no contra =
    equivalence (subst F.id (lookup-strengthen CsAs)) (subst F.id (P.sym (lookup-strengthen CsAs)))
    where lookup-strengthen : forall {n} {x} {contra} {As : Vec Set n} {B : Set} {CsL : Vec Set (suc n)}
                              (CsAsB : CsL =~= As ++ Vec.[ B ]) -> lookup (strengthenF x contra) As =~= lookup x CsL
          lookup-strengthen {.0} {zero} {contra} {[]} {B} {C :: CsL} p = magic (contra refl)
          lookup-strengthen {.(suc _)} {zero} {contra} {A :: As} {B} {C :: CsL} p = ::-inj1 (P.sym p)
          lookup-strengthen {zero} {suc ()} {contra} {[]} {B} {CsL} p
          lookup-strengthen {suc n} {suc x} {contra} {A :: As} {B} {C :: CsL} p = lookup-strengthen (::-inj2 p)
  SynSemSub {n} {As} {CsL} (t *t s) t' CsAs =
    equivalence (\ tsv -> _,,_ {{TypeLattice' t CsL}} {{TypeLattice' s CsL}}
                               (Equivalence.to (SynSemSub t t' CsAs) <$> Abs.fst {{latt}} {{lats}} tsv)
                               (Equivalence.to (SynSemSub s t' CsAs) <$> Abs.snd {{latt}} {{lats}} tsv))
                (\ tsv -> _,,_ {{latt}} {{lats}}
                               (Equivalence.from (SynSemSub t t' CsAs) <$> Abs.fst {{TypeLattice' t CsL}} {{TypeLattice' s CsL}} tsv)
                               (Equivalence.from (SynSemSub s t' CsAs) <$> Abs.snd {{TypeLattice' t CsL}} {{TypeLattice' s CsL}} tsv))
    where latt-map : forall {n} {A} {As : Vec Set n} (CsL : Vec (Sigma Set IsLattice) (suc n)) (CsAs : Vec.map proj1 CsL =~= As ++ Vec.[ A ])
                     -> Vec (Sigma Set IsLattice) (n +N 1)
          latt-map {zero} {.C} {[]} ((C , LC) :: []) refl = Vec.[ ((C , LC)) ]
          latt-map {suc n} {A} {A2 :: As} ((C , LC) :: CsL) CsAs =
               (A2 , subst (\ x -> IsLattice x) (::-inj1 CsAs) LC) :: latt-map {n} {A} {As} CsL (::-inj2 CsAs)
          latt-map-prop : forall {n} {A} {As : Vec Set n} (CsL : Vec (Sigma Set IsLattice) (suc n)) (CsAs : Vec.map proj1 CsL =~= As ++ Vec.[ A ])
            -> Vec.map proj1 (Util.take n (latt-map {A = A} {As = As} CsL CsAs)) =~= As
          latt-map-prop {zero} {A} {[]} CsL CsAs = refl
          latt-map-prop {suc n} {A} {A2 :: As} ((C , LC) :: CsL) CsAs = P.cong (\ x -> A2 :: x) (latt-map-prop {n} {A} {As} CsL (::-inj2 CsAs))
          latt : IsLattice ([[ t < t' > ]]t' As)
          latt = subst (\ x -> IsLattice ([[ t < t' > ]]t' x)) (latt-map-prop {As = As} CsL CsAs)
                  (TypeLattice' (t < t' >) (Util.take n (latt-map {As = As} CsL CsAs)))
          lats : IsLattice ([[ s < t' > ]]t' As)
          lats = subst (\ x -> IsLattice ([[ s < t' > ]]t' x)) (latt-map-prop {As = As} CsL CsAs)
                  (TypeLattice' (s < t' >) (Util.take n (latt-map {As = As} CsL CsAs)))
  SynSemSub {n} {As} {CsL} (t +t s) t' CsAs =
    equivalence (\ { (tv , sv) -> Equivalence.to (SynSemSub t t' CsAs) <$> tv , Equivalence.to (SynSemSub s t' CsAs) <$> sv })
                (\ { (tv , sv) -> Equivalence.from (SynSemSub t t' CsAs) <$> tv , Equivalence.from (SynSemSub s t' CsAs) <$> sv })
  SynSemSub {n} {As} {CsL} (Rec t) t' CsAs = {!!}

  AbstractSemanticOps : SemanticOps
  AbstractSemanticOps = record
                          { [[_]]t' = [[_]]t'
                          ; I-num = fromInteger
                          ; _-I_ = Sign-minus
                          ; _+I_ = Sign-plus
                          ; _*I_ = Sign-mult
                          ; _<=I_ = Sign-leq
                          ; _~I_ = Sign-eq
                          ; B-tt = \ { true -> true ; false -> false }
                          ; B-ff =  \ { true -> false ; false -> true }
                          ; B-if = \ {t} f tv fv ->
                              let open IsLattice (TypeLattice {t})
                              in (B2.if (f true) then tv else bot) lub (B2.if f false then fv else bot)
                          ; P-pair = \ {t} {s} v1 v2 -> _,,_ {{TypeLattice {t}}} {{TypeLattice {s}}} v1 v2
                          ; P-fst = \ {t} {s} v -> Abs.fst {{TypeLattice {t}}} {{TypeLattice {s}}} v
                          ; P-snd = \ {t} {s} v -> Abs.snd {{TypeLattice {t}}} {{TypeLattice {s}}} v
                          ; S-left =  \ {t} {s} v -> v , IsLattice.bot (TypeLattice {s})
                          ; S-right = \ {t} {s} v -> IsLattice.bot (TypeLattice {t}) , v
                          ; S-case = \ { {t} {s} {w} (tv , sv) tf sf ->
                                    let open IsLattice (TypeLattice {w})
                                    in (B2.if (toBool (IsLattice.is-bot (TypeLattice {t}) tv)) then bot else tf tv) lub
                                       (B2.if (toBool (IsLattice.is-bot (TypeLattice {s}) sv)) then bot else sf sv)  }
                          ; S-abs = \ {t} -> case (depth , refl) return (\ (n : Sigma Nat (\ n -> n =~= depth)) -> [[ t < Rec t > ]]t' [] ->
                                                                            Fix# (\ B -> [[ t ]]t' (B :: [])) (proj1 n)) of (\
                                                               { (zero , refl) -> \ _ -> in-bot ;
                                                                 ((suc n) , p) -> \ x -> in-f# (Equivalence.to (SynSemSub t (Rec t) {!!}) <$> x)
                                                               })
                          ; S-rep = \ {t} -> {!!}
                          }
