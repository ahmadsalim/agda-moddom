module Language.Semantics where


open import Data.Integer renaming (ℤ to Integer; _+_ to _+Z_; _*_ to _*Z_; _-_ to _-Z_; suc to isuc;
                                   _≤?_ to _<=?Z_; _≟_ to _~?Z_)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin
open import Data.Unit renaming (⊤ to Unit)
open import Data.Bool as B2 renaming (Bool to B2)
open import Data.Empty renaming (⊥ to Empty; ⊥-elim to magic)
open import Data.Sum renaming (_⊎_ to Either; inj₁ to inj1; inj₂ to inj2)
open import Data.Product renaming (_×_ to _**_; Σ to Sigma; proj₁ to proj1; proj₂ to proj2)
open import Data.Vec as Vec renaming (_∷_ to _::_)
open import Data.Vec.All as VA renaming (_∷_ to _::_)
open import Relation.Nullary.Decidable as Dec renaming (⌊_⌋ to toBool)
open import Relation.Nullary
open import Relation.Binary.HeterogeneousEquality as P renaming (_≅_ to _=~=_; ≡-to-≅ to ==-to-=~=)
import Relation.Binary.PropositionalEquality as PE
open import Function as F renaming (_∋_ to the)
open import Function.Equality renaming (_⟨$⟩_ to _<$>_)
open import Function.Equivalence as E renaming (_⇔_ to Equiv; _∘_ to _o_)
import Level

open import Domains.Concrete
open import Domains.Abstract as Abs
open import Language.Rec
open import Util renaming (_≟F_ to _~F?_)

record SemanticOps : Set1 where
  field
    [[_]]t : Type -> Set

  field
    I-num : Integer -> [[ Int ]]t

    _-I_ _+I_ _*I_ : [[ Int ]]t -> [[ Int ]]t -> [[ Int ]]t
    _<=I_ _~I_ : [[ Int ]]t -> [[ Int ]]t -> [[ Bool ]]t

    B-tt B-ff : [[ Bool ]]t
    B-if : forall {t} -> [[ Bool ]]t -> [[ t ]]t -> [[ t ]]t -> [[ t ]]t

    P-pair : forall {t s} -> [[ t ]]t -> [[ s ]]t -> [[ t *t s ]]t
    P-fst : forall {t s} ->  [[ t *t s ]]t -> [[ t ]]t
    P-snd : forall {t s} -> [[ t *t s ]]t -> [[ s ]]t

    E-left : forall {t s} -> [[ t ]]t -> [[ t +t s ]]t
    E-right : forall {t s} -> [[ s ]]t -> [[ t +t s ]]t
    E-case : forall {t s w} -> [[ t +t s ]]t -> ([[ t ]]t -> [[ w ]]t)
                                             -> ([[ s ]]t -> [[ w ]]t)
                                             -> [[ w ]]t

    S-abs : forall {t} -> [[ t < Rec t > ]]t -> [[ Rec t ]]t
    S-rep : forall {t} -> [[ Rec t ]]t -> [[ t < Rec t > ]]t

module ConcreteOps where
  open Equivalence

  [[_]]t' : Type' opn -> Set -> Set
  [[ Int ]]t' A = Integer
  [[ Bool ]]t' A = B2
  [[ Var ]]t' A = A
  [[ t *t s ]]t' A = ([[ t ]]t' A) ** ([[ s ]]t' A)
  [[ t +t s ]]t' A = Either ([[ t ]]t' A) ([[ s ]]t' A)

  [[_]]t : Type' cls -> Set
  [[ Int ]]t = Integer
  [[ Bool ]]t = B2
  [[ t *t s ]]t = [[ t ]]t ** [[ s ]]t
  [[ t +t s ]]t = Either [[ t ]]t [[ s ]]t
  [[ Rec t ]]t = Fix [[ t ]]t'

  mutual
    fix : forall {i} {A} (f : A -> A) -> Delay i A
    fix f = later (fix' f) Delays.>>= (\ x -> now (f x))

    fix' : forall {i} {A} (f : A -> A) -> InfDelay i A
    InfDelay.force (fix' f) = fix f

  SynSemSub : forall t t' -> Equiv [[ t < t' > ]]t ([[ t ]]t' [[ t' ]]t)
  SynSemSub Int t' = equivalence F.id F.id
  SynSemSub Bool t' = equivalence F.id F.id
  SynSemSub Var t' = equivalence F.id F.id
  SynSemSub (t *t s) t' =
    equivalence (\ { (tv , sv) -> to (SynSemSub t t') <$> tv , to (SynSemSub s t') <$> sv })
                (\ { (tv , sv) -> from (SynSemSub t t') <$> tv , from (SynSemSub s t') <$> sv } )
  SynSemSub (t +t s) t' =
    equivalence (\ { (inj1 tv) -> inj1 (to (SynSemSub t t') <$> tv) ; (inj2 sv) -> inj2 (to (SynSemSub s t') <$> sv) })
                (\ { (inj1 tv) -> inj1 (from (SynSemSub t t') <$> tv) ; (inj2 sv) -> inj2 (from (SynSemSub s t') <$> sv) })
  ConcreteSemanticOps : SemanticOps
  ConcreteSemanticOps = record
                          { [[_]]t = [[_]]t
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
                          ; E-left = inj1
                          ; E-right = inj2
                          ; E-case =
                             \ v c1 c2 ->
                               case v of \ {
                                  (inj1 x) -> c1 x;
                                  (inj2 y) -> c2 y
                                }
                          ; S-abs = \ {t} x -> in-f (to (SynSemSub t (Rec t)) <$> x)
                          ; S-rep = \ {t} x -> from (SynSemSub t (Rec t)) <$> Fix.out-f x
                          }

module AbstractOps (depth : Nat) where
  open Equivalence

  [[_]]t' : Type' opn -> Set -> Set
  [[ Int ]]t' A = Sign
  [[ Bool ]]t' A = B2 -> B2
  [[ Var ]]t' A = A
  [[ t *t s ]]t' A = [[ t ]]t' A *O* [[ s ]]t' A
  [[ t +t s ]]t' A = [[ t ]]t' A ** [[ s ]]t' A

  [[_]]t : Type' cls -> Set
  [[ Int ]]t = Sign
  [[ Bool ]]t = B2 -> B2
  [[ t *t s ]]t = [[ t ]]t *O* [[ s ]]t
  [[ t +t s ]]t = [[ t ]]t ** [[ s ]]t
  [[ Rec t ]]t = Fix# [[ t ]]t' depth

  TypeLattice' : forall {t} {A} -> IsLattice A -> IsLattice ([[ t ]]t' A)
  TypeLattice' {Int} LA = SignLat
  TypeLattice' {Bool} LA = BoolLat
  TypeLattice' {Var} LA = LA
  TypeLattice' {t *t s} LA = CoalescedProdLat {{TypeLattice' {t} LA}} {{TypeLattice' {s} LA}}
  TypeLattice' {t +t s} LA = ProdLat {{TypeLattice' {t} LA}} {{TypeLattice' {s} LA}}

  instance
    TypeLattice : forall {t} -> IsLattice ([[ t ]]t)
    TypeLattice {Int} = SignLat
    TypeLattice {Bool} = BoolLat
    TypeLattice {t *t s} = CoalescedProdLat
    TypeLattice {t +t s} = ProdLat
    TypeLattice {Rec t} = Fix#-Lat {{TypeLattice' {t}}}

  tmap : forall {A B : Set} {{LA : IsLattice A}} {{LB : IsLattice B}} t -> (f : A -> B) → [[ t ]]t' A → [[ t ]]t' B
  tmap Int f v = v
  tmap Bool f v = v
  tmap Var f v = f v
  tmap {{LA}} {{LB}} (t *t s) f v =
    _,,_ {{TypeLattice' {t} LB}} {{TypeLattice' {s} LB}}
    (tmap {{LA}} {{LB}} t f (Abs.fst {{TypeLattice' {t} LA}} {{TypeLattice' {s} LA}} v))
    (tmap {{LA}} {{LB}} s f (Abs.snd {{TypeLattice' {t} LA}} {{TypeLattice' {s} LA}} v))
  tmap {{LA}} {{LB}} (t +t s) f (tv , sv) = tmap {{LA}} {{LB}} t f tv , tmap {{LA}} {{LB}} s f sv

  TypeDecLattice' : forall {A} {{LA : IsLattice A}} {{DLA : IsDecLattice A {{LA}}}}
                    {t} -> IsDecLattice ([[ t ]]t' A) {{TypeLattice' {t} LA}}
  TypeDecLattice' {A} {{LA}} {{DLA}} {Int} = SignDecLat
  TypeDecLattice' {A} {{LA}} {{DLA}} {Bool} = BoolDecLat
  TypeDecLattice' {A} {{LA}} {{DLA}} {Var} = DLA
  TypeDecLattice' {A} {{LA}} {{DLA}} {t *t s} =
    CoalescedProdDecLat {{TypeLattice' {t} LA}} {{TypeLattice' {s} LA}}
                        {{TypeDecLattice' {{LA}} {{DLA}} {t}}} {{TypeDecLattice' {{LA}} {{DLA}} {s}}}
  TypeDecLattice' {A} {{LA}} {{DLA}} {t +t s} =
    ProdDecLat {{TypeLattice' {t} LA}} {{TypeLattice' {s} LA}}
               {{TypeDecLattice' {{LA}} {{DLA}} {t}}} {{TypeDecLattice' {{LA}} {{DLA}} {s}}}

  instance
    TypeDecLattice : forall {t} -> IsDecLattice [[ t ]]t
    TypeDecLattice {Int} = SignDecLat
    TypeDecLattice {Bool} = BoolDecLat
    TypeDecLattice {t *t s} = CoalescedProdDecLat
    TypeDecLattice {t +t s} = ProdDecLat
    TypeDecLattice {Rec t} = Fix#-DecLat {{TypeLattice' {t}}} {{\ {X#} {{LX#}} DLX# -> TypeDecLattice' {{LX#}} {{DLX#}} {t}}}

  SynSemSub : forall t t' -> Equiv [[ t < t' > ]]t ([[ t ]]t' [[ t' ]]t)
  SynSemSub Int t' = equivalence F.id F.id
  SynSemSub Bool t' = equivalence F.id F.id
  SynSemSub Var t' = equivalence F.id F.id
  SynSemSub (t *t s) t' =
    equivalence (\ tsv -> _,,_ {{TypeLattice' {t} TypeLattice}} {{TypeLattice' {s} TypeLattice}}
                               (to (SynSemSub t t') <$> Abs.fst tsv) (to (SynSemSub s t') <$> Abs.snd tsv))
                (\ tsv -> (from (SynSemSub t t') <$> Abs.fst {{TypeLattice' {t} TypeLattice}} {{TypeLattice' {s} TypeLattice}} tsv) ,,
                          (from (SynSemSub s t') <$> Abs.snd {{TypeLattice' {t} TypeLattice}} {{TypeLattice' {s} TypeLattice}} tsv))
  SynSemSub (t +t s) t' =
    equivalence (\ { (tv , sv) -> to (SynSemSub t t') <$> tv , to (SynSemSub s t') <$> sv })
                (\ { (tv , sv) -> from (SynSemSub t t') <$> tv , from (SynSemSub s t') <$> sv } )
  AbstractSemanticOps : SemanticOps
  AbstractSemanticOps = record
                          { [[_]]t = [[_]]t
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
                          ; E-left =  \ {t} {s} v -> v , IsLattice.bot (TypeLattice {s})
                          ; E-right = \ {t} {s} v -> IsLattice.bot (TypeLattice {t}) , v
                          ; E-case = \ { {t} {s} {w} (tv , sv) tf sf ->
                                    let open IsLattice (TypeLattice {w})
                                    in (B2.if (toBool (IsLattice.is-bot (TypeLattice {t}) tv)) then bot else tf tv) lub
                                       (B2.if (toBool (IsLattice.is-bot (TypeLattice {s}) sv)) then bot else sf sv)  }
                          ; S-abs = (\ {t} -> absv {t})
                          ; S-rep = (\ {t} -> repv {t})
                          }
    where absv : forall {t} -> [[ t < Rec t > ]]t -> [[ Rec t ]]t
          absv {t} = case depth , refl return (\ (np : Sigma Nat (_=~= depth)) ->
                                                  [[ t < Rec t > ]]t -> Fix# (\ B -> [[ t ]]t' B) (proj1 np)) of (\ {
                                                    (zero , refl) -> \ _ -> in-bot ;
                                                    (suc n , p) -> \ v ->
                                                      let nv : [[ t ]]t' (Fix# [[ t ]]t' (suc n))
                                                          nv = subst (\ m -> [[ t ]]t' (Fix# [[ t ]]t' m)) (P.sym p) (to (SynSemSub t (Rec t)) <$> v)
                                                      in in-f# (tmap {{Fix#-Lat {{TypeLattice' {t}}}}} {{Fix#-Lat {{TypeLattice' {t}}}}} t
                                                                (from (FixEquiv {{TypeLattice' {t}}}
                                                                      (\ {A} {B} {{LA}} {{LB}} -> tmap {A} {B} {{LA}} {{LB}} t)) <$>_) nv)
                                                  })
          repv : forall {t} -> [[ Rec t ]]t -> [[ t < Rec t > ]]t
          repv {t} in-bot = IsLattice.bot (TypeLattice {t < Rec t >})
          repv {t} (in-f# x) = from (SynSemSub t (Rec t)) <$>
                                 tmap {{Fix#-Lat {{TypeLattice' {t}}}}} {{Fix#-Lat {{TypeLattice' {t}}}}} t
                                      (to (FixEquiv {{TypeLattice' {t}}} (\ {A} {B} {{LA}} {{LB}} -> tmap {A} {B} {{LA}} {{LB}} t)) <$>_) x

module Semantics (Ops : SemanticOps) where
  open SemanticOps Ops
  open FunType

  [[_]]G : forall {n} (G : Ctx n) -> Set
  [[ G ]]G = VA.All [[_]]t G

  [[_]]ft : FunType -> Set
  [[ ft ]]ft = VA.All [[_]]t (fromList (argtys ft)) -> [[ returnty ft ]]t

  [[_]]D : forall {m} (D : FunCtx m) -> Set
  [[ D ]]D = VA.All [[_]]ft D

  mutual
    [[_]]e : forall {n} {m} {G : Ctx n} {D : FunCtx m} {t} (e : Expr G D t) -> [[ G ]]G -> [[ D ]]D -> [[ t ]]t
    [[ Expr.const x ]]e g d = I-num x
    [[ ($ x) {{PE.refl}} ]]e g d = VA.lookup x g
    [[ [ x + y ]b ]]e g d = [[ x ]]e g d +I [[ y ]]e g d
    [[ [ x - y ]b ]]e g d = [[ x ]]e g d -I [[ y ]]e g d
    [[ [ x * y ]b ]]e g d = [[ x ]]e g d *I [[ y ]]e g d
    [[ [ x <= y ]l ]]e g d = [[ x ]]e g d <=I [[ y ]]e g d
    [[ [ x ~ y ]l ]]e g d = [[ x ]]e g d ~I [[ y ]]e g d
    [[ if e then et else ef ]]e g d = B-if ([[ e ]]e g d)
                                          ([[ et ]]e g d)
                                          ([[ ef ]]e g d)
    [[ _!_ f {{PE.refl}} es ]]e g d = VA.lookup f d ([[ es ]]es g d)
    [[ e1 , e2 ]]e g d = P-pair ([[ e1 ]]e g d) ([[ e2 ]]e g d)
    [[ Expr.fst e ]]e g d = P-fst ([[ e ]]e g d)
    [[ Expr.snd e ]]e g d = P-snd ([[ e ]]e g d)
    [[ inl e ]]e g d = E-left ([[ e ]]e g d)
    [[ inr e ]]e g d = E-right ([[ e ]]e g d)
    [[ case e of el or er ]]e g d = E-case ([[ e ]]e g d)
                                          (\ vl -> [[ el ]]e (vl :: g) d)
                                          (\ vr -> [[ er ]]e (vr :: g) d)
    [[ abs {{PE.refl}} e ]]e g d = S-abs ([[ e ]]e g d)
    [[ rep {{PE.refl}} e ]]e g d = S-rep ([[ e ]]e g d)

    [[_]]es : forall {n} {m} {G : Ctx n} {D : FunCtx m} {ts}
             (es : Exprs G D ts) -> [[ G ]]G -> [[ D ]]D -> VA.All [[_]]t (fromList ts)
    [[ [] ]]es g d = []
    [[ e :: es ]]es g d = [[ e ]]e g d :: [[ es ]]es g d

    [[_]]p : forall {m} {D : FunCtx m} {k} {D2 : FunCtx k} -> ProgDef D D2 -> [[ D ]]D -> [[ D2 ]]D
    [[ [] ]]p d = []
    [[ fd :: fds ]]p d = (\ avs -> [[ fd ]]e avs d) :: [[ fds ]]p d

    [[_]] : forall {m} {D : FunCtx m} -> Prog D -> [[ D ]]D -> [[ D ]]D
    [[ P ]] = [[ P ]]p
