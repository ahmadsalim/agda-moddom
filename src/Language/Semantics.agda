module Language.Semantics where


open import Data.Integer renaming (ℤ to Integer; _+_ to _+Z_; _*_ to _*Z_; _-_ to _-Z_; suc to isuc;
                                   _≤?_ to _<=?Z_; _≟_ to _~?Z_)
open import Data.Nat renaming (ℕ to Nat)
open import Data.Fin
open import Data.Maybe
open import Data.Unit renaming (⊤ to Unit)
open import Data.Bool as B2 renaming (Bool to B2)
open import Data.Empty renaming (⊥ to Empty; ⊥-elim to magic)
open import Data.Sum renaming (_⊎_ to Either; inj₁ to inj1; inj₂ to inj2)
open import Data.Product renaming (_×_ to _**_; Σ to Sigma; proj₁ to proj1; proj₂ to proj2)
open import Data.List as List
open import Data.Vec as Vec renaming (_∷_ to _::_) hiding (_>>=_)
open import Data.Vec.All as VA renaming (_∷_ to _::_)
open import Relation.Nullary.Decidable as Dec renaming (⌊_⌋ to toBool)
open import Relation.Nullary
open import Relation.Binary.HeterogeneousEquality as P renaming (_≅_ to _=~=_; ≡-to-≅ to ==-to-=~=)
import Relation.Binary.PropositionalEquality as PE renaming (_≡_ to _==_)
open import Function as F renaming (_∋_ to the)
open import Function.Equality renaming (_⟨$⟩_ to _<$$>_)
open import Function.Equivalence as E renaming (_⇔_ to Equiv; _∘_ to _o_)
import Level
open import Size

open import Category.Monad
open import Category.Applicative
open import Category.Functor

open import Domains.Concrete
open import Domains.Abstract as Abs
open import Language.Rec
open import Util renaming (_≟F_ to _~F?_)

record SemanticOps (m : Set -> Set) : Set1 where
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
    E-case : forall {t s w} -> [[ t +t s ]]t -> ([[ t ]]t -> m [[ w ]]t)
                                             -> ([[ s ]]t -> m [[ w ]]t)
                                             -> m [[ w ]]t

    S-abs : forall {t} -> [[ t < Rec t > ]]t -> [[ Rec t ]]t
    S-rep : forall {t} -> [[ Rec t ]]t -> [[ t < Rec t > ]]t

module Fixing where
  mutual
    fix : forall {i} {A} (f : A -> A) -> Delay i A
    fix f = later (fix' f) Delays.>>= (\ x -> now (f x))

    fix' : forall {i} {A} (f : A -> A) -> InfDelay i A
    InfDelay.force (fix' f) = fix f

module ConcreteOps where
  open Equivalence

  mutual
    [[_]]t' : Type' opn -> Set -> Set
    [[ Var ]]t' A = A
    [[ Const t ]]t' A = [[ t ]]t
    [[ t *t s ]]t' A = ([[ t ]]t' A) ** ([[ s ]]t' A)
    [[ t +t s ]]t' A = Either ([[ t ]]t' A) ([[ s ]]t' A)

    [[_]]t : Type' cls -> Set
    [[ Int ]]t = Integer
    [[ Bool ]]t = B2
    [[ t *t s ]]t = [[ t ]]t ** [[ s ]]t
    [[ t +t s ]]t = Either [[ t ]]t [[ s ]]t
    [[ Rec t ]]t = Fix [[ t ]]t'

  SynSemSub : forall t t' -> Equiv [[ t < t' > ]]t ([[ t ]]t' [[ t' ]]t)
  SynSemSub (Const t) t' = equivalence F.id F.id
  SynSemSub Var t' = equivalence F.id F.id
  SynSemSub (t *t s) t' =
    equivalence (\ { (tv , sv) -> to (SynSemSub t t') <$$> tv , to (SynSemSub s t') <$$> sv })
                (\ { (tv , sv) -> from (SynSemSub t t') <$$> tv , from (SynSemSub s t') <$$> sv } )
  SynSemSub (t +t s) t' =
    equivalence (\ { (inj1 tv) -> inj1 (to (SynSemSub t t') <$$> tv) ; (inj2 sv) -> inj2 (to (SynSemSub s t') <$$> sv) })
                (\ { (inj1 tv) -> inj1 (from (SynSemSub t t') <$$> tv) ; (inj2 sv) -> inj2 (from (SynSemSub s t') <$$> sv) })
  ConcreteSemanticOps : forall {m} -> SemanticOps m
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
                          ; S-abs = \ {t} x -> in-f (to (SynSemSub t (Rec t)) <$$> x)
                          ; S-rep = \ {t} x -> from (SynSemSub t (Rec t)) <$$> Fix.out-f x
                          }

module AbstractOps (depth : Nat) where
  open Equivalence

  mutual
    [[_]]t' : Type' opn -> Set -> Set
    [[ Const t ]]t' A = [[ t ]]t
    [[ Var ]]t' A = A
    [[ t *t s ]]t' A = [[ t ]]t' A *O* [[ s ]]t' A
    [[ t +t s ]]t' A = [[ t ]]t' A ** [[ s ]]t' A

    [[_]]t : Type' cls -> Set
    [[ Int ]]t = Sign
    [[ Bool ]]t = B2 -> B2
    [[ t *t s ]]t = [[ t ]]t *O* [[ s ]]t
    [[ t +t s ]]t = [[ t ]]t ** [[ s ]]t
    [[ Rec t ]]t = Fix# [[ t ]]t' depth

  mutual
    TypeLattice' : forall {t} {A} -> IsLattice A -> IsLattice ([[ t ]]t' A)
    TypeLattice' {Const t} LA = TypeLattice {t}
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
  tmap (Const t) f v = v
  tmap Var f v = f v
  tmap {{LA}} {{LB}} (t *t s) f v =
    _,,_ {{TypeLattice' {t} LB}} {{TypeLattice' {s} LB}}
    (tmap {{LA}} {{LB}} t f (Abs.fst {{TypeLattice' {t} LA}} {{TypeLattice' {s} LA}} v))
    (tmap {{LA}} {{LB}} s f (Abs.snd {{TypeLattice' {t} LA}} {{TypeLattice' {s} LA}} v))
  tmap {{LA}} {{LB}} (t +t s) f (tv , sv) = tmap {{LA}} {{LB}} t f tv , tmap {{LA}} {{LB}} s f sv

  mutual
    TypeDecLattice' : forall {A} {{LA : IsLattice A}} {{DLA : IsDecLattice A {{LA}}}}
                      {t} -> IsDecLattice ([[ t ]]t' A) {{TypeLattice' {t} LA}}
    TypeDecLattice' {A} {{LA}} {{DLA}} {Const t} = TypeDecLattice {t}
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
  SynSemSub (Const t) t' = equivalence F.id F.id
  SynSemSub Var t' = equivalence F.id F.id
  SynSemSub (t *t s) t' =
    equivalence (\ tsv -> _,,_ {{TypeLattice' {t} TypeLattice}} {{TypeLattice' {s} TypeLattice}}
                               (to (SynSemSub t t') <$$> Abs.fst tsv) (to (SynSemSub s t') <$$> Abs.snd tsv))
                (\ tsv -> (from (SynSemSub t t') <$$> Abs.fst {{TypeLattice' {t} TypeLattice}} {{TypeLattice' {s} TypeLattice}} tsv) ,,
                          (from (SynSemSub s t') <$$> Abs.snd {{TypeLattice' {t} TypeLattice}} {{TypeLattice' {s} TypeLattice}} tsv))
  SynSemSub (t +t s) t' =
    equivalence (\ { (tv , sv) -> to (SynSemSub t t') <$$> tv , to (SynSemSub s t') <$$> sv })
                (\ { (tv , sv) -> from (SynSemSub t t') <$$> tv , from (SynSemSub s t') <$$> sv } )
  AbstractSemanticOps : forall {m : Set -> Set} {{RM : RawMonad m}} -> SemanticOps m
  AbstractSemanticOps {{RM}} = record
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
                                        open RawMonad RM renaming (_⊛_ to _<*>_)
                                    in (| _lub_ (B2.if (toBool (IsLattice.is-bot (TypeLattice {t}) tv)) then return bot else tf tv)
                                                (B2.if (toBool (IsLattice.is-bot (TypeLattice {s}) sv)) then return bot else sf sv) |)  }
                          ; S-abs = (\ {t} -> absv {t})
                          ; S-rep = (\ {t} -> repv {t})
                          }
    where absv : forall {t} -> [[ t < Rec t > ]]t -> [[ Rec t ]]t
          absv {t} = case depth , refl return (\ (np : Sigma Nat (_=~= depth)) ->
                                                  [[ t < Rec t > ]]t -> Fix# (\ B -> [[ t ]]t' B) (proj1 np)) of (\ {
                                                    (zero , refl) -> \ _ -> in-bot ;
                                                    (suc n , p) -> \ v ->
                                                      let nv : [[ t ]]t' (Fix# [[ t ]]t' (suc n))
                                                          nv = subst (\ m -> [[ t ]]t' (Fix# [[ t ]]t' m)) (P.sym p) (to (SynSemSub t (Rec t)) <$$> v)
                                                      in in-f# (tmap {{Fix#-Lat {{TypeLattice' {t}}}}} {{Fix#-Lat {{TypeLattice' {t}}}}} t
                                                                (from (FixEquiv {{TypeLattice' {t}}}
                                                                      (\ {A} {B} {{LA}} {{LB}} -> tmap {A} {B} {{LA}} {{LB}} t)) <$$>_) nv)
                                                  })
          repv : forall {t} -> [[ Rec t ]]t -> [[ t < Rec t > ]]t
          repv {t} in-bot = IsLattice.bot (TypeLattice {t < Rec t >})
          repv {t} (in-f# x) = from (SynSemSub t (Rec t)) <$$>
                                 tmap {{Fix#-Lat {{TypeLattice' {t}}}}} {{Fix#-Lat {{TypeLattice' {t}}}}} t
                                      (to (FixEquiv {{TypeLattice' {t}}} (\ {A} {B} {{LA}} {{LB}} -> tmap {A} {B} {{LA}} {{LB}} t)) <$$>_) x

module Semantics (Ops : forall i -> SemanticOps (Delay i)) where
  open FunType

  [[_]]G : forall {n} (G : Ctx n) (i : Size) -> Set
  [[ G ]]G i = VA.All [[_]]t G
    where open SemanticOps (Ops i)

  [[_]]ft : FunType -> Size -> Set
  [[ ft ]]ft i = VA.All [[_]]t (fromList (argtys ft)) -> Delay i [[ returnty ft ]]t
    where open SemanticOps (Ops i)

  open RawMonad {{...}} renaming (_⊛_ to _<*>_)

  mutual
    [[_]]e : forall {n} {G : Ctx n} {ft} {t} (e : Expr G ft t) {i} -> [[ G ]]G i -> [[ ft ]]ft i -> Delay i (SemanticOps.[[_]]t (Ops i) t)
    [[ const n ]]e {i} g f = (| (I-num n) |)
      where open SemanticOps (Ops i)
    [[ ($ x) {{PE.refl}} ]]e g f = (| (VA.lookup x g) |)
    [[ [ x + y ]2 ]]e {i} g f = (| [[ x ]]e g f +I [[ y ]]e g f |)
      where open SemanticOps (Ops i)
    [[ [ x - y ]2 ]]e {i} g f = (| [[ x ]]e g f -I [[ y ]]e g f |)
      where open SemanticOps (Ops i)
    [[ [ x * y ]2 ]]e {i} g f = (| [[ x ]]e g f *I [[ y ]]e g f |)
      where open SemanticOps (Ops i)
    [[ [ x <= y ]l ]]e {i} g f = (| [[ x ]]e g f <=I [[ y ]]e g f |)
      where open SemanticOps (Ops i)
    [[ [ x \/ y ]b ]]e {i} g f = (| B-if ([[ x ]]e g f) ([[ y ]]e g f) (| B-ff |) |)
      where open SemanticOps (Ops i)
    [[ [ x /\ y ]b ]]e {i} g f = do
        v <- [[ x ]]e {i} g f
        (| B-if (| v |) (| B-tt |) ([[ y ]]e g f) |)
      where open SemanticOps (Ops i)
    [[ [ not x ]b ]]e {i} g f = do
        v <- [[ x ]]e g f
        (| (B-if v B-ff B-tt) |)
      where open SemanticOps (Ops i)
    [[ true ]]e {i} g f = (| B-tt |)
      where open SemanticOps (Ops i)
    [[ false ]]e {i} g f = (| B-ff |)
      where open SemanticOps (Ops i)
    [[ [ x ~ y ]l ]]e {i} g f = (| [[ x ]]e g f ~I [[ y ]]e g f |)
      where open SemanticOps (Ops i)
    [[ lett eb inn er ]]e g f = do
       vb <- [[ eb ]]e g f
       [[ er ]]e (vb :: g) f
    [[ if e then et else ef ]]e {i }g f = (| B-if ([[ e ]]e g f)
                                            ([[ et ]]e g f)
                                            ([[ ef ]]e g f) |)
      where open SemanticOps (Ops i)
    [[ rec es ]]e g f = f =<< [[ es ]]es g f
    [[ e1 , e2 ]]e {i} g f = (| P-pair ([[ e1 ]]e g f) ([[ e2 ]]e g f) |)
      where open SemanticOps (Ops i)
    [[ fst e ]]e {i} g f = (| P-fst ([[ e ]]e g f) |)
      where open SemanticOps (Ops i)
    [[ snd e ]]e {i} g f = (| P-snd ([[ e ]]e g f) |)
      where open SemanticOps (Ops i)
    [[ inl e ]]e {i} g f = (| E-left ([[ e ]]e g f) |)
      where open SemanticOps (Ops i)
    [[ inr e ]]e {i} g f = (| E-right ([[ e ]]e g f) |)
      where open SemanticOps (Ops i)
    [[ case e of el or er ]]e {i} g f = do
        v <- [[ e ]]e g f
        E-case v (\ v1 -> [[ el ]]e (v1 :: g) f)
                 (\ v2 -> [[ er ]]e (v2 :: g) f)
      where open SemanticOps (Ops i)
    [[ abs {{PE.refl}} e ]]e {i} g f = (| S-abs ([[ e ]]e g f) |)
      where open SemanticOps (Ops i)
    [[ rep {{PE.refl}} e ]]e {i} g f = (| S-rep ([[ e ]]e g f) |)
      where open SemanticOps (Ops i)

    [[_]]es : forall {n} {i} {G : Ctx n} {ft} {ts}
             (es : Exprs G ft ts) -> [[ G ]]G i -> [[ ft ]]ft i -> Delay i (VA.All (SemanticOps.[[_]]t (Ops i)) (fromList ts))
    [[ [] ]]es g f = (| [] |)
    [[ e :: es ]]es g f = (| ([[ e ]]e g f) :: ([[ es ]]es g f) |)

module Example where
  natTy' : Type' opn
  natTy' = Const Bool +t Var

  natTy : Type
  natTy = Rec natTy'

  exprTy' : Type' opn
  exprTy' =     Const natTy -- Constant
             +t (Var *t Var) -- Times
             +t (Var *t Var) -- Plus
             +t Const Int -- Variable

  exprTy : Type
  exprTy = Rec exprTy'

  simpleExpr-sig : FunType
  simpleExpr-sig = List.[ exprTy ] ==> exprTy

  simpleExpr : FunDef simpleExpr-sig
  simpleExpr = <<
                  Expr.case rep {tx = exprTy'} {{PE.refl}} ($ zero)
                  of abs {{PE.refl}} (inl ($ zero))
                  or Expr.case ($_ zero {{PE.refl}})
                  of lett rec (Expr.fst ($_ zero {{PE.refl}}) :: [])
                      inn lett rec (Expr.snd ($_ (suc zero) {{PE.refl}}) :: [])
                      inn Expr.case rep {tx = exprTy'} {{PE.refl}} ($ suc zero) -- Pattern match on first to check whether constant
                          of Expr.case rep {tx = natTy'} {{PE.refl}} ($ zero) -- Check whether zero
                            of abs {{PE.refl}} (inl (abs {{PE.refl}} (inl true))) -- return zero
                            or Expr.case rep {tx = exprTy'} {{PE.refl}} ($ suc (suc zero)) -- Pattern match on second to check whether constant
                              of Expr.case rep {tx = natTy'} {{PE.refl}} ($ zero) -- Check whether zero
                                of abs {{PE.refl}} (inl (abs {{PE.refl}} (inl true))) -- return zero
                                or abs {{PE.refl}} (inr (inl (($ suc (suc (suc (suc (suc zero))))) , ($ suc (suc (suc (suc zero))))))) -- identity
                              or abs {{PE.refl}} (inr (inl (($ suc (suc (suc (suc zero)))) , ($ suc (suc (suc zero)))))) -- identity
                          or Expr.case rep {tx = exprTy'} {{PE.refl}} ($ suc zero) -- Pattern match on second to check whether constant
                          of Expr.case rep {tx = natTy'} {{PE.refl}} ($ zero) -- Check whether zero
                            of abs {{PE.refl}} (inl (abs {{PE.refl}} (inl true))) -- return zero
                            or abs {{PE.refl}} (inr (inl (($ suc (suc (suc (suc zero)))) , ($ suc (suc (suc zero)))))) -- identity
                          or abs {{PE.refl}} (inr (inl (($ suc (suc (suc zero))) , ($ suc (suc zero)))))
                  or Expr.case $_ zero {{PE.refl}}
                  of abs {{PE.refl}} (inr (inr (inl (rec (Expr.fst ($_ zero {{PE.refl}}) :: []) ,
                                                      rec (Expr.snd ($_ zero {{PE.refl}}) :: [])))))
                  or abs {{PE.refl}} (inr (inr (inr ($ zero))))
               >>

module Concrete where
  open ConcreteOps
  open Fixing
  open Semantics (\ i -> ConcreteSemanticOps {Delay i})
  [[_]] : forall {ft} (f : FunDef ft) {i} -> [[ ft ]]ft i
  [[ << rhs >> ]] {i} args = [[ rhs ]]e args (\ args -> later \ { .InfDelay.force -> [[ << rhs >> ]] args})

  simpleExprSem : [[ Example.simpleExpr-sig ]]ft _
  simpleExprSem = [[ Example.simpleExpr ]]

  seNat : Set
  seNat = Fix (\ A -> Either B2 A)

  seNatZero : seNat
  seNatZero = in-f (inj1 true)

  seNatSuc : seNat -> seNat
  seNatSuc n = in-f (inj2 n)

  seExpr : Set
  seExpr = Fix (\ A -> Either seNat (Either (A ** A) (Either (A ** A) Integer)))

  seExprCst : seNat -> seExpr
  seExprCst n = in-f (inj1 n)

  seExprTimes : seExpr -> seExpr -> seExpr
  seExprTimes x y = in-f (inj2 (inj1 (x , y)))

  seExprPlus : seExpr -> seExpr -> seExpr
  seExprPlus x y = in-f (inj2 (inj2 (inj1 (x , y))))

  seExprVar : Integer -> seExpr
  seExprVar i = in-f (inj2 (inj2 (inj2 i)))

  test1 : just (seExprCst (seNatSuc seNatZero)) PE.==
             Delays.run 1000 (simpleExprSem (seExprCst (seNatSuc seNatZero) :: []))
  test1 = PE.refl

  test2 : just (seExprPlus (seExprVar (+ 1)) (seExprCst seNatZero)) PE.==
             Delays.run 1000 (simpleExprSem ((seExprPlus (seExprVar (+ 1)) (seExprTimes (seExprCst seNatZero) (seExprVar (+ 0)))) :: []))
  test2 = PE.refl

module Abstract (depth : Nat) where
  open AbstractOps depth
  -- open Semantics AbstractSemanticOps

  --[[_]]# : forall {i} {m} {D : FunCtx m} -> Prog D -> Delay i [[ D ]]D
  --[[ P ]]# = {!!}
