module Language.Rec where

open import Data.Nat renaming (ℕ to Nat; _+_ to _+N_; _*_ to _*N_)
open import Data.Integer renaming (ℤ to Integer; _+_ to _+Z_; _*_ to _*Z_; _-_ to _-Z_; suc to isuc)
open import Data.List renaming (_∷_ to _::_)
open import Data.Vec renaming (_∷_ to _::_)
open import Data.Fin renaming (_+_ to _+F_; _-_ to _-F_; _≤_ to _<=F_; _≤?_ to _<=F?_; fromℕ to fromNat)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)

open import Util renaming (_≟F_ to _~F?_)

infixr 6 _*t_
infixr 4 _+t_

data State : Set where opn cls : State

data Type' : State -> Set where
  Int  : Type' cls
  Bool : Type' cls
  Const : Type' cls -> Type' opn
  Var  : Type' opn
  _*t_ _+t_  : forall {s} -> Type' s -> Type' s -> Type' s
  Rec  : Type' opn -> Type' cls

Type : Set
Type = Type' cls

_<_> : Type' opn -> Type' cls -> Type' cls
Var < t' > = t'
(Const t) < t' > = t
(t1 *t t2) < t' > = t1 < t' > *t t2 < t' >
(t1 +t t2) < t' > = t1 < t' > +t t2 < t' >

record FunType : Set where
  constructor _==>_
  field
    argtys   : List Type
    returnty : Type
open FunType

Ctx : Nat -> Set
Ctx n = Vec Type n

FunCtx : Nat -> Set
FunCtx n = Vec FunType n

data BinaryOp (A : Set) : Set where
  _+_ _-_ _*_ : A -> A -> BinaryOp A

data LogicOp (A : Set) : Set where
  _<=_ _~_ : A -> A -> LogicOp A

data BoolOp (A : Set) : Set where
  _\/_ _/\_ : A -> A -> BoolOp A
  not : A -> BoolOp A

mutual
  data Expr {n m : Nat} (G : Ctx n) (D : FunCtx m) : Type -> Set where
    const : Integer -> Expr G D Int
    $_ : forall {t} (x : Fin n) {{tc : t == lookup x G}} -> Expr G D t
    [_]2 : BinaryOp (Expr G D Int) -> Expr G D Int
    [_]l : LogicOp (Expr G D Int) -> Expr G D Bool
    [_]b : BoolOp (Expr G D Bool) -> Expr G D Bool
    true : Expr G D Bool
    false : Expr G D Bool
    lett_inn_ : forall {t1 t2} -> Expr G D t1 -> Expr (t1 :: G) D t2 -> Expr G D t2
    if_then_else_ : forall {t} -> Expr G D Bool -> Expr G D t -> Expr G D t -> Expr G D t
    _!_ : forall {ft} (f : Fin m) {{ftc : ft == lookup f D}} -> Exprs G D (argtys ft) -> Expr G D (returnty ft)
    _,_ : forall {t1 t2} -> Expr G D t1 -> Expr G D t2 -> Expr G D (t1 *t t2)
    fst : forall {t1 t2} -> Expr G D (t1 *t t2) -> Expr G D t1
    snd : forall {t1 t2} -> Expr G D (t1 *t t2) -> Expr G D t2
    inl : forall {t1 t2} -> Expr G D t1 -> Expr G D (t1 +t t2)
    inr : forall {t1 t2} -> Expr G D t2 -> Expr G D (t1 +t t2)
    case_of_or_ : forall {t1 t2 tr} -> Expr G D (t1 +t t2) -> Expr (t1 :: G) D tr -> Expr (t2 :: G) D tr -> Expr G D tr
    abs : forall {tx tr} {{tc : tr == tx < Rec tx >}} -> Expr G D tr -> Expr G D (Rec tx)
    rep : forall {tx tr} {{tc : tr == tx < Rec tx >}} -> Expr G D (Rec tx) -> Expr G D tr

  data Exprs {n m : Nat} (G : Ctx n) (D : FunCtx m) : List Type -> Set where
    [] : Exprs G D []
    _::_ : forall {t ts} -> Expr G D t -> Exprs G D ts -> Exprs G D (t :: ts)

  data ProgDef {m} (D : FunCtx m) : {n : Nat} -> FunCtx n -> Set where
    [] : ProgDef D []
    _::_ : forall {n} {ft} {fts : FunCtx n} -> Expr (fromList (argtys ft)) D (returnty ft) -> ProgDef D fts -> ProgDef D (ft :: fts)

  Prog : {n : Nat} -> FunCtx n -> Set
  Prog D = ProgDef D D
