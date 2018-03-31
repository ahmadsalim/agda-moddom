module Language.Rec where

open import Data.Nat renaming (ℕ to Nat; _+_ to _+N_; _*_ to _*N_)
open import Data.Integer renaming (ℤ to Integer; _+_ to _+Z_; _*_ to _*Z_; _-_ to _-Z_; suc to isuc)
open import Data.List renaming (_∷_ to _::_)
open import Data.Vec as Vec renaming (_∷_ to _::_)
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

data BinaryOp (A : Set) : Set where
  _+_ _-_ _*_ : A -> A -> BinaryOp A

data LogicOp (A : Set) : Set where
  _<=_ _~_ : A -> A -> LogicOp A

data BoolOp (A : Set) : Set where
  _\/_ _/\_ : A -> A -> BoolOp A
  not : A -> BoolOp A

mutual
  data Expr {n : Nat} (G : Ctx n) (ft : FunType) : Type -> Set where
    const : Integer -> Expr G ft Int
    $_ : forall {t} (x : Fin n) {{tc : t == Vec.lookup x G}} -> Expr G ft t
    [_]2 : BinaryOp (Expr G ft Int) -> Expr G ft Int
    [_]l : LogicOp (Expr G ft Int) -> Expr G ft Bool
    [_]b : BoolOp (Expr G ft Bool) -> Expr G ft Bool
    true : Expr G ft Bool
    false : Expr G ft Bool
    lett_inn_ : forall {t1 t2} -> Expr G ft t1 -> Expr (t1 :: G) ft t2 -> Expr G ft t2
    if_then_else_ : forall {t} -> Expr G ft Bool -> Expr G ft t -> Expr G ft t -> Expr G ft t
    rec : Exprs G ft (argtys ft) -> Expr G ft (returnty ft)
    _,_ : forall {t1 t2} -> Expr G ft t1 -> Expr G ft t2 -> Expr G ft (t1 *t t2)
    fst : forall {t1 t2} -> Expr G ft (t1 *t t2) -> Expr G ft t1
    snd : forall {t1 t2} -> Expr G ft (t1 *t t2) -> Expr G ft t2
    inl : forall {t1 t2} -> Expr G ft t1 -> Expr G ft (t1 +t t2)
    inr : forall {t1 t2} -> Expr G ft t2 -> Expr G ft (t1 +t t2)
    case_of_or_ : forall {t1 t2 tr} -> Expr G ft (t1 +t t2) -> Expr (t1 :: G) ft tr -> Expr (t2 :: G) ft tr -> Expr G ft tr
    abs : forall {tx tr} {{tc : tr == tx < Rec tx >}} -> Expr G ft tr -> Expr G ft (Rec tx)
    rep : forall {tx tr} {{tc : tr == tx < Rec tx >}} -> Expr G ft (Rec tx) -> Expr G ft tr

  data Exprs {n : Nat} (G : Ctx n) (ft : FunType) : List Type -> Set where
    [] : Exprs G ft []
    _::_ : forall {t ts} -> Expr G ft t -> Exprs G ft ts -> Exprs G ft (t :: ts)

  record FunDef (ft : FunType) : Set where
    constructor <<_>>
    field
      rhs : Expr (fromList (argtys ft)) ft (returnty ft)
