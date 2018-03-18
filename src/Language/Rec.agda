module Language.Rec where

open import Data.Nat renaming (ℕ to Nat; _+_ to _+N_; _*_ to _*N_)
open import Data.Integer renaming (ℤ to Integer; _+_ to _+Z_; _*_ to _*Z_; _-_ to _-Z_; suc to isuc)
open import Data.List renaming (_∷_ to _::_)
open import Data.Vec renaming (_∷_ to _::_)
open import Data.Fin renaming (_+_ to _+F_; _-_ to _-F_; _≤_ to _<=F_; _≤?_ to _<=F?_; fromℕ to fromNat)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _~_)

open import Util renaming (_≟F_ to _~F?_)

infixr 6 _*t_
infixr 4 _+t_

data Type' (n : Nat) : Set where
  Int  : Type' n
  Bool : Type' n
  Var  : Fin n -> Type' n
  _*t_ _+t_  : Type' n -> Type' n -> Type' n
  Rec  : Type' (suc n) -> Type' n

Type : Set
Type = Type' zero

shiftVar : forall {n} -> Fin (suc n) -> Fin n -> Fin (suc n)
shiftVar c x with (c <=F? (weakenF x))
shiftVar c x | yes _ = suc x
shiftVar c x | no _ = weakenF x

shiftType : forall {n} -> Fin (suc n) -> Type' n -> Type' (suc n)
shiftType x Int = Int
shiftType x Bool = Bool
shiftType x (Var y) = Var (shiftVar x y)
shiftType x (t1 *t t2) = shiftType x t1 *t shiftType x t2
shiftType x (t1 +t t2) = shiftType x t1 +t shiftType x t2
shiftType x (Rec t) = Rec (shiftType (suc x) t)

substType : forall {n} -> Type' (suc n) -> Type' n -> Type' n
substType Int t' = Int
substType Bool t' = Bool
substType {n} (Var x) t' with (x ~F? (fromNat n))
substType {n} (Var x) t' | yes _ = t'
substType {n} (Var x) t' | no contra = Var (strengthenF x contra)
substType (t1 *t t2) t' = substType t1 t' *t substType t2 t'
substType (t1 +t t2) t' = substType t1 t' +t substType t2 t'
substType (Rec t) t' = Rec (substType t (shiftType zero t'))

record FunType : Set where
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
  _<=_ _==_ : A -> A -> LogicOp A

mutual
  data Expr {n m : Nat} (G : Ctx n) (D : FunCtx m) : Type -> Set where
    const : Integer -> Expr G D Int
    $_ : forall {t} (x : Fin n) {{tc : t ~ lookup x G}} -> Expr G D t
    [_]b : BinaryOp (Expr G D Int) -> Expr G D Int
    [_]l : LogicOp (Expr G D Int) -> Expr G D Bool
    if_then_else : forall {t} -> Expr G D Bool -> Expr G D t -> Expr G D t
    <_> : forall {ft} (f : Fin m) {{ftc : ft ~ lookup f D}} -> Exprs G D (argtys ft) -> Expr G D (returnty ft)
    _,_ : forall {t1 t2} -> Expr G D t1 -> Expr G D t2 -> Expr G D (t1 *t t2)
    fst : forall {t1 t2} -> Expr G D (t1 *t t2) -> Expr G D t1
    snd : forall {t1 t2} -> Expr G D (t1 *t t2) -> Expr G D t2
    inl : forall {t1 t2} -> Expr G D t1 -> Expr G D (t1 +t t2)
    inr : forall {t1 t2} -> Expr G D t2 -> Expr G D (t1 +t t2)
    case_of_or_ : forall {t1 t2 tr} -> Expr G D (t1 +t t2) -> Expr (t1 :: G) D tr -> Expr (t2 :: G) D tr -> Expr G D tr
    abs : forall {tx tr} {{tc : tr ~ substType tx (Rec tx)}} -> Expr G D tr -> Expr G D (Rec tx)
    rep : forall {tx tr} {{tc : tr ~ substType tx (Rec tx)}} -> Expr G D (Rec tx) -> Expr G D tr

  data Exprs {n m : Nat} (G : Ctx n) (D : FunCtx m) : List Type -> Set where
    [] : Exprs G D []
    _::_ : forall {t ts} -> Expr G D t -> Exprs G D ts -> Exprs G D (t :: ts)
