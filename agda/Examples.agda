module Examples where

open import Prelude 
open import Syntax
open AList String _≟_
open import Unification
open import W
open import Print

--------------------------------------------------------------------------------
-- ∅ ⊢ λ x. x : ∀ α. α → α

id′ : Expr
id′ = `λ "x" (` "x")

empty : TypeAss
empty = ∅

ty = 𝒲 empty id′
S = fst ty
τ = snd ty

_ : print (mgt id′) ≡ "∀ {a} (a → a)"
_ = refl
--------------------------------------------------------------------------------
-- Church naturals.

C0 : Expr
C0 = `λ "x" (`λ "y" (` "y"))

_ : print (mgt C0) ≡ "∀ {b,c} (b → (c → c))"
_ = {!   !} -- refl

C1 : Expr
C1 = `λ "x"
       (`λ "y"
         ((` "x") · (` "y")))
_ : print (mgt C1) ≡ "∀ {c} ((c → c) → (c → c))"
_ = {!   !} -- refl

--------------------------------------------------------------------------------
-- let polymorphic terms.

-- λ x. x
--   (let
--     f := λ x. x
--   In (f · (λ x. x)) (f tt))
M : Expr 
M = 
  (`λ "x"
    (` "x" ·
      (Let
        "f" := (`λ "x" (` "x"))
        In
          (((` "f") · (`λ "x" (` "x"))) · ((` "f") · tt)))))

_ : print (mgt M) ≡ {! print (mgt M) !} 
_ = refl 




