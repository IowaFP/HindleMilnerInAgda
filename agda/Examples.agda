module Examples where

open import Prelude 
open import Syntax
open AList ℕ _≟_
open import Unification
open import W
open import Print

--------------------------------------------------------------------------------
-- ∅ ⊢ λ x. x : ∀ α. α → α

id : Expr
id = `λ 0 (` 0)

empty : TypeAss
empty = ∅

ty = 𝒲 empty id
S = fst ty
τ = snd ty

_ : print (mgt id) ≡ "∀ {b} (b → b)"
_ = refl
--------------------------------------------------------------------------------
-- Church naturals.

C0 : Expr
C0 = `λ 1 (`λ 0 (` 0))

_ : print (mgt C0) ≡ "∀ {b,c} (b → (c → c))"
_ = refl

C1 : Expr
C1 = `λ 1
       (`λ 0
         ((` 1) · (` 0)))
_ : print (mgt C1) ≡ "∀ {c} ((c → c) → (c → c))"
_ = refl

--------------------------------------------------------------------------------
-- let polymorphic terms.

-- λ x. x
--   (let
--     f := λ x. x
--   In (f · (λ x. x)) (f tt))
M : String
M = print (mgt
  (`λ 10
    (` 10 ·
      (Let
        0 := (`λ 1 (` 1))
        In
          (((` 0) · (`λ 2 (` 2))) · ((` 0) · tt))))))




