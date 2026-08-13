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
id′ = `λ "x" ． ` "x"

empty : TypeAss
empty = ∅

ty = 𝒲 empty id′
S = fst ty
τ = snd ty

_ : show (mgt id′) ≡ "∀ {a} (a → a)"
_ = refl

-- --------------------------------------------------------------------------------
-- -- Church naturals.

C0 : Expr
C0 = `λ "x" ． `λ "y" ． ` "y"

_ : show (mgt C0) ≡ "∀ {a, b} (a → (b → b))"
_ = refl

C1 : Expr
C1 = `λ "f" ． `λ "x" ． ` "f" · ` "x"
_ : show (mgt C1) ≡ "∀ {b, c} ((b → c) → (b → c))"
_ = refl

-- --------------------------------------------------------------------------------
-- -- let polymorphic terms.

-- λ x. x
--   (let id := λ x. x In ((f (λ x. x)) (f tt)))
--     
--       
M : Expr 
M = `λ "x" ．
   (` "x" ·
    (Let
      "id" := (`λ "x" ． ` "x")
        In
          ((` "id" · (`λ "x" ． ` "x")) · (` "id" · tt))))

_ : show (mgt M) ≡ "∀ {b} ((⊤ → b) → b)"
_ = refl 




