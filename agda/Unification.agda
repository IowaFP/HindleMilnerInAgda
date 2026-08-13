module Unification where

open import Prelude 
open import Syntax
open AList ℕ _≟_

--------------------------------------------------------------------------------
-- Unification (𝒰).
--

{-# TERMINATING #-}
𝒰 : Type → Type → Maybe Subst
𝒰 (τ₁ `→ τ₂) (υ₁ `→ υ₂) with 𝒰 τ₁ υ₁
... | nothing = nothing
... | just S₁ with 𝒰 (sub't S₁ τ₂) (sub't S₁ υ₂)
...   | just S₂ = just (sub'S S₂ S₁)
...   | nothing = nothing
𝒰 ⊤ ⊤ = just ∅
𝒰 (` α) τ@(` β) with α ≡ᵇ β
... | true = just ∅
... | false = just [ α ↦ τ ]
-- Don't think this is right ?
-- Also, need to check if α ∈ ftv x.
𝒰 (` α) τ with occurs α τ
... | true = nothing
... | false = just [ α ↦ τ ]
𝒰 τ (` α) with occurs α τ
... | true = nothing
... | false = just [ α ↦ τ ]
𝒰 _ _ = nothing
