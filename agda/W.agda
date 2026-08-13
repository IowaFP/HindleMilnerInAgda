module W where

open import Prelude 
open import Syntax
open import Unification
open AList ℕ _≟_

--------------------------------------------------------------------------------
-- Implementation of Algorithm 𝒲, following Lee and Yi (1998) and Jones (1995).

idS : Subst
idS = ∅

-- TODO.
-- Need to switch this to Maybe (Subst × Type)
𝒲 : TypeAss → Expr → Subst × Type
𝒲 Γ tt =  idS , ⊤
𝒲 Γ (` x) with (Γ ∋[ x ] (§ (` x)))
... | § τ    = idS , τ
... | σ@(`∀ T τ) = idS , sub't (freshen (T ++ dom Γ)) τ
𝒲 Γ (`λ x e) = let
                 β = new Γ
                 (S₁ , τ₁) = 𝒲 (x ↦ § β , Γ) e
               in S₁ , (sub't S₁ β) `→ τ₁ 
𝒲 Γ (e₁ · e₂) with new Γ | 𝒲 Γ e₁
... | β | (S₁ , τ₁) with 𝒲 (sub'Γ S₁ Γ) e₂
...   | (S₂ , τ₂) with 𝒰 (sub't S₂ τ₁) (τ₂ `→ β)
...     | just S₃ = S₃ ∘' (S₂ ∘' S₁) , sub't S₃ β
...     | nothing = ∅ , ⊤
𝒲 Γ (Let x := e₁ In e₂) =
  let
    (S₁ , τ₁) = 𝒲 Γ e₁
    (S₂ , τ₂) = 𝒲 (x ↦ (gen Γ τ₁ ) , sub'Γ S₁ Γ) e₂
  in (S₂ ∘' S₁) , τ₂

--------------------------------------------------------------------------------
-- Inference of most general type scheme.

mgt : Expr → Scheme
mgt e = let S , τ = 𝒲 ∅ e in gen ∅ τ

