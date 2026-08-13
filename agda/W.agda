module W where

open import Prelude 
open import Syntax
open import Unification
open AList String _≟_

--------------------------------------------------------------------------------
-- Implementation of Algorithm 𝒲, following Lee and Yi (1998) and Jones (1995).

-- TODO.
-- Need to switch this to Maybe (Subst × Type)
𝒲 : TypeAss → Expr → Subst × Type
𝒲 Γ tt =  ∅ , ⊤
𝒲 Γ (` x) with (Γ ∋[ x ] (§ (` x)))
... | § τ    = ∅ , τ
... | σ@(`∀ T τ) = ∅ , (τ [ (freshen (T ++ dom Γ)) ]t)
𝒲 Γ (`λ x e) = let
                 β = new Γ
                 (σ₁ , τ₁) = 𝒲 (x ↦ § β , Γ) e
               in σ₁ , (β [ σ₁ ]t) `→ τ₁ 
𝒲 Γ (e₁ · e₂) with new Γ | 𝒲 Γ e₁
... | β | (σ₁ , τ₁) with 𝒲 (Γ [ σ₁ ]Γ) e₂
...   | (σ₂ , τ₂) with 𝒰 (τ₁ [ σ₂ ]t) (τ₂ `→ β)
...     | just σ₃ = σ₃ ∘' (σ₂ ∘ₛ σ₁) , (β [ σ₃ ]t) -- β [ σ₃ ]t
...     | nothing = ∅ , ⊤
𝒲 Γ (Let x := e₁ In e₂) =
  let
    (σ₁ , τ₁) = 𝒲 Γ e₁
    (σ₂ , τ₂) = 𝒲 (x ↦ (gen Γ τ₁ ) , (Γ [ σ₁ ]Γ)) e₂
  in (σ₂ ∘' σ₁) , τ₂

--------------------------------------------------------------------------------
-- Inference of most general type scheme.

mgt : Expr → Scheme
mgt e = let σ , τ = 𝒲 ∅ e in gen ∅ τ

