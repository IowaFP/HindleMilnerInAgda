module Syntax where

open import Prelude
open import Data.List.Membership.DecPropositional _≟_ using (_∉?_ ) public 
open AList String _≟_


--------------------------------------------------------------------------------
-- Syntax for implementation of Algorithm 𝒲 and Algorithm ℳ, following Lee and
-- Yi (1998).
-- Author: Alex Hubers <ahubers@uiowa.edu>
--
--------------------------------------------------------------------------------
-- Variable Representation & substitution.
-- We used a named representation.

Var = String
Vars = List Var

--------------------------------------------------------------------------------
-- Syntax
--
-- TODO:
--   - Refactor from ℕ vars to String vars
--   - Add recursive functions / LFP operator.
--   - Add Inductive-recursive definition 
--       _∉ₑ_ : Var → Expr → Set
--       _∉ₑ_ : (x : Var) (e : Expr) → Dec (x ∉ₑ? Expr)
--   - So that we can constrain `λ with {free : True (x ∉ₑ? Expr)}

data Expr : Set where
  tt    : Expr
  `    : (x : Var) → Expr
  `λ    : (x : Var) → (e : Expr) → Expr
  _·_  : (e₁ : Expr) → (e₂ : Expr) → Expr
  Let_:=_In_ : (x : Var) → (e₁ : Expr) → (e₂ : Expr) → Expr

data Type : Set where
  ⊤    : Type
  `    : (α : Var) → Type
  _`→_ : (τ₁ : Type) → (τ₂ : Type) → Type

data Scheme : Set where
  §  : (τ : Type) → Scheme
  `∀ : (T : Vars) → (τ : Type) → Scheme

--------------------------------------------------------------------------------
-- Typing Assignments map *type vars* to *type schemes*.

TypeAss : Set
TypeAss = AssocList Scheme

--------------------------------------------------------------------------------
-- Substitutions map type vars to types.

Subst : Set
Subst = AssocList Type

--------------------------------------------------------------------------------
-- Lift a substitution up to a typing assignment.

lift : Subst → TypeAss
lift = map §

--------------------------------------------------------------------------------
-- Free type variables in types, schemes, and environments.

-- Set difference.
_╲_ : List Var → List Var → List Var
xs ╲ ys = filter (_∉? ys) xs

dedup = deduplicate _≟_

ftv : Scheme → Vars
ftv't : Type → Vars

ftv (§ τ) = ftv't τ
ftv (`∀ T τ) = ftv't τ ╲ (dedup T)

ftv't ⊤ = []
ftv't (` α) = α ∷ []
ftv't (τ₁ `→ τ₂) = dedup (ftv't τ₁ ++ ftv't τ₂)

ftv'Γ : TypeAss → Vars
ftv'Γ ∅ = []
ftv'Γ (α ↦ σ , Γ) = dedup (ftv σ ++ (ftv'Γ Γ))

--------------------------------------------------------------------------------
-- Occurrence.
-- Does α occur free in type τ?

occurs : (α : Var) → (τ : Type) → Bool
occurs α ⊤ = false
occurs α (` β) = α == β
occurs α (τ₁ `→ τ₂) = (occurs α τ₁) ∨ (occurs α τ₂)


-- occurs : (α : Var) → (τ : Type) → Dec (α ∈ ftv't τ)
-- occurs α ⊤ = no (λ ())
-- occurs α (` β) with α Dat.Nat._≟_ β
-- ... | yes α≡β rewrite α≡β = yes (here refl)
-- ... | no a≠β = no (λ { (here Α≡β) → a≠β Α≡β})
-- occurs α (τ₁ `→ τ₂) with occurs α τ₁ | occurs α τ₂
-- ... | yes p | _ = yes (∈-++⁺ˡ p)
-- ... | _ | yes p = yes ( (∈-++⁺ʳ  (ftv't τ₁) p))
-- ... | no p₁ | no p₂ = no (contra (∈-++⁻ (ftv't τ₁)) λ { (left x) → p₁ x ; (right x) → p₂ x })

--------------------------------------------------------------------------------
-- Freshening, i.e.,
--   freshen Γ (∀αᵢ.τ) := [βᵢ/αᵢ]τ
-- with βᵢ fresh in αᵢ ∪ dom Γ for i ≥ 0.

-- Produce fresh β from vars αᵢ.
-- Unsafe if you run out of variables in the alphabet.
fresh : Vars → Var
fresh vs = unsafeHead (alphabet ╲ vs)

-- Produce the substitution [βᵢ/αᵢ] fresh βᵢ from vars αᵢ.
freshen : Vars → Subst
freshen as = go as as
  where
    -- "all" accumulates each fresh var we add,
    -- so that we do not produce duplicates.
    go : Vars → Vars → Subst
    go [] all = ∅
    go (x ∷ xs) all = let β = fresh all in (x ↦ (` β) , (go xs (β ∷ all)))

-- Quick test 
_ : freshen ("x" ∷ "y" ∷ "z" ∷ []) ≡ "x" ↦ ` "a" , "y" ↦ ` "b" , "z" ↦ ` "c" , ∅ 
_ = refl 

new : TypeAss → Type
new Γ = ` (fresh (dom Γ))

--------------------------------------------------------------------------------
-- Substitution.

infixl 2 _[_]
infixl 2 _[_]t
_[_] : Scheme → Subst → Scheme
_[_]t : Type → Subst → Type

(§ τ) [ σ ]    = § (τ [ σ ]t)
(`∀ T τ) [ σ ] = `∀ T (τ [ σ ]t)

⊤ [ _ ]t = ⊤
(` x) [ σ ]t = σ ∋[ x ] (` x)
(τ `→ τ') [ σ ]t = (τ [ σ ]t) `→ (τ' [ σ ]t)

-- --------------------------------------------------------------------------------
-- Substitution over typing environments.

_[_]Γ : TypeAss → Subst → TypeAss
Γ [ σ ]Γ = map (_[ σ ]) Γ

--------------------------------------------------------------------------------

-- Substitution within a substitution, e.g.,
--    β ↦ ζ ∘ (α ↦ (β → β))
-- should yield the substitution
--    (α ↦ (ζ → ζ) , β ↦ ζ)
-- AH> Why does σ₁ ∘ₛ ∅ = σ₁? Should it not yield ∅? 

infixr 1 _∘ₛ_
_∘ₛ_ : Subst → Subst → Subst
σ₁ ∘ₛ ∅ = ∅
σ₁ ∘ₛ (α ↦ τ  , σ₂) = α ↦ τ [ σ₁ ]t , σ₁ ∘ₛ σ₂ 

-- --------------------------------------------------------------------------------
-- Generalization, a là Jones (1995) and Damas and Milner (1982).

gen : TypeAss → Type → Scheme
gen Γ τ = `∀ ((ftv't τ) ╲ ftv'Γ Γ) τ
