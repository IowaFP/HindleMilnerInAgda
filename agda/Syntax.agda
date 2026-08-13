module Syntax where

open import Prelude
open AList ℕ _≟_

--------------------------------------------------------------------------------
-- Syntax for implementation of Algorithm 𝒲 and Algorithm ℳ, following Lee and
-- Yi (1998).
-- Author: Alex Hubers <ahubers@uiowa.edu>
--
--------------------------------------------------------------------------------
-- Variable Representation & substitution.
--
-- N.B.
--  - We use a named representation of variables -- even if those names come from
--    ℕ. So this is *not* DeBruijn. For example, the lambda term
--        λ 3. λ 4. 3 4
--    is α-equivalent to
--        λ x. λ y. x y.
--    This makes implementation easiest, but likely would need to be changed to
--    either DeBruijn or Locally Nameless (see Charguéraud (2012)) before
--    formalizing any metatheory. I personally would recommend locally nameless,
--    as we require freshness and decidable equality of variable representation
--    -- precisely what is necessary for LN.

Var = ℕ
Vars = List Var

--------------------------------------------------------------------------------
-- Syntax
--
-- N.B.
--   - We omit recursive functions for simplicity.

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
-- Typing Assignments.
--
-- N.B.
--   - Typing assignments *look* the same as typing environments, but actually
--     map *type vars* to *type schemes*. An environment maps term vars to type
--     schemes.

TypeAss : Set
TypeAss = AssocList Scheme

--------------------------------------------------------------------------------
-- Substitutions.

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
occurs α (` β) = α ≡ᵇ β
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
fresh : Vars → Var
fresh = suc ∘ (max 0)

-- Produce the substitution [βᵢ/αᵢ] fresh βᵢ from vars αᵢ.
freshen : Vars → Subst
freshen as = go as as
  where
    -- "all" accumulates each fresh var we add,
    -- so that we do not produce duplicates.
    go : Vars → Vars → Subst
    go [] all = ∅
    go (x ∷ xs) all = let β = fresh all in (x ↦ (` β) , (go xs (β ∷ all)))
new : TypeAss → Type
new Γ = ` (fresh (dom Γ))

--------------------------------------------------------------------------------
-- Substitution.

sub : Subst → Scheme → Scheme
sub't : Subst → Type → Type

sub S (§ τ)     = § (sub't S τ)
sub S (`∀ T τ) = `∀ T (sub't S τ)

sub't S ⊤ = ⊤
sub't S (` x) = S ∋[ x ] (` x)
sub't S (τ `→ τ') = sub't S τ `→ sub't S τ'

-- --------------------------------------------------------------------------------
-- Substitution over typing environments.

sub'Γ : Subst → TypeAss → TypeAss
sub'Γ S Γ = map (sub S) Γ

--------------------------------------------------------------------------------
-- Substitution within a substitution, e.g.,
--    β ↦ ζ ∘ (α ↦ (β → β))
-- should yield the substitution
--    (β ↦ ζ , α ↦ (ζ → ζ))
-- i.e., we eagerly apply the substitution on the left.

sub'S : Subst → Subst → Subst
sub'S S₁ ∅ = S₁
sub'S S₁ (α ↦ τ , S₂) = α ↦ sub't S₁ τ , sub'S S₁ S₂

-- --------------------------------------------------------------------------------
-- Generalization, a là Jones (1995) and Damas and Milner (1982).

gen : TypeAss → Type → Scheme
gen Γ τ = `∀ ((ftv't τ) ╲ ftv'Γ Γ) τ
