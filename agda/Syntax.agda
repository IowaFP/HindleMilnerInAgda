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
TVar = String

Vars = List Var
TVars = List TVar

--------------------------------------------------------------------------------
-- Syntax
--

infixr 5 _·_
infixr 4 `λ_．_
data Expr : Set where
  tt    : Expr
  `_    : (x : Var) → Expr
  `λ_．_    : (x : Var) → (e : Expr) → Expr
  _·_  : (e₁ : Expr) → (e₂ : Expr) → Expr
  Let_:=_In_ : (x : Var) → (e₁ : Expr) → (e₂ : Expr) → Expr

infixr 5 _`→_
data Type : Set where
  ⊤    : Type
  `_    : (α : TVar) → Type
  _`→_ : (τ₁ : Type) → (τ₂ : Type) → Type

data Scheme : Set where
  §  : (τ : Type) → Scheme
  `∀ : (T : TVars) → (τ : Type) → Scheme

--------------------------------------------------------------------------------
-- Renamings map variables to variables.

Renaming : Set 
Renaming = AssocList Var

--------------------------------------------------------------------------------
-- Substitutions map type vars to types.

Subst : Set
Subst = AssocList Type

--------------------------------------------------------------------------------
-- Typing Assignments map *type vars* to *type schemes*.

TypeAss : Set
TypeAss = AssocList Scheme


--------------------------------------------------------------------------------
-- Renamings can be promoted trivially to substitutions

sub : Renaming → Subst 
sub = map `_ 

--------------------------------------------------------------------------------
-- Substitutions can be promoted trivially to Type Assignments

ass : Subst → TypeAss
ass = map §

--------------------------------------------------------------------------------
-- Some helpers

-- Set difference.
_╲_ : Vars → Vars → Vars
xs ╲ ys = filter (_∉? ys) xs

-- Removing duplicates 
dedup : Vars → Vars
dedup = deduplicate _≟_

--------------------------------------------------------------------------------
-- Free type variables in types, schemes, and typing assignments.

ftv : Scheme → TVars
ftv't : Type → TVars
ftv'Γ : TypeAss → TVars 

ftv (§ τ) = ftv't τ
ftv (`∀ T τ) = ftv't τ ╲ (dedup T)

ftv't ⊤ = []
ftv't (` α) = α ∷ []
ftv't (τ₁ `→ τ₂) = dedup (ftv't τ₁ ++ ftv't τ₂)

ftv'Γ ∅ = []
ftv'Γ (α ↦ σ , Γ) = dedup (ftv σ ++ ftv'Γ Γ)

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

-- Produce the Renaming [βᵢ/αᵢ] fresh βᵢ from vars αᵢ.
freshen : Vars → Renaming
freshen as = go as as
  where
    -- "all" accumulates each fresh var we add,
    -- so that we do not produce duplicates.
    go : Vars → Vars → Renaming
    go [] all = ∅
    go (x ∷ xs) all = let β = fresh all in (x ↦ β , (go xs (β ∷ all)))

-- Quick test 
_ : freshen ("x" ∷ "y" ∷ "z" ∷ []) ≡ "x" ↦ "a" , "y" ↦ "b" , "z" ↦ "c" , ∅ 
_ = refl 

-- Generate a new name
new : TypeAss → Var
new Γ = (fresh (ftv'Γ Γ))

--------------------------------------------------------------------------------
-- Substitution.

infixl 2 _[_]β 
infixl 2 _[_]t
_[_]β : Scheme → Subst → Scheme
_[_]t : Type → Subst → Type

-- Capture avoiding substitution over type schemes
(§ τ) [ σ ]β    = § (τ [ σ ]t)
(`∀ T τ) [ σ ]β = let ρ = freshen T in `∀ (cod ρ) ((τ [ sub ρ ]t)  [ σ ]t)

⊤ [ _ ]t = ⊤
(` x) [ σ ]t = σ ∋[ x ] (` x)
(τ₁ `→ τ₂) [ σ ]t = (τ₁ [ σ ]t) `→ (τ₂ [ σ ]t)

-- test for capture avoiding substitution
_ :   ((`∀ ("α" ∷ "β"  ∷ []) (` "α" `→ ` "β" `→ ` "c")) [ ("α" ↦ ⊤ , "β" ↦ ⊤ , "c" ↦ ⊤ , ∅) ]β) 
    ≡ (`∀ ("a" ∷ "b"  ∷ []) (` "a" `→ ` "b" `→ ⊤))
_ = refl 

-- --------------------------------------------------------------------------------
-- Substitution over typing environments.

_[_]Γ : TypeAss → Subst → TypeAss
Γ [ σ ]Γ = map (_[ σ ]β) Γ

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
