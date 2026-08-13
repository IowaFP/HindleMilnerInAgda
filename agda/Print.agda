module Print where
open import Prelude hiding (_++_)
open import Data.String using (intersperse ; _++_)
open import Data.List using (map)
open import Syntax

--------------------------------------------------------------------------------
-- Pretty Printing of terms.

-- This should already be defined in Data.List?
lookup : ∀ {A : Set} → List A → ℕ → Maybe A
lookup [] _ = nothing
lookup (x ∷ xs) zero = just x
lookup (x ∷ xs) (suc n) = lookup xs n

name : Var → String 
name = id 
-- name : Var → String
-- name α with lookup alphabet α
-- ... | just n = n
-- ... | nothing = "pfft"

print : Scheme → String
print't : Type → String
print (§ τ) = print't τ
print (`∀ T τ) = "∀ {" ++ (intersperse ", " (map name T)) ++ "} " ++ print't τ

_ : print (`∀ ("x" ∷ "y" ∷ []) ⊤) ≡ "∀ {x, y} ⊤"
_ = refl

print't ⊤ = "⊤"
print't (` α) = name α
print't (τ `→ τ') = "(" ++ print't τ ++ " → " ++ print't τ' ++ ")"
