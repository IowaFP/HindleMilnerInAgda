module Print where
open import Prelude hiding (_++_)
open import Data.String using (intersperse ; _++_)
open import Data.List using (map)
open import Syntax

--------------------------------------------------------------------------------
-- Pretty Printing of terms.

record Show {ℓ} (A : Set ℓ) : Set ℓ where 
  field 
    show : A → String 
open Show {{...}} public 


instance 
  ShowScheme : Show Scheme 
  ShowType   : Show Type 

  ShowScheme .show (§ τ) = show τ
  ShowScheme .show (`∀ T τ) = "∀ {" ++ (intersperse ", " T) ++ "} " ++ show τ

  ShowType .show ⊤ = "⊤"
  ShowType .show (` α) = α
  ShowType .show (τ₁ `→ τ₂) = "(" ++ show τ₁ ++ " → " ++ show τ₂ ++ ")"

-- print : Scheme → String
-- print't : Type → String
-- print (§ τ) = print't τ
-- print (`∀ T τ) = "∀ {" ++ (intersperse ", " (map name T)) ++ "} " ++ print't τ

-- _ : print (`∀ ("x" ∷ "y" ∷ []) ⊤) ≡ "∀ {x, y} ⊤"
-- _ = refl

-- print't ⊤ = "⊤"
-- print't (` α) = name α
-- print't (τ₁ `→ τ₂) = "(" ++ print't τ₁ ++ " → " ++ print't τ₂ ++ ")"
