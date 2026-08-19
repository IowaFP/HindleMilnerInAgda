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