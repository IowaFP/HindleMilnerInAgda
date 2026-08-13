module Prelude where 

open import Data.Bool using (Bool ; true ; false ; _∨_ ) public 
open import Data.String using (String) public 
open import Data.Maybe using (Maybe ; nothing ; just) public
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _≡ᵇ_) public 
open import Data.List using (List ; filter ; deduplicate ; [] ; _∷_ ; _++_) public 
open import Data.List.Extrema.Nat using (max) public 
open import Data.List.Membership.DecPropositional _≟_ using (_∉?_ ) public 
-- open import Data.List.Membership.Propositional.Properties public 

open import Data.Product
  using (_×_ ; _,_)
  renaming (proj₁ to fst ; proj₂ to snd)
  public 
  
open import Data.Sum
  using (_⊎_)
  renaming (inj₁ to left ; inj₂ to right)
  public 

open import Relation.Binary.PropositionalEquality public 
open import Function using (_∘_) public

open import AssocList public 


-- --------------------------------------------------------------------------------
-- -- Data 

-- open import Data.Bool using (Bool ; true ; false ; _∨_)public 
-- open import Data.String using (String) public  
-- open import Data.Nat public 
-- open import Data.List
--   hiding (or ; lookup ; _─_ ; any ; head ; tail) public 
-- open import Data.List.Extrema.Nat public 
-- open import Data.List.Relation.Unary.Any public 
--   hiding (map) public 
-- import Data.List.Membership.DecPropositional as Membership
-- open import Data.List.Membership.Propositional.Properties public 
-- open Membership _≟_ hiding (_∷=_ ; _─_ ; find) public 

-- --------------------------------------------------------------------------------
-- -- Relation 

-- open import Relation.Binary.PropositionalEquality
--   hiding (subst)

-- open import Relation.Nullary
--   using (¬_; Dec; yes; no) public 
-- open import Relation.Nullary.Decidable
--   hiding (map) public 
-- open import Relation.Nullary.Negation
--   renaming (contraposition to contra) public 

-- open import Data.Product
--   renaming (proj₁ to fst ; proj₂ to snd)
--   hiding (map) public 
  
-- open import Data.Sum
--   renaming (_⊎_ to _or_ ; inj₁ to left ; inj₂ to right)
--   hiding (map) public 

-- --------------------------------------------------------------------------------
-- -- Function 

-- open import Function public 
