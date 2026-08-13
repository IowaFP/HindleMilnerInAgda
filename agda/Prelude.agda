module Prelude where 
--------------------------------------------------------------------------------
-- Levels 

open import Agda.Primitive public

--------------------------------------------------------------------------------
-- Data 

open import Data.Bool using (Bool ; true ; false ; _∨_ ) public 
open import Data.String using (String ; _≟_ ; _==_) public 
open import Data.Maybe using (Maybe ; nothing ; just) public
open import Data.Nat using (ℕ ; zero ; suc) public 
open import Data.List using (List ; head ; tail ; filter ; deduplicate ; [] ; _∷_ ; _++_) public 
open import Data.List.Extrema.Nat using (max) public 
-- open import Data.List.Membership.Propositional.Properties public 

open import Data.Product
  using (_×_ ; _,_)
  renaming (proj₁ to fst ; proj₂ to snd)
  public 
  
open import Data.Sum
  using (_⊎_)
  renaming (inj₁ to left ; inj₂ to right)
  public 
--------------------------------------------------------------------------------
-- Relation

open import Relation.Binary.PropositionalEquality public 

--------------------------------------------------------------------------------
-- Function

open import Function using (_∘_ ; id) public

--------------------------------------------------------------------------------
-- Ours 

open import AssocList public 

-- A list of chars for drawing fresh variable names. 
alphabet = 
    "a" ∷ "b" ∷ "c" ∷ "d" ∷ 
    "e" ∷ "f" ∷ "g" ∷ "h" ∷ 
    "i" ∷ "j" ∷ "k" ∷ "l" ∷ 
    "m" ∷ "n" ∷ "o" ∷ "p" ∷ 
    "q" ∷ "r" ∷ "s" ∷ "t" ∷
    "u" ∷ "v" ∷ "w" ∷ "x" ∷ 
    "y" ∷ "z" ∷ [] 

private variable
  ℓ : Level 
  A : Set ℓ 

-- This is not a safe development
postulate
  undefined : A 

unsafeHead : List A → A 
unsafeHead [] = undefined
unsafeHead (x ∷ xs) = x 