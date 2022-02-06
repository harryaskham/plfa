module Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import Isomorphism using (_≃_; _≲_; _⇔_; extensionality)
open Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record
  { to      = λ { z → ⟨ _⇔_.to z , _⇔_.from z ⟩ }
  ; from    = λ { ⟨ x , y ⟩ → record { to = x; from = y } }
  ; from∘to = λ { z → refl }
  ; to∘from = λ { ⟨ x , y ⟩ → refl }
  }

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

infixr 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to = λ { (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x }
  ; from = λ { (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x }
  ; from∘to = λ { (inj₁ x) → refl ; (inj₂ x) → refl }
  ; to∘from = λ { (inj₁ x) → refl ; (inj₂ x) → refl }
  }

⊎-assoc : ∀ {A B C : Set} → A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc = record
  { to = λ { (inj₁ a) → inj₁ (inj₁ a) ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b) ; (inj₂ (inj₂ c)) → inj₂ c }
  ; from = λ { (inj₁ (inj₁ a)) → inj₁ a ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b) ; (inj₂ c) → inj₂ (inj₂ c) }
  ; from∘to = λ { (inj₁ a) → refl ; (inj₂ (inj₁ b)) → refl ; (inj₂ (inj₂ c)) → refl }
  ; to∘from = λ { (inj₁ (inj₁ a)) → refl ; (inj₁ (inj₂ b)) → refl ; (inj₂ c) → refl }
  }
