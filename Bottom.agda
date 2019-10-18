open import Agda.Primitive

data ⊥ : Set where

¬_ : ∀{a} → Set a → Set a
¬ A = A → ⊥

data Dec {a} (A : Set a) : Set a where
  yes : A   → Dec A
  no  : ¬ A → Dec A

Pred : ∀{a} → (A : Set a) → Set (lsuc lzero ⊔ a)
Pred A = A → Set
