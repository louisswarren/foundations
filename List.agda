open import Agda.Builtin.List public
open import Agda.Builtin.Sigma


open import Bottom

infix 4 _∈_ --_∉_
infixr 5 [_]∷_ _∷_

data _∈_ {a} {A : Set a} : A → List A → Set a where
  [_]∷_ : (x : A) → (xs : List A) → x ∈ (x ∷ xs)
  _∷_   : {x : A} {xs : List A} → (y : A) → x ∈ xs → x ∈ (y ∷ xs)

∀[_]_ : ∀{a} {A : Set a} → List A → Pred A → Set a
∀[ xs ] P = ∀ x → x ∈ xs → P x

record ∃[_]_ {a} {A : Set a} (xs : List A) (P : Pred A) : Set a where
  constructor [_,_,_]
  field
    x    : A
    x∈xs : x ∈ xs
    Px   : P x
open ∃[_]_ renaming (x to value ; x∈xs to contains ; Px to satisfies) public

data All {a} {A : Set a} (P : Pred A) : List A → Set a where
  []  : All P []
  _∷_ : ∀{x xs} → P x → All P xs → All P (x ∷ xs)

data Any {a} {A : Set a} (P : Pred A) : List A → Set a where
  [_]∷_ : ∀{x} → P x → ∀ xs → Any P (x ∷ xs)
  _∷_   : ∀{xs} → (x : A) → Any P xs → Any P (x ∷ xs)

∀listAll : ∀{a} {A : Set a} {P : Pred A} {xs : List A} → ∀[ xs ] P → All P xs
∀listAll {xs = []}     ∀[]P   = []
∀listAll {xs = y ∷ ys} ∀[ys]P = ∀[ys]P y ([ y ]∷ ys)
                                ∷ ∀listAll (λ x z → ∀[ys]P x (y ∷ z))

All∀list : ∀{a} {A : Set a} {P : Pred A} {xs : List A} → All P xs → ∀[ xs ] P
All∀list []         y ()
All∀list (Px ∷ Pxs) y ([ .y ]∷ xs) = Px
All∀list (Px ∷ Pxs) y (z ∷ y∈xs)   = All∀list Pxs y y∈xs

∃listAny : ∀{a} {A : Set a} {P : Pred A} {xs : List A} → ∃[ xs ] P → Any P xs
∃listAny [ x , [ .x ]∷ xs , Px ] = [ Px ]∷ xs
∃listAny [ x , y ∷ x∈xs   , Px ] = y ∷ ∃listAny [ x , x∈xs , Px ]

Any∃list : ∀{a} {A : Set a} {P : Pred A} {xs : List A} → Any P xs → ∃[ xs ] P
Any∃list ([ x ]∷ xs) = [ _ , [ _ ]∷ xs , x ]
Any∃list (x ∷ AnyPxs) = [ value ∃[xs]P , x ∷ contains ∃[xs]P , satisfies ∃[xs]P ]
  where
    ∃[xs]P : ∃[ _ ] _
    ∃[xs]P = Any∃list AnyPxs

module _ where
  open import Agda.Builtin.Nat renaming (Nat to ℕ)
  open import Agda.Builtin.Equality

  data _≤_ : ℕ → ℕ → Set where
    0≤n   : ∀{n} → zero ≤ n
    sn≤sm : ∀{n m} → n ≤ m → suc n ≤ suc m

  _ : 3 ∈ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
  _ = 1 ∷ 2 ∷ [ 3 ]∷ 4 ∷ 5 ∷ []

  l10 : ∀[ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [] ] _≤ 10
  l10 .1 ([ .1 ]∷ .(2 ∷ 3 ∷ 4 ∷ 5 ∷ [])) = sn≤sm 0≤n
  l10 .2 (.1 ∷ [ .2 ]∷ .(3 ∷ 4 ∷ 5 ∷ [])) = sn≤sm (sn≤sm 0≤n)
  l10 .3 (.1 ∷ .2 ∷ [ .3 ]∷ .(4 ∷ 5 ∷ [])) = sn≤sm (sn≤sm (sn≤sm 0≤n))
  l10 .4 (.1 ∷ .2 ∷ .3 ∷ [ .4 ]∷ .(5 ∷ [])) = sn≤sm (sn≤sm (sn≤sm (sn≤sm 0≤n)))
  l10 .5 (.1 ∷ .2 ∷ .3 ∷ .4 ∷ [ .5 ]∷ .[]) = sn≤sm (sn≤sm (sn≤sm (sn≤sm (sn≤sm 0≤n))))
  l10 x (.1 ∷ .2 ∷ .3 ∷ .4 ∷ .5 ∷ ())

  l2 : ∃[ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [] ] _≤ 2
  l2 = [ 1 , [ 1 ]∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [] , sn≤sm 0≤n ]
