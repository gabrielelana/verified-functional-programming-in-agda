module Chapter-01 where

  data 𝔹 : Set where
    tt : 𝔹
    ff : 𝔹

  infix  7 ~_
  infixr 6 _^_
  infixr 6 _&&_
  infixr 5 _||_

  ~_ : 𝔹 → 𝔹
  ~ tt = ff
  ~ ff = tt

  _&&_ : 𝔹 → 𝔹 → 𝔹
  tt && b = b
  ff && b  = ff

  _||_ : 𝔹 → 𝔹 → 𝔹
  ff || b = b
  tt || b  = tt

  -- Exercise 1.3
  _^_ : 𝔹 → 𝔹 → 𝔹
  tt ^ ff = tt
  ff ^ tt  = tt
  _ ^ _ = ff

  -- Exercise 1.3
  -- p → q ≡ ~ p ∨ q
  _imp_ : 𝔹 → 𝔹 → 𝔹
  -- p imp q = (~ p) || q
  tt imp b = b
  ff imp b = ff


  if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
  if tt then tb else fb = tb
  if ff then tb else fb = fb

  open import Relation.Binary.PropositionalEquality

  -- Exercise 1.1: What's the value of the following expressions
  _ : tt && (ff ^ ~ ff) ≡ tt
  _ = refl

  _ : ~ tt && (ff imp ff) ≡ ff
  _ = refl

  _ : if (tt ^ tt) then ff else ff ≡ ff
  _ = refl

  -- Exercise 1.2: What's the type of the following expressions
  -- tt : 𝔹
  -- if tt then ff else tt : 𝔹
  -- _&&_ : 𝔹 → 𝔹 → 𝔹
  -- 𝔹 : Set

  -- Exercise 1.4: Define a data type for the day of the week
  data Day : Set where
    monday : Day
    tuesday : Day
    wednesday : Day
    thursday : Day
    friday : Day
    saturday : Day
    sunday : Day

  -- Exercise 1.4: Define the following function
  nextday : Day -> Day
  nextday monday = tuesday
  nextday tuesday = wednesday
  nextday wednesday = thursday
  nextday thursday = friday
  nextday friday = saturday
  nextday saturday = sunday
  nextday sunday = monday

  -- Exercise 1.5: Define a data type for the suits of a standard deck of cards
  data Suit : Set where
    hearts : Suit
    spades : Suit
    diamonds : Suit
    clubs : Suit

  -- Exercise 1.6: Define the following function
  is-red : Suit -> 𝔹
  is-red hearts = tt
  is-red diamonds = tt
  is-red _ = ff
