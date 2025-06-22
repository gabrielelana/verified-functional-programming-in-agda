module Chapter-02 where

  open import Relation.Binary.PropositionalEquality
  open import Chapter-01

  ~~tt : ~ ~ tt ≡ tt
  ~~tt = refl

  ~~ff : ~ ~ ff ≡ ff
  ~~ff = refl

  -- We are giving a definition for a symbol `~~tt`
  -- The definition has a type, in this case `~ ~ tt ≡ tt`

  -- Agda adopts the simple but powerful idea of treating any program
  -- expressions that appear inside types as equal if their defining equations
  -- make them equal.

  -- Therefore `~ ~ tt` is evaluated to `tt`

  -- The two formulas are said to be definitionally equal.

  -- `refl` is the sole constructor of the equality type.

  -- Can we prove it in a more general way?

  ~~elim : ∀ (b : 𝔹) → ~ ~ b ≡ b
  ~~elim tt = refl
  ~~elim ff = refl

  -- This theorem that we are trying to prove can be shown by case analysis on
  -- the variable `b`.

  -- So the universal type `∀ (b : B) → ~ ~ b ≡ b` can be seen as a function
  -- type: given input `b`, the `~~elim` function will return an output of type
  -- `~ ~ b ≡ b`. This is also part of the Curry-Howard isomorphism.

  ~~elim₁ : ∀ (b : 𝔹) → ~ ~ b ≡ b
  ~~elim₁ tt = ~~tt -- refl{lzero}{𝔹}{tt}
  ~~elim₁ ff = ~~ff -- refl{lzero}{𝔹}{ff}

  -- Let's prove another one
  &&-idem : ∀ (b : 𝔹) → b && b ≡ b
  &&-idem tt = refl
  &&-idem ff = refl

  -- Same one but letting Agda do more inference on `b` type
  &&-idem₁ : ∀ b → b && b ≡ b
  &&-idem₁ tt = refl
  &&-idem₁ ff = refl

  -- We can also make the `b` parameter implicit, this will be
  -- helpful when you need to use the theorem
  &&-idem₂ : ∀{b} → b && b ≡ b
  &&-idem₂{tt} = refl
  &&-idem₂{ff} = refl

  _ : tt && tt ≡ tt
  _ = &&-idem₁ tt

  _ : tt && tt ≡ tt
  _ = &&-idem₂ -- NOTE: no explicit parameter needed

  -- Proof with an assumption

  -- For every boolean `b1` and `b2`
  -- if the disjunction between them is false
  -- then `b1` must be false

  -- Under the Curry-Howard isomorphism, to express an assumption, we write a
  -- function that takes in a proof of that assumption and then produces the
  -- proof of the desired result.

  ||≡ff₁ : ∀ {b1 b2} → b1 || b2 ≡ ff → b1 ≡ ff
  ||≡ff₁ {ff} p = refl -- when `b1` is `ff` then the result is literally `ff ≡ ff`, then definitionally equal
  ||≡ff₁ {tt} ()       -- we can omit the right side of the equation because the left contains the absurd `()`

  -- Congruence proof
  ||-cong : ∀ {b1 b2 b2'} → b2 ≡ b2' → b1 || b2 ≡ b1 || b2'
  ||-cong p rewrite p = refl

  -- Suppose you have a proof `p` of some equation `X ≡ Y`. Then rewrite p
  -- instructs the Agda type checker to look in the goal for any occurrences of
  -- X, and transform those into Y.

  if-same : ∀ {a} {A : Set a} →
            ∀ (b : 𝔹) (x : A) →
            (if b then x else x) ≡ x
  if-same tt x = refl
  if-same ff x = refl

  -- Exercise 2.1
  imp-antisymm : ∀ {b1 b2 : 𝔹} → (b1 imp b2 ≡ tt) → (b2 imp b1 ≡ tt) → (b1 ≡ b2)
  imp-antisymm {tt} {tt} _ _ = refl
  imp-antisymm {tt} {ff} () _
  imp-antisymm {ff} {tt} _ ()
  imp-antisymm {ff} {ff} _ _ = refl

  ff-xor : ∀ (b : 𝔹) → ff ^ b ≡ b
  ff-xor tt = refl
  ff-xor ff = refl

  tt-xor : ∀ (b : 𝔹) → tt ^ b ≡ ~ b
  tt-xor tt = refl
  tt-xor ff = refl

  ~-xor-distrb : ∀ (a b : 𝔹) → ~ (a ^ b) ≡ ~ a ^ b
  ~-xor-distrb tt tt = refl
  ~-xor-distrb tt ff = refl
  ~-xor-distrb ff tt = refl
  ~-xor-distrb ff ff = refl

  xor-distrib-&& : ∀ (x y : 𝔹) → x ^ (y && x) ≡ ~ y && x
  xor-distrib-&& tt tt = refl
  xor-distrib-&& tt ff = refl
  xor-distrib-&& ff tt = refl
  xor-distrib-&& ff ff = refl

  -- Exercise 2.2
  -- De morgan first law
  demorgan-first-law : ∀ (x y : 𝔹) → ~ (x && y) ≡ ~ x || ~ y
  demorgan-first-law tt tt = refl
  demorgan-first-law tt ff = refl
  demorgan-first-law ff tt = refl
  demorgan-first-law ff ff = refl

  -- De morgan second law
  demorgan-second-law : ∀ (x y : 𝔹) → ~ (x || y) ≡ ~ x && ~ y
  demorgan-second-law tt tt = refl
  demorgan-second-law tt ff = refl
  demorgan-second-law ff tt = refl
  demorgan-second-law ff ff = refl

  -- Material conditional
  material-conditional : ∀ (x y : 𝔹) → x imp y ≡ ~ x || y
  material-conditional tt tt = refl
  material-conditional tt ff = refl
  material-conditional ff _ = refl

  -- Exercise 2.3
  -- Which of the following formulas could be proved by refl?

  -- Yes
  formula-001 : tt ≡ tt
  formula-001 = refl

  -- Yes
  formula-002 : ff ≡ ff
  formula-002 = refl

  -- No: is not definitionally equal, different constructors
  -- formula-003 : ff ≡ tt

  -- Yes
  formula-004 : ff && ff ≡ ~ tt
  formula-004 = refl

  -- Yes
  formula-005 : ∀ {x : 𝔹} → tt && x ≡ x
  formula-005 = refl

  formula-006 : ∀ {x : 𝔹} → x && tt ≡ x
  formula-006 {tt} = refl
  formula-006 {ff} = refl
