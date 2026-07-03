-- tpil ======================

-- definition of ¬p
example {p : Prop}: (¬p) = (p → False) := rfl

-- what implication means
example {A X : Prop} (h1 : A) (h2: A → X) : X := h2 h1

-- ∧-intro without tactics
example {A B : Prop} (hA : A) (hB : B) : A ∧ B :=
  And.intro hA hB

-- ∧-left-elim without tactics
example {A B : Prop} (h : A ∧ B) : A :=
  h.left

-- ∨-elim without tactics
example {A B X : Prop} (h : A ∨ B) (h1: A → X) (h2: B → X): X :=
  h.elim h1 h2

-- ∨-left-intro without tactics
example {A B : Prop} (hA : A) : A ∨ B := Or.inl hA

-- tactics ============

-- defeq, no tactic
example : 2 + 3 = 5 := rfl

-- rw
example {a b : Nat} (h: a = b) : a * a + 2 = b * b + 2 := by
  rw[h]

-- decide
example : 2 + 3 * 3 > 10 := by decide

-- omega
example {a b : Int}
  (h1: 2 * a + b ≥ 5)
  (h2: a + 2 * b ≥ 3)
  : 7 * a + 5 * b ≥ 18 := by omega

-- game/robo/logo ============

-- rfl
example (x: Nat) : x = x := by rfl

-- True and False
example : True := by trivial
example : True := by decide
example : True := by constructor
example : True := True.intro
example : ¬False := by trivial
example : ¬False := by decide

-- assumption
example {A: Prop} (h: A) : A := by assumption

-- contradiction
example (A : Prop) (h : False) : A := by contradiction
example (A : Prop) (n: Nat) (h : n ≠ n) : A := by contradiction

-- ∧-intro using tactics (constructor)
example {A B : Prop} (hA : A) (hB : B) : A ∧ B := by
  constructor
  · assumption
  · assumption

-- ∨-intro using tactics (left)
example {A B : Prop} (hA : A) : A ∨ B := by
  left
  assumption

-- ∧-elim using tactics (obtain)
example {A B : Prop} (h : A ∧ B) : A := by
  obtain ⟨hA, hB⟩ := h
  assumption

-- ∨-elim using tactics (obtain)
example {A B X : Prop} (h : A ∨ B) (h1: A → X) (h2: B → X): X := by
  obtain hA | hB := h
  · exact h1 hA
  · exact h2 hB
