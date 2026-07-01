-- game/robo/logo

example (x: Nat) : x = x := by rfl

example {A: Prop} (h: A) : A := by assumption

example : True := by trivial
example : True := by decide
example : True := by constructor
example : True := True.intro

example : ¬False := by trivial
example : ¬False := by decide

example (A : Prop) (h : False) : A := by contradiction
example (A : Prop) (n: Nat) (h : n ≠ n) : A := by contradiction

example {A B : Prop} (hA : A) (hB : B) : A ∧ B := by
  constructor
  assumption
  assumption

example {A B X : Prop} (h : A ∨ B) : X := by
  obtain hA | hB := h
  sorry
  sorry
