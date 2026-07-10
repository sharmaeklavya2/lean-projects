module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

noncomputable def rawcat (x : ℝ) : ℕ :=
  (⌊1/x⌋.toNat)

noncomputable def cat (M : ℕ) (x : ℝ) : ℕ :=
  -- M ≥ 1 and x ∈ (0, 1]
  -- category of an item of size x
  min M (⌊1/x⌋.toNat)

noncomputable def wh (M : ℕ) (x : ℝ) : ℝ :=
  -- M ≥ 1 and x ∈ (0, 1]
  -- harmonic weight of an item of size x
  if x ≤ 1/M then M * x / (M-1) else 1 / (⌊1/x⌋.toNat)
