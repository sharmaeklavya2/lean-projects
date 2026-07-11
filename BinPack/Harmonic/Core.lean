module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

def rawcat (x : α) : ℕ :=
  (⌊1/x⌋.toNat)

def cat (M : ℕ) (x : α) : ℕ :=
  -- M ≥ 1 and x ∈ (0, 1]
  -- category of an item of size x
  min M (⌊1/x⌋.toNat)

def wh (M : ℕ) (x : α) : α :=
  -- M ≥ 1 and x ∈ (0, 1]
  -- harmonic weight of an item of size x
  if x ≤ 1/M then M * x / (M-1) else 1 / (⌊1/x⌋.toNat)
