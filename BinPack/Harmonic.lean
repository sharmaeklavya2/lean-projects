import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.List.Sort

noncomputable def cat (M : ℕ) (x : ℝ) : Nat :=
  min M (⌊1/x⌋.toNat)

noncomputable def w (M : ℕ) (x : ℝ) : ℝ :=
  -- M ≥ 1 and x ∈ (0, 1]
  if x ≤ 1/M then M * x / (M-1) else 1 / (⌊1/x⌋.toNat)

def A007018 : ℕ → ℕ
  -- https://oeis.org/A007018
  | 0 => 0
  | 1 => 1
  | n + 1 => A007018 n * (A007018 n + 1)

noncomputable def T : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 : ℝ) / (A007018 (n + 1)) + T n

theorem harmonic_bound_i (M : ℕ) (y : List ℝ) (i : ℕ)
  (hM : M ≥ 2)
  (hSorted : y.SortedGE)
  (hy : ∀ z ∈ y, (0 < z ∧ z ≤ 1))
  (hi : A007018 i < M ∧ M ≤ A007018 (i + 1))
  (hSum : y.sum ≤ 1)
  : (y.map (w M)).sum ≤ T i + (M / (M-1)) / (A007018 (i+1))
  := by sorry
