import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-- The w₃ weight function -/
noncomputable def w3 (x : ℝ) : ℝ :=
  if 1/2 < x then 1
  else if 1/3 < x then 1/2
  else 3 * x / 2

/-- Harmonic-3: if items fit in one bin (sum ≤ 1), their w₃-weight is ≤ 7/4 -/
theorem harmonic_k3 {n : ℕ} (s : Fin n → ℝ)
    (hs_positive : ∀ i, 0 < s i)
    (hsum : ∑ i, s i ≤ 1) :
    ∑ i, w3 (s i) ≤ 7/4 := by
  let L : Finset (Fin n) := Finset.univ.filter (fun i => 1/2 < s i)
  let M : Finset (Fin n) := Finset.univ.filter (fun i => 1/3 < s i ∧ s i ≤ 1/2)
  let S : Finset (Fin n) := Finset.univ.filter (fun i => s i ≤ 1/3)
  have hL : L.card ≤ 1 := by
    by_contra h
    push Not at h
    -- h : 1 < L.card; extract two distinct elements a, b ∈ L
    rw [Finset.one_lt_card] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    -- Each has size > 1/2
    have hsa : 1/2 < s a := by
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at ha; exact ha
    have hsb : 1/2 < s b := by
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hb; exact hb
    -- So s a + s b ≤ ∑ i ∈ L, s i (since {a,b} ⊆ L and s is nonneg)
    have hpair : s a + s b ≤ ∑ i ∈ L, s i := by
      have hLsub : ({a, b} : Finset _) ⊆ L := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hb
      calc s a + s b
          = ∑ i ∈ ({a, b} : Finset _), s i := (Finset.sum_pair hab).symm
        _ ≤ ∑ i ∈ L, s i := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hLsub
            intros i _ _; exact le_of_lt (hs_positive i)
    -- And ∑ i ∈ L, s i ≤ ∑ i, s i ≤ 1
    have hLle : ∑ i ∈ L, s i ≤ 1 := by
      have : ∑ i ∈ L, s i ≤ ∑ i, s i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intros i _ _; exact le_of_lt (hs_positive i)
      linarith
    linarith
  -- Step 2: L, M, S partition Fin n
  have hpartition : Finset.univ = L ∪ M ∪ S := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_union, L, M, S,
               Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro
      by_cases h1 : 1/2 < s i
      · left; left; exact h1
      · by_cases h2 : 1/3 < s i
        · left; right; exact ⟨h2, not_lt.mp h1⟩
        · right; exact not_lt.mp h2
    · intro; trivial
  have hdisjoint : Disjoint (L ∪ M) S := by
    simp only [Finset.disjoint_left, Finset.mem_union, L, M, S,
               Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi his
    rcases hi with h1 | ⟨h2, _⟩
    · linarith
    · linarith
  have hdisjointLM : Disjoint L M := by
    simp only [Finset.disjoint_left, L, M,
               Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi him
    linarith [him.2]
  -- Split the sum
  have hsum_split : ∑ i, w3 (s i) = ∑ i ∈ L, w3 (s i) + ∑ i ∈ M, w3 (s i) + ∑ i ∈ S, w3 (s i) := by
    rw [← Finset.sum_union hdisjointLM, ← Finset.sum_union hdisjoint, ← hpartition]
  -- Step 3: simplify w3 on each class
  have hwL : ∀ i ∈ L, w3 (s i) = 1 := fun i hi => by
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [w3, if_pos hi]
  have hwM : ∀ i ∈ M, w3 (s i) = 1/2 := fun i hi => by
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [w3, if_neg (not_lt.mpr hi.2), if_pos hi.1]
  have hwS : ∀ i ∈ S, w3 (s i) = 3 * s i / 2 := fun i hi => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [w3, if_neg (not_lt.mpr (le_trans hi (by norm_num : (1:ℝ)/3 ≤ 1/2))),
               if_neg (not_lt.mpr hi)]
  -- Step 4: compute weight sums using w3 values on each class
  have hWL : ∑ i ∈ L, w3 (s i) = L.card := by
    rw [Finset.sum_congr rfl hwL, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hWM : ∑ i ∈ M, w3 (s i) = M.card / 2 := by
    rw [Finset.sum_congr rfl hwM, Finset.sum_const, nsmul_eq_mul]; ring
  have hWS : ∑ i ∈ S, w3 (s i) = 3/2 * ∑ i ∈ S, s i := by
    have h : ∑ i ∈ S, w3 (s i) = ∑ i ∈ S, (3/2 * s i) :=
      Finset.sum_congr rfl (fun i hi => by rw [hwS i hi]; ring)
    rw [h, ← Finset.mul_sum]
  -- Step 5: size lower bounds (each L-item > 1/2, each M-item > 1/3)
  have hSL : (L.card : ℝ) / 2 ≤ ∑ i ∈ L, s i := by
    have h : ∑ i ∈ L, (1/2 : ℝ) ≤ ∑ i ∈ L, s i :=
      Finset.sum_le_sum (fun i hi => by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hi; linarith)
    simp only [Finset.sum_const, nsmul_eq_mul] at h; linarith
  have hSM : (M.card : ℝ) / 3 ≤ ∑ i ∈ M, s i := by
    have h : ∑ i ∈ M, (1/3 : ℝ) ≤ ∑ i ∈ M, s i :=
      Finset.sum_le_sum (fun i hi => by
        simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at hi; linarith [hi.1])
    simp only [Finset.sum_const, nsmul_eq_mul] at h; linarith
  -- Step 6: total size splits across L, M, S and is ≤ 1
  have hsize_split : ∑ i ∈ L, s i + ∑ i ∈ M, s i + ∑ i ∈ S, s i ≤ 1 := by
    have heq : ∑ i, s i = ∑ i ∈ L, s i + ∑ i ∈ M, s i + ∑ i ∈ S, s i := by
      rw [← Finset.sum_union hdisjointLM, ← Finset.sum_union hdisjoint, ← hpartition]
    linarith
  -- Step 7: combine everything
  have hSS : (0 : ℝ) ≤ ∑ i ∈ S, s i :=
    Finset.sum_nonneg (fun i _ => le_of_lt (hs_positive i))
  have hLcard : (L.card : ℝ) ≤ 1 := by exact_mod_cast hL
  have hMcard : (0 : ℝ) ≤ M.card := Nat.cast_nonneg _
  rw [hsum_split, hWL, hWM, hWS]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ ∑ i ∈ L, s i - L.card / 2 by linarith)
                        (show (0:ℝ) ≤ 3/2 by norm_num),
             mul_nonneg (show (0:ℝ) ≤ ∑ i ∈ M, s i - M.card / 3 by linarith)
                        (show (0:ℝ) ≤ 3/2 by norm_num),
             mul_nonneg (show (0:ℝ) ≤ 1 - (L.card : ℝ) by linarith)
                        (show (0:ℝ) ≤ 1/4 by norm_num),
             mul_nonneg (show (0:ℝ) ≤ 1 - ∑ i ∈ L, s i - ∑ i ∈ M, s i - ∑ i ∈ S, s i by linarith)
                        (show (0:ℝ) ≤ 3/2 by norm_num)]
