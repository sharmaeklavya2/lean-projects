import DataMktOligoHard.Basic

/-!
# Properties of the special points (sp-props.tex)

This file corresponds to the "Properties of the Special Points" subsection.
It establishes the interval bounds and defining identities of the special points
`(pᵢ, qᵢ)` and proves `μ(pᵢ, qᵢ) = μᵢ` for `i ∈ {1, 2, 3}`.
(The `i = 4` case is on the knife-edge `p = α·q` and is deferred to the case-4 file.)

(Notation: this section transcribes old-paper text, where the poor-buyer count is
written `n - 1`; that is our Lean `n`. In particular the paper's `n·ĉ₁` is our
`(n + 1)·chat1 = n + α·q1`.)
-/

namespace DataMktOligoHard

variable {α β n : ℝ}

/-! ## Positivity facts from the constraints -/

/-- `0 < α`, from Constraint c1 (`2 ≤ α`). -/
theorem alpha_pos (h : Constraints α β n) : 0 < α := by linarith [h.c1_lo]

/-- `0 < n`, from `α ≤ β < α + n`. -/
theorem n_pos (h : Constraints α β n) : 0 < n := by linarith [h.c1_mid, h.c1_hi]

/-- `0 < α + n`. -/
theorem alpha_add_n_pos (h : Constraints α β n) : 0 < α + n := by
  linarith [alpha_pos h, n_pos h]

/-! ## Properties of `q₁` (thm:q1) -/

/-- `q₁ < 1`, from Constraint c1 (`β < α + n`). -/
theorem q1_lt_one (h : Constraints α β n) : q1 α β n < 1 := by
  simp only [q1]
  rw [div_lt_one (alpha_add_n_pos h)]
  exact h.c1_hi

/-- `1 < α·q₁`, i.e. `q₁ > 1/α`, from Constraint c2 (`α + n < α·β`). -/
theorem one_lt_alpha_mul_q1 (h : Constraints α β n) : 1 < α * q1 α β n := by
  simp only [q1]
  rw [← mul_div_assoc, one_lt_div (alpha_add_n_pos h)]
  exact h.c2

/-- `α·q₁ < β`, since `α·q₁ < α ≤ β` (uses `q₁ < 1`). -/
theorem alpha_mul_q1_lt_beta (h : Constraints α β n) : α * q1 α β n < β := by
  have h1 : α * q1 α β n < α * 1 := mul_lt_mul_of_pos_left (q1_lt_one h) (alpha_pos h)
  rw [mul_one] at h1
  linarith [h.c1_mid]

/-- First `max` branch of `r₁*` at `q₁`: `g₁(q₁) = β + n·(1 - q₁) = n + α·q₁`
(uses `q₁ < 1`). -/
theorem g1_q1 (h : Constraints α β n) :
    β + n * max 0 (1 - q1 α β n) = n + α * q1 α β n := by
  have hne : (α + n) ≠ 0 := ne_of_gt (alpha_add_n_pos h)
  rw [max_eq_right (by linarith [q1_lt_one h] : (0:ℝ) ≤ 1 - q1 α β n)]
  simp only [q1]; field_simp; ring

/-- Second `max` branch of `r₁*` at `q₁`: `g₂(q₁) = α·q₁ + n = n + α·q₁`
(uses `1 < α·q₁ < β`). -/
theorem g2_q1 (h : Constraints α β n) :
    min β (α * q1 α β n) + n * min 1 (α * q1 α β n) = n + α * q1 α β n := by
  rw [min_eq_right (le_of_lt (alpha_mul_q1_lt_beta h)),
      min_eq_left (le_of_lt (one_lt_alpha_mul_q1 h))]
  ring

/-- `r₁*(q₁) = n + α·q₁` (thm:q1). Both `max` branches evaluate to this common value. -/
theorem r1star_q1 (h : Constraints α β n) :
    r1star α β n (q1 α β n) = n + α * q1 α β n := by
  unfold r1star
  rw [g1_q1 h, g2_q1 h, max_self]

/-- `r₁*(q) ≥ n + α·q₁` for all `q` (thm:q1). For `q ≤ q₁` the non-increasing first
branch `g₁` dominates; for `q ≥ q₁` the non-decreasing second branch `g₂` does. -/
theorem r1star_ge (h : Constraints α β n) (q : ℝ) :
    n + α * q1 α β n ≤ r1star α β n q := by
  have hn : (0:ℝ) < n := n_pos h
  have hα : (0:ℝ) < α := alpha_pos h
  unfold r1star
  rcases le_total q (q1 α β n) with hle | hle
  · -- `q ≤ q₁`: `n + α·q₁ = g₁(q₁) ≤ g₁(q) ≤ max`.
    refine le_trans ?_ (le_max_left _ _)
    rw [← g1_q1 h]
    have hmax : max 0 (1 - q1 α β n) ≤ max 0 (1 - q) := max_le_max le_rfl (by linarith)
    have := mul_le_mul_of_nonneg_left hmax hn.le
    linarith
  · -- `q₁ ≤ q`: `n + α·q₁ = g₂(q₁) ≤ g₂(q) ≤ max`.
    refine le_trans ?_ (le_max_right _ _)
    rw [← g2_q1 h]
    have hαle : α * q1 α β n ≤ α * q := mul_le_mul_of_nonneg_left hle hα.le
    have hm1 : min β (α * q1 α β n) ≤ min β (α * q) := min_le_min le_rfl hαle
    have hm2 : min 1 (α * q1 α β n) ≤ min 1 (α * q) := min_le_min le_rfl hαle
    have := mul_le_mul_of_nonneg_left hm2 hn.le
    linarith

/-- `μ(p₁, q₁) = μ₁` (thm:p1). Here `p₁ < α·q₁`, so `V` is the singleton
`{(r₁⁺, r₂⁻)}` and both best-response ratios equal `μ₁`. -/
theorem μ_p1_q1 (h : Constraints α β n) :
    μ α β n (p1 α β n) (q1 α β n) = μ1 α β n := by
  sorry

/-- `μ(p₂, q₂) = μ₂` (thm:q2), where `p₂ = β`. Here `p₂ > α·q₂`, so `V` is the
singleton `{(r₁⁻, r₂⁺)}` and both best-response ratios equal `μ₂`. -/
theorem μ_p2_q2 (h : Constraints α β n) :
    μ α β n (p2 β) (q2 α β n) = μ2 α β n := by
  sorry

/-- `μ(p₃, q₃) = μ₃` (thm:p3). Here `p₃ > α·q₃`, so `V` is the singleton
`{(r₁⁻, r₂⁺)}` and both best-response ratios equal `μ₃`. -/
theorem μ_p3_q3 (h : Constraints α β n) :
    μ α β n (p3 α β n) (q3 α β n) = μ3 α β n := by
  sorry

end DataMktOligoHard
