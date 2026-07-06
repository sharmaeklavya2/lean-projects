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

/-- `1/α < q₁` (thm:q1), the lower end of `q₁ ∈ (1/α, 1)`. -/
theorem one_div_alpha_lt_q1 (h : Constraints α β n) : 1 / α < q1 α β n := by
  rw [div_lt_iff₀ (alpha_pos h)]
  nlinarith [one_lt_alpha_mul_q1 h]

/-- `r₁*(q₁) = (n+1)·ĉ₁`, i.e. the paper's `n·ĉ₁` (paper's total-buyer count `n`
is our `n + 1`). -/
theorem r1star_q1' (h : Constraints α β n) :
    r1star α β n (q1 α β n) = (n + 1) * chat1 α β n := by
  have hn1 : (n:ℝ) + 1 ≠ 0 := by linarith [n_pos h]
  rw [r1star_q1 h]
  simp only [chat1]
  field_simp

/-! ### Paper-facing statement of thm:q1

The theorem below transcribes thm:q1 verbatim; its proof only assembles the helper
lemmas above. A verifier checks *this statement* against the paper, and
`#print axioms thm_q1` to confirm it rests on no `sorry`. -/

/-- **thm:q1** (paper): `q₁ ∈ (1/α, 1)`, `r₁*(q₁) = n·ĉ₁`, and `r₁*(q) ≥ n·ĉ₁` for
all `q ≥ 0`. Here the paper's `n·ĉ₁` is our `(n + 1)·chat1` (paper's total-buyer
count `n` is our `n + 1`); we prove the last part for *all* `q`, not just `q ≥ 0`. -/
theorem thm_q1 (h : Constraints α β n) :
    q1 α β n ∈ Set.Ioo (1 / α) 1 ∧
    r1star α β n (q1 α β n) = (n + 1) * chat1 α β n ∧
    ∀ q, 0 ≤ q → (n + 1) * chat1 α β n ≤ r1star α β n q := by
  have hnc : (n + 1) * chat1 α β n = n + α * q1 α β n := by
    rw [← r1star_q1' h, r1star_q1 h]
  refine ⟨⟨one_div_alpha_lt_q1 h, q1_lt_one h⟩, r1star_q1' h, fun q _ => ?_⟩
  rw [hnc]; exact r1star_ge h q

/-! ## Properties of `ĉ₁` and `p₁` (thm:p1) -/

/-- `ĉ₁ > 1` (thm:p1): since `ĉ₁ = (n + α·q₁)/(n + 1)` and `α·q₁ > 1`. -/
theorem chat1_gt_one (h : Constraints α β n) : 1 < chat1 α β n := by
  have hn1 : (0:ℝ) < n + 1 := by linarith [n_pos h]
  simp only [chat1]
  rw [one_lt_div hn1]
  linarith [one_lt_alpha_mul_q1 h]

/-- `0 < α·ĉ₁` (the quantity under `p₁`'s square root uses `4/(α·ĉ₁)`). -/
theorem alpha_mul_chat1_pos (h : Constraints α β n) : 0 < α * chat1 α β n :=
  mul_pos (alpha_pos h) (by linarith [chat1_gt_one h])

/-- `0 < p₁` (independent of the constraints — the square root is `≥ 0`). -/
theorem p1_pos (_h : Constraints α β n) : 0 < p1 α β n := by
  simp only [p1]; positivity

/-- `p₁ < 1` (thm:p1), since the square root exceeds `1`. -/
theorem p1_lt_one (h : Constraints α β n) : p1 α β n < 1 := by
  have hk : 0 < α * chat1 α β n := alpha_mul_chat1_pos h
  have hr1 : 1 < 1 + 4 / (α * chat1 α β n) := by
    have : 0 < 4 / (α * chat1 α β n) := by positivity
    linarith
  have hs_gt1 : 1 < Real.sqrt (1 + 4 / (α * chat1 α β n)) := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hr1
    rwa [Real.sqrt_one] at this
  simp only [p1]
  rw [div_lt_one (by positivity)]
  linarith

/-- The defining identity `p₁² = α·ĉ₁·(1 - p₁)` (thm:p1): `p₁` solves
`ĉ₁/x = x/(α(1-x))`, i.e. `x² + α·ĉ₁·x - α·ĉ₁ = 0`. Reduces to `k(s² - 1) = 4`
where `k = α·ĉ₁`, `s = √(1 + 4/k)`. -/
theorem p1_quadratic (h : Constraints α β n) :
    p1 α β n ^ 2 = α * chat1 α β n * (1 - p1 α β n) := by
  have hk : 0 < α * chat1 α β n := alpha_mul_chat1_pos h
  simp only [p1]
  set k := α * chat1 α β n with hk_def
  have hkne : k ≠ 0 := ne_of_gt hk
  have hr0 : 0 ≤ 1 + 4 / k := by positivity
  set s := Real.sqrt (1 + 4 / k) with hs_def
  have hs2 : s ^ 2 = 1 + 4 / k := by rw [hs_def]; exact Real.sq_sqrt hr0
  have hu : (1 + s) ≠ 0 := by positivity
  have hkey : k * s ^ 2 = k + 4 := by rw [hs2]; field_simp
  field_simp
  -- goal: `2 ^ 2 = (1 + s) * k * (1 + s - 2)`; the RHS is `k·s² - k = 4`.
  have expand : (1 + s) * k * (1 + s - 2) = k * s ^ 2 - k := by ring
  rw [expand, hkey]; ring

/-- `α·(1 - p₁) < p₁`, i.e. `1 - p₁ < p₁/α` (thm:p1 line 68). Chain:
`α(1-p₁) < α·ĉ₁·(1-p₁) = p₁² < p₁`, using `ĉ₁ > 1` and `0 < p₁ < 1`. -/
theorem alpha_mul_one_sub_p1_lt_p1 (h : Constraints α β n) :
    α * (1 - p1 α β n) < p1 α β n := by
  have hq := p1_quadratic h
  have hc := chat1_gt_one h
  have hp1_pos := p1_pos h
  have hp1_lt := p1_lt_one h
  have hα := alpha_pos h
  nlinarith [hq, mul_pos (sub_pos.mpr hp1_lt) hp1_pos,
    mul_pos (mul_pos hα (sub_pos.mpr hp1_lt)) (sub_pos.mpr hc)]

/-- `p₁ < α·q₁` (thm:p1 line 68): since `p₁ < 1 < α·q₁`. -/
theorem p1_lt_alpha_mul_q1 (h : Constraints α β n) : p1 α β n < α * q1 α β n := by
  linarith [p1_lt_one h, one_lt_alpha_mul_q1 h]

/-- `1 < p₁ + q₁` (thm:p1 line 68): since `1 - p₁ < 1/α < q₁`
(from `α(1-p₁) < 1 < α·q₁`). -/
theorem one_lt_p1_add_q1 (h : Constraints α β n) : 1 < p1 α β n + q1 α β n := by
  have h1 := alpha_mul_one_sub_p1_lt_p1 h
  have h2 := p1_lt_one h
  have h3 := one_lt_alpha_mul_q1 h
  have hα := alpha_pos h
  have hstep : α * (1 - p1 α β n) < α * q1 α β n := by linarith
  have := lt_of_mul_lt_mul_left hstep hα.le
  linarith

/-- `α/(α+1) < p₁` (thm:p1 line 47), the lower end of `p₁ ∈ (α/(α+1), 1)`.
Equivalent to `α(1-p₁) < p₁`. -/
theorem p1_gt_ratio (h : Constraints α β n) : α / (α + 1) < p1 α β n := by
  have hα := alpha_pos h
  rw [div_lt_iff₀ (by linarith : (0:ℝ) < α + 1)]
  nlinarith [alpha_mul_one_sub_p1_lt_p1 h]

/-- The `r₁⁺` component of `V` at `(p₁,q₁)`: `r₁⁺ = p₁·(1+n)` (uses `p₁ < 1 ≤ β`). -/
theorem r1hi_p1_q1 (h : Constraints α β n) :
    r1hi β n (p1 α β n) (q1 α β n) = p1 α β n * (1 + n) := by
  have hp1_le_β : p1 α β n ≤ β := by linarith [p1_lt_one h, h.c1_lo, h.c1_mid]
  simp only [r1hi]
  rw [min_eq_left hp1_le_β, min_eq_left (le_of_lt (p1_lt_one h))]
  ring

/-- The `r₂⁻` component of `V` at `(p₁,q₁)`: `r₂⁻ = n·(1-p₁)` (uses `1-p₁ ≤ q₁`). -/
theorem r2lo_p1_q1 (h : Constraints α β n) :
    r2lo n (p1 α β n) (q1 α β n) = n * (1 - p1 α β n) := by
  have h1p : (0:ℝ) ≤ 1 - p1 α β n := by linarith [p1_lt_one h]
  have hq1 : 1 - p1 α β n ≤ q1 α β n := by linarith [one_lt_p1_add_q1 h]
  simp only [r2lo]
  rw [max_eq_right h1p, min_eq_right hq1]

/-- `r₂*(p₁) = n·(p₁/α)` (uses `1-p₁ ≤ p₁/α ≤ 1`). -/
theorem r2star_p1 (h : Constraints α β n) :
    r2star α n (p1 α β n) = n * (p1 α β n / α) := by
  have hα := alpha_pos h
  have hp1_lt := p1_lt_one h
  have hp1_div_le : p1 α β n / α ≤ 1 := by rw [div_le_one hα]; linarith [h.c1_lo]
  have h1p_le : 1 - p1 α β n ≤ p1 α β n / α := by
    rw [le_div_iff₀ hα]; nlinarith [alpha_mul_one_sub_p1_lt_p1 h]
  simp only [r2star]
  rw [min_eq_right hp1_div_le, max_eq_right h1p_le]

/-- Seller 1's ratio at `(p₁,q₁)` equals `μ₁`: `(n+α·q₁)/(p₁(1+n)) = ĉ₁/p₁`,
using `n + α·q₁ = ĉ₁·(n+1)`. -/
theorem ratio1_p1_q1 (h : Constraints α β n) :
    ratio (r1star α β n (q1 α β n)) (r1hi β n (p1 α β n) (q1 α β n)) = μ1 α β n := by
  have hp1_pos := p1_pos h
  have hn := n_pos h
  have hden : p1 α β n * (1 + n) ≠ 0 :=
    mul_ne_zero (ne_of_gt hp1_pos) (ne_of_gt (by linarith : (0:ℝ) < 1 + n))
  rw [r1star_q1 h, r1hi_p1_q1 h, ratio, if_neg hden]
  simp only [μ1, chat1]
  rw [div_div]
  congr 1
  ring

/-- Seller 2's ratio at `(p₁,q₁)` equals `μ₁`: `(p₁/α)/(1-p₁) = ĉ₁/p₁`,
using the quadratic `p₁² = α·ĉ₁·(1-p₁)`. -/
theorem ratio2_p1_q1 (h : Constraints α β n) :
    ratio (r2star α n (p1 α β n)) (r2lo n (p1 α β n) (q1 α β n)) = μ1 α β n := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hp1_pos := p1_pos h
  have hp1_lt := p1_lt_one h
  have h1p_pos : (0:ℝ) < 1 - p1 α β n := by linarith
  have hden : n * (1 - p1 α β n) ≠ 0 := mul_ne_zero (ne_of_gt hn) (ne_of_gt h1p_pos)
  rw [r2star_p1 h, r2lo_p1_q1 h, ratio, if_neg hden,
      mul_div_mul_left (p1 α β n / α) (1 - p1 α β n) (ne_of_gt hn), div_div]
  simp only [μ1]
  rw [div_eq_div_iff (ne_of_gt (mul_pos hα h1p_pos)) (ne_of_gt hp1_pos)]
  have hpp : p1 α β n * p1 α β n = p1 α β n ^ 2 := by ring
  rw [hpp, p1_quadratic h]; ring

/-- `μ(p₁, q₁) = μ₁` (thm:p1). Here `p₁ < α·q₁`, so `V` is the singleton
`{(r₁⁺, r₂⁻)}` and both best-response ratios equal `μ₁`. -/
theorem μ_p1_q1 (h : Constraints α β n) :
    μ α β n (p1 α β n) (q1 α β n) = μ1 α β n := by
  -- `V` is the singleton `{(r₁⁺, r₂⁻)}` (branch `p < α·q`, since `p₁ + q₁ > 1`).
  have hV : V α β n (p1 α β n) (q1 α β n)
          = {(r1hi β n (p1 α β n) (q1 α β n), r2lo n (p1 α β n) (q1 α β n))} := by
    unfold V
    rw [if_neg (not_le.mpr (one_lt_p1_add_q1 h)), if_pos (p1_lt_alpha_mul_q1 h)]
  -- The `sInf`'s set is the singleton `{μ₁}` (both ratios equal `μ₁`).
  have hset : {m : ℝ | ∃ r1 r2, (r1, r2) ∈ V α β n (p1 α β n) (q1 α β n) ∧
                m = max (ratio (r1star α β n (q1 α β n)) r1)
                        (ratio (r2star α n (p1 α β n)) r2)}
            = {μ1 α β n} := by
    rw [hV]
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨r1, r2, ⟨rfl, rfl⟩, rfl⟩
      rw [ratio1_p1_q1 h, ratio2_p1_q1 h, max_self]
    · rintro rfl
      exact ⟨_, _, ⟨rfl, rfl⟩, by rw [ratio1_p1_q1 h, ratio2_p1_q1 h, max_self]⟩
  unfold μ
  rw [hset, csInf_singleton]

/-! ### Paper-facing statement of thm:p1 -/

/-- **thm:p1** (paper): `p₁ ∈ (α/(α+1), 1)`, `ĉ₁ > 1`, and `μ(p₁, q₁) = μ₁`.
The paper's ratio equalities `r₁*(q₁)/r₁ = r₂*(p₁)/r₂ = μ₁` are `ratio1_p1_q1` and
`ratio2_p1_q1`, from which `μ(p₁, q₁) = μ₁` follows. Not formalized: that `p₁` is the
*unique* positive root of `ĉ₁/x = x/(α(1-x))` (only existence, `p1_quadratic`, is
needed downstream). -/
theorem thm_p1 (h : Constraints α β n) :
    p1 α β n ∈ Set.Ioo (α / (α + 1)) 1 ∧
    1 < chat1 α β n ∧
    μ α β n (p1 α β n) (q1 α β n) = μ1 α β n :=
  ⟨⟨p1_gt_ratio h, p1_lt_one h⟩, chat1_gt_one h, μ_p1_q1 h⟩

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
