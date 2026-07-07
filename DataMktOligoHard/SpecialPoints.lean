import DataMktOligoHard.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Properties of the special points (sp-props.tex)

This file corresponds to the "Properties of the Special Points" subsection.
It establishes the interval bounds and defining identities of the special points
`(pᵢ, qᵢ)` and proves `μ(pᵢ, qᵢ) = μᵢ` for `i ∈ {1, 2, 3}`.
(The `i = 4` case is on the knife-edge `p = α·q` and is deferred to the case-4 file.)

(Notation: this section transcribes old-paper text, where the poor-buyer count is
written `n - 1`; that is our Lean `n`. In particular the paper's `n·ĉ₁` is our
`(n + 1)·chat1 = n + α·q1`.)

## Omitted results

These lemmas feed the next 4 subsections and the main claim (`cStar_le_μ`, in
`Pending`), so omissions are tracked here explicitly. Add back if later needed.

* Uniqueness of the positive roots of the defining quadratics for `p₁` (thm:p1),
  `q₂` (thm:q2), `μ₃` (thm:mu3). We formalize only *existence* (that the point
  satisfies its equation), which is all that `μ(pᵢ,qᵢ) = μᵢ` requires. Believed
  unneeded downstream.
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

/-- **thm:q1**:
1.  `q₁ ∈ (1/α, 1)`,
2.  `r₁*(q₁) = n·ĉ₁`,
3.  `r₁*(q) ≥ n·ĉ₁` for all `q ≥ 0`.
Here the paper's `n·ĉ₁` is our `(n + 1)·chat1` (paper's total-buyer count `n` is our `n + 1`);
we prove the last part for *all* `q`, not just `q ≥ 0`. -/
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
    ratio (cap α β n) (r1star α β n (q1 α β n)) (r1hi β n (p1 α β n) (q1 α β n)) = μ1 α β n := by
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
    ratio (cap α β n) (r2star α n (p1 α β n)) (r2lo n (p1 α β n) (q1 α β n)) = μ1 α β n := by
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
                m = max (ratio (cap α β n) (r1star α β n (q1 α β n)) r1)
                        (ratio (cap α β n) (r2star α n (p1 α β n)) r2)}
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

/-- **thm:p1**:
1.  `p₁ ∈ (α/(α+1), 1)`,
2.  `ĉ₁ > 1`,
3.  `p₁` solves its defining equation `ĉ₁/p₁ = p₁/(α(1-p₁))`
    (stated as the quadratic `p₁² = α·ĉ₁·(1-p₁)`),
4.  `μ(p₁, q₁) = μ₁`.
The paper's ratio equalities `r₁*(q₁)/r₁ = r₂*(p₁)/r₂ = μ₁` are `ratio1_p1_q1`/`ratio2_p1_q1`.
Not formalized: *uniqueness* of that positive root. -/
theorem thm_p1 (h : Constraints α β n) :
    p1 α β n ∈ Set.Ioo (α / (α + 1)) 1 ∧
    1 < chat1 α β n ∧
    (p1 α β n) ^ 2 = α * chat1 α β n * (1 - p1 α β n) ∧
    μ α β n (p1 α β n) (q1 α β n) = μ1 α β n :=
  ⟨⟨p1_gt_ratio h, p1_lt_one h⟩, chat1_gt_one h, p1_quadratic h, μ_p1_q1 h⟩

/-! ## Properties of `q₂` (thm:q2) -/

/-- `0 < L₂ = n² + αn + αβ`. -/
theorem L2_pos (h : Constraints α β n) : 0 < L2 α β n := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  simp only [L2]
  nlinarith [mul_pos hα hn, mul_pos hα hβ, sq_nonneg n]

/-- `0 < q₂`. -/
theorem q2_pos (h : Constraints α β n) : 0 < q2 α β n := by
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hn := n_pos h
  simp only [q2]
  apply div_pos (by linarith)
  linarith [Real.sqrt_nonneg (L2 α β n)]

/-- `α·q₂ = √L₂ - n` (the convenient closed form for `q₂`, since
`α(n+β) = (√L₂-n)(√L₂+n) = L₂ - n²`). -/
theorem alpha_mul_q2 (h : Constraints α β n) :
    α * q2 α β n = Real.sqrt (L2 α β n) - n := by
  have hn := n_pos h
  have hs_pos : 0 ≤ Real.sqrt (L2 α β n) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (L2 α β n) ^ 2 = L2 α β n := Real.sq_sqrt (L2_pos h).le
  simp only [q2]
  set s := Real.sqrt (L2 α β n)
  have hden : (n + s) ≠ 0 := ne_of_gt (by linarith)
  rw [mul_div_assoc', div_eq_iff hden]
  simp only [L2] at hs2
  linear_combination -hs2  -- α·(n+β) = (s-n)(n+s) = s² - n², using s² = L₂

/-- The defining quadratic `α·q₂² + 2n·q₂ = n + β` (thm:q2): `q₂` solves
`(αx+n)/(β+n(1-x)) = 1/x`. Derived from `α·q₂ + n = √L₂` (`alpha_mul_q2`). -/
theorem q2_quadratic (h : Constraints α β n) :
    α * (q2 α β n) ^ 2 + 2 * n * (q2 α β n) = n + β := by
  have hα := alpha_pos h
  have hαne : α ≠ 0 := ne_of_gt hα
  have hq2 : α * q2 α β n = Real.sqrt (L2 α β n) - n := alpha_mul_q2 h
  -- `(α·q₂ + n)² = (√L₂)² = L₂`.
  have hsq : (α * q2 α β n + n) ^ 2 = L2 α β n := by
    have he : α * q2 α β n + n = Real.sqrt (L2 α β n) := by rw [hq2]; ring
    rw [he]; exact Real.sq_sqrt (L2_pos h).le
  have hL2 : L2 α β n = n ^ 2 + α * n + α * β := by simp only [L2]
  -- `α·(α·q₂² + 2n·q₂) = (α·q₂+n)² - n² = αn + αβ = α·(n+β)`; cancel `α`.
  have hcancel : α * (α * q2 α β n ^ 2 + 2 * n * q2 α β n) = α * (n + β) := by
    linear_combination hsq + hL2
  exact mul_left_cancel₀ hαne hcancel

/-- `q₂ < 1` (thm:q2). Root-sign: `f(1) = α + n - β > 0` for the upward parabola
`f(x) = αx² + 2nx - (n+β)` with `f(q₂) = 0`. -/
theorem q2_lt_one (h : Constraints α β n) : q2 α β n < 1 := by
  nlinarith [q2_quadratic h, h.c1_hi, alpha_pos h, n_pos h, q2_pos h,
    mul_pos (alpha_pos h) (q2_pos h)]

/-- `1 < α·q₂`, i.e. `q₂ > 1/α` (thm:q2). Uses `α·q₂ = √L₂ - n` and `(n+1)² < L₂`
(equivalently `2n + 1 < α(n+β)`, from `α ≥ 2 ≤ β`). -/
theorem one_lt_alpha_mul_q2 (h : Constraints α β n) : 1 < α * q2 α β n := by
  have hn := n_pos h
  rw [alpha_mul_q2 h]
  have h1 : ((n + 1 : ℝ)) ^ 2 < L2 α β n := by
    simp only [L2]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ α - 2 by linarith [h.c1_lo]) hn.le,
      mul_nonneg (show (0:ℝ) ≤ α - 2 by linarith [h.c1_lo])
        (show (0:ℝ) ≤ β by linarith [h.c1_lo, h.c1_mid]), h.c1_lo, h.c1_mid]
  have h2 := Real.sqrt_lt_sqrt (sq_nonneg (n + 1)) h1
  rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ n + 1)] at h2
  linarith

/-- `1/α < q₂`, the lower end of `q₂ ∈ (1/α, 1)`. -/
theorem one_div_alpha_lt_q2 (h : Constraints α β n) : 1 / α < q2 α β n := by
  rw [div_lt_iff₀ (alpha_pos h)]
  nlinarith [one_lt_alpha_mul_q2 h]

/-- `α·q₂ < β` (thm:q2 line 101), since `α·q₂ < α ≤ β` (uses `q₂ < 1`). -/
theorem alpha_mul_q2_lt_beta (h : Constraints α β n) : α * q2 α β n < β := by
  have h1 : α * q2 α β n < α * 1 := mul_lt_mul_of_pos_left (q2_lt_one h) (alpha_pos h)
  rw [mul_one] at h1
  linarith [h.c1_mid]

/-- The `r₁⁻` component of `V` at `(β,q₂)`: `r₁⁻ = β + n·(1-q₂)`. -/
theorem r1lo_β_q2 (h : Constraints α β n) :
    r1lo β n β (q2 α β n) = β + n * (1 - q2 α β n) := by
  have h1q : (0:ℝ) ≤ 1 - q2 α β n := by linarith [q2_lt_one h]
  have h1q_le_β : 1 - q2 α β n ≤ β := by linarith [q2_pos h, h.c1_lo, h.c1_mid]
  simp only [r1lo]
  rw [min_self, max_eq_right h1q, min_eq_right h1q_le_β]

/-- The `r₂⁺` component of `V` at `(β,q₂)`: `r₂⁺ = n·q₂`. -/
theorem r2hi_β_q2 (h : Constraints α β n) :
    r2hi n β (q2 α β n) = n * q2 α β n := by
  simp only [r2hi]
  rw [min_eq_left (le_of_lt (q2_lt_one h))]

/-- `r₁*(q₂) = max(β + n(1-q₂), α·q₂ + n)` (uses `1 < α·q₂ < β` and `q₂ < 1`). -/
theorem r1star_q2 (h : Constraints α β n) :
    r1star α β n (q2 α β n) = max (β + n * (1 - q2 α β n)) (α * q2 α β n + n) := by
  have h1q : (0:ℝ) ≤ 1 - q2 α β n := by linarith [q2_lt_one h]
  simp only [r1star]
  rw [max_eq_right h1q, min_eq_right (le_of_lt (alpha_mul_q2_lt_beta h)),
      min_eq_left (le_of_lt (one_lt_alpha_mul_q2 h)), mul_one]

/-- `r₂*(β) = n` (uses `1 - β ≤ 1 ≤ β/α`). -/
theorem r2star_β (h : Constraints α β n) : r2star α n β = n := by
  have hα := alpha_pos h
  have hβα : (1:ℝ) ≤ β / α := by rw [le_div_iff₀ hα, one_mul]; exact h.c1_mid
  have h1β : 1 - β ≤ 1 := by linarith [h.c1_lo, h.c1_mid]
  simp only [r2star]
  rw [min_eq_left hβα, max_eq_right h1β]
  ring

/-- Seller 2's ratio at `(β,q₂)` equals `μ₂`: `n/(n·q₂) = 1/q₂`. -/
theorem ratio2_β_q2 (h : Constraints α β n) :
    ratio (cap α β n) (r2star α n β) (r2hi n β (q2 α β n)) = μ2 α β n := by
  have hn := n_pos h
  have hq2 := q2_pos h
  have hden : n * q2 α β n ≠ 0 := mul_ne_zero (ne_of_gt hn) (ne_of_gt hq2)
  rw [r2star_β h, r2hi_β_q2 h, ratio, if_neg hden]
  simp only [μ2]
  rw [div_eq_div_iff hden (ne_of_gt hq2)]
  ring

/-- Seller 1's ratio at `(β,q₂)` equals `μ₂`: with `A = β+n(1-q₂)`, `B = α·q₂+n`,
the quadratic gives `B·q₂ = A`, so `max(A,B) = B` (as `q₂ < 1`) and `B/A = 1/q₂`. -/
theorem ratio1_β_q2 (h : Constraints α β n) :
    ratio (cap α β n) (r1star α β n (q2 α β n)) (r1lo β n β (q2 α β n)) = μ2 α β n := by
  have hn := n_pos h
  have hq2 := q2_pos h
  have hq2lt := q2_lt_one h
  have hα := alpha_pos h
  have hA_pos : 0 < β + n * (1 - q2 α β n) := by
    have := mul_pos hn (show (0:ℝ) < 1 - q2 α β n by linarith)
    linarith [h.c1_lo, h.c1_mid]
  have hB_pos : 0 < α * q2 α β n + n := by
    have := mul_pos hα hq2; linarith
  have hBA : (α * q2 α β n + n) * q2 α β n = β + n * (1 - q2 α β n) := by
    linear_combination q2_quadratic h
  have hAB : β + n * (1 - q2 α β n) ≤ α * q2 α β n + n := by
    nlinarith [hBA, hB_pos, hq2lt]
  rw [r1star_q2 h, r1lo_β_q2 h, max_eq_right hAB, ratio, if_neg (ne_of_gt hA_pos)]
  simp only [μ2]
  rw [div_eq_div_iff (ne_of_gt hA_pos) (ne_of_gt hq2)]
  linear_combination q2_quadratic h

/-- `μ(p₂, q₂) = μ₂` (thm:q2), where `p₂ = β`. Here `p₂ > α·q₂`, so `V` is the
singleton `{(r₁⁻, r₂⁺)}` and both best-response ratios equal `μ₂`. -/
theorem μ_p2_q2 (h : Constraints α β n) :
    μ α β n (p2 β) (q2 α β n) = μ2 α β n := by
  simp only [p2]
  -- `V` is the singleton `{(r₁⁻, r₂⁺)}` (branch `p > α·q`, since `β > α·q₂`).
  have hV : V α β n β (q2 α β n)
          = {(r1lo β n β (q2 α β n), r2hi n β (q2 α β n))} := by
    unfold V
    rw [if_neg (not_le.mpr
          (by linarith [q2_pos h, h.c1_lo, h.c1_mid] : (1:ℝ) < β + q2 α β n)),
        if_neg (not_lt.mpr (le_of_lt (alpha_mul_q2_lt_beta h))),
        if_pos (alpha_mul_q2_lt_beta h)]
  have hset : {m : ℝ | ∃ r1 r2, (r1, r2) ∈ V α β n β (q2 α β n) ∧
                m = max (ratio (cap α β n) (r1star α β n (q2 α β n)) r1)
                        (ratio (cap α β n) (r2star α n β) r2)}
            = {μ2 α β n} := by
    rw [hV]
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨r1, r2, ⟨rfl, rfl⟩, rfl⟩
      rw [ratio1_β_q2 h, ratio2_β_q2 h, max_self]
    · rintro rfl
      exact ⟨_, _, ⟨rfl, rfl⟩, by rw [ratio1_β_q2 h, ratio2_β_q2 h, max_self]⟩
  unfold μ
  rw [hset, csInf_singleton]

/-! ### Paper-facing statement of thm:q2 -/

/-- **thm:q2**:
1.  `q₂ ∈ (1/α, 1)`
2.  `μ(β, q₂) = μ₂`.
3.  `q₂` solves `α·x² + 2n·x = n + β`, derived from `(αx+n)/(β+n(1-x)) = 1/x`.
The paper's ratio equalities `r₁*(q₂)/r₁ = r₂*(β)/r₂ = μ₂` are `ratio1_β_q2` and `ratio2_β_q2`,
from which `μ(β, q₂) = μ₂` follows.
Not formalized: that `q₂` is the *unique* positive root of `(αx+n)/(β+n(1-x)) = 1/x`. -/
theorem thm_q2 (h : Constraints α β n) :
    q2 α β n ∈ Set.Ioo (1 / α) 1 ∧
    μ α β n (p2 β) (q2 α β n) = μ2 α β n ∧
    α * (q2 α β n) ^ 2 + 2 * n * (q2 α β n) = n + β :=
  ⟨⟨one_div_alpha_lt_q2 h, q2_lt_one h⟩, μ_p2_q2 h, q2_quadratic h⟩

/-! ## Properties of `μ₃` (thm:mu3)

`μ₃` is the positive root of the quadratic `αβx² + n·L₁·x - L₂ = 0`
(paper: `αβx² + (n-1)(n-1+α-β)x - ((n-1)²+(n-1)α+αβ) = 0`). -/

/-- `0 < q₁ = β/(α+n)`. -/
theorem q1_pos (h : Constraints α β n) : 0 < q1 α β n :=
  div_pos (by linarith [h.c1_lo, h.c1_mid]) (alpha_add_n_pos h)

/-- `0 < L₁ = α + n - β`, from Constraint c1 (`β < α + n`). -/
theorem L1_pos (h : Constraints α β n) : 0 < L1 α β n := by
  simp only [L1]; linarith [h.c1_hi]

/-- The discriminant `D := n²L₁² + 4αβL₂ ≥ 0` under `D`'s square root in `μ₃`. -/
theorem mu3_disc_nonneg (h : Constraints α β n) :
    0 ≤ n ^ 2 * (L1 α β n) ^ 2 + 4 * α * β * L2 α β n := by
  have hα := alpha_pos h
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hL2 := L2_pos h
  nlinarith [sq_nonneg (n * L1 α β n), mul_pos (mul_pos hα hβ) hL2]

/-- `μ₃` satisfies its defining quadratic `αβ·μ₃² + n·L₁·μ₃ - L₂ = 0` (thm:mu3).
Proof: `2αβ·μ₃ + L₁·n = √D`; squaring kills the root and, after clearing `4αβ`,
leaves the quadratic. -/
theorem mu3_quadratic (h : Constraints α β n) :
    α * β * (μ3 α β n) ^ 2 + n * L1 α β n * μ3 α β n - L2 α β n = 0 := by
  have hα := alpha_pos h
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hab : (2 * α * β : ℝ) ≠ 0 := ne_of_gt (by nlinarith [mul_pos hα hβ])
  set D := n ^ 2 * (L1 α β n) ^ 2 + 4 * α * β * L2 α β n with hDdef
  have hD : 0 ≤ D := hDdef ▸ mu3_disc_nonneg h
  have hs2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
  have hval : 2 * α * β * μ3 α β n + L1 α β n * n = Real.sqrt D := by
    rw [μ3, ← hDdef]; field_simp; ring
  have hsq : (2 * α * β * μ3 α β n + L1 α β n * n) ^ 2 = D := by rw [hval]; exact hs2
  have key : 4 * α * β * (α * β * (μ3 α β n) ^ 2 + n * L1 α β n * μ3 α β n - L2 α β n) = 0 := by
    rw [hDdef] at hsq; linear_combination hsq
  have h4ne : (4 * α * β : ℝ) ≠ 0 := ne_of_gt (by nlinarith [mul_pos hα hβ])
  exact (mul_eq_zero.mp key).resolve_left h4ne

/-- `0 < μ₃` (thm:mu3): the numerator `√D - L₁n > 0` since `D > (L₁n)²`. -/
theorem mu3_pos (h : Constraints α β n) : 0 < μ3 α β n := by
  have hα := alpha_pos h
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hn := n_pos h
  have hL1 := L1_pos h
  have hL2 := L2_pos h
  have hLn_nonneg : 0 ≤ L1 α β n * n := mul_nonneg hL1.le hn.le
  have hlt : (L1 α β n * n) ^ 2 < n ^ 2 * (L1 α β n) ^ 2 + 4 * α * β * L2 α β n := by
    nlinarith [mul_pos (mul_pos hα hβ) hL2]
  have h2 : Real.sqrt ((L1 α β n * n) ^ 2)
          < Real.sqrt (n ^ 2 * (L1 α β n) ^ 2 + 4 * α * β * L2 α β n) :=
    Real.sqrt_lt_sqrt (by positivity) hlt
  rw [Real.sqrt_sq hLn_nonneg] at h2
  simp only [μ3]
  apply div_pos (by linarith [h2]) (by nlinarith [mul_pos hα hβ])

/-- `1 < μ₃` (thm:mu3): `f(1) = -βn < 0` for the upward parabola `f`, so its
positive root `μ₃` exceeds `1`. Concretely `(μ₃-1)(αβ(μ₃+1)+nL₁) = βn > 0`. -/
theorem one_lt_mu3 (h : Constraints α β n) : 1 < μ3 α β n := by
  have hα := alpha_pos h
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hn := n_pos h
  have hL1 := L1_pos h
  have hpos := mu3_pos h
  have hquad := mu3_quadratic h
  have hbr : 0 < α * β * (μ3 α β n + 1) + n * L1 α β n := by
    nlinarith [mul_pos hα hβ, mul_pos (mul_pos hα hβ) hpos, mul_pos hn hL1]
  have hfact : (μ3 α β n - 1) * (α * β * (μ3 α β n + 1) + n * L1 α β n) = β * n := by
    simp only [L1, L2] at hquad ⊢; linear_combination hquad
  nlinarith [hfact, hbr, mul_pos hβ hn]

/-- `β·μ₃ < α + n` (thm:mu3, the bound `μ₃ < 1/q₁`): `f(1/q₁) > 0` is Constraint c3,
so the positive root `μ₃` is below `1/q₁`, i.e. `β·μ₃ < α+n`. -/
theorem beta_mul_mu3_lt (h : Constraints α β n) : β * μ3 α β n < α + n := by
  have hα := alpha_pos h
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hn := n_pos h
  have hL1 := L1_pos h
  have hpos := mu3_pos h
  have hA := alpha_add_n_pos h
  have hquad := mu3_quadratic h
  have hbr : 0 < α * ((α + n) + β * μ3 α β n) + n * L1 α β n := by
    nlinarith [mul_pos hα hA, mul_pos (mul_pos hα hβ) hpos, mul_pos hn hL1]
  have hfact : ((α + n) - β * μ3 α β n) * (α * ((α + n) + β * μ3 α β n) + n * L1 α β n)
             = (α + n) ^ 3 - β * (α * β + 2 * n * (α + n)) := by
    simp only [L1, L2] at hquad ⊢; linear_combination (-β) * hquad
  have hHA : 0 < (α + n) ^ 3 - β * (α * β + 2 * n * (α + n)) := by linarith [h.c3]
  nlinarith [hfact, hbr, hHA]

/-- `q₁·μ₃ < 1` (thm:mu3), equivalent to `β·μ₃ < α+n`; used to place `p₃ < α`. -/
theorem q1_mul_mu3_lt_one (h : Constraints α β n) : q1 α β n * μ3 α β n < 1 := by
  have hA := alpha_add_n_pos h
  simp only [q1]
  rw [div_mul_eq_mul_div, div_lt_one hA]
  linarith [beta_mul_mu3_lt h]

/-- `μ₃ < 1/q₁` (thm:mu3), the upper end of `μ₃ ∈ (1, 1/q₁)`. -/
theorem mu3_lt_one_div_q1 (h : Constraints α β n) : μ3 α β n < 1 / q1 α β n := by
  rw [lt_div_iff₀ (q1_pos h), mul_comm]
  exact q1_mul_mu3_lt_one h

/-! ### Paper-facing statement of thm:mu3 -/

/-- **thm:mu3**:
1.  `1 < μ₃ < 1/q₁`,
2.  `μ₃` solves the quadratic `αβx² + n(n+α-β)x - (n²+nα+αβ) = 0`
    (paper's `n-1` is our `n`; `n+α-β = L₁`, `n²+nα+αβ = L₂`).
Not formalized: that `μ₃` is the *unique* positive root. -/
theorem thm_mu3 (h : Constraints α β n) :
    1 < μ3 α β n ∧ μ3 α β n < 1 / q1 α β n ∧
    α * β * (μ3 α β n) ^ 2 + n * (n + α - β) * (μ3 α β n) - (n ^ 2 + n * α + α * β) = 0 := by
  refine ⟨one_lt_mu3 h, mu3_lt_one_div_q1 h, ?_⟩
  have := mu3_quadratic h
  simp only [L1, L2] at this
  linear_combination this

/-! ## Properties of `p₃` (thm:p3)

`q₃ = q₁` and `p₃ = α·q₁·μ₃`. Since `μ₃ ∈ (1, 1/q₁)`, we get `p₃ ∈ (α·q₁, α)`,
so `p₃ > α·q₃`: `V` is the singleton `{(r₁⁻, r₂⁺)}` and both ratios equal `μ₃`.
We state helpers in terms of `q₁` (which is `q₃` by definition). -/

/-- `α·q₁ < p₃` (lower end of `p₃ ∈ (α·q₁, α)`): since `μ₃ > 1` and `α·q₁ > 0`. -/
theorem p3_gt_alpha_q1 (h : Constraints α β n) : α * q1 α β n < p3 α β n := by
  have hpos : 0 < α * q1 α β n := mul_pos (alpha_pos h) (q1_pos h)
  simp only [p3]
  nlinarith [mul_pos hpos (sub_pos.mpr (one_lt_mu3 h))]

/-- `p₃ < α` (upper end of `p₃ ∈ (α·q₁, α)`): since `q₁·μ₃ < 1`. -/
theorem p3_lt_alpha (h : Constraints α β n) : p3 α β n < α := by
  have hα := alpha_pos h
  simp only [p3]
  nlinarith [mul_pos hα (sub_pos.mpr (q1_mul_mu3_lt_one h))]

/-- `1 < p₃`: since `1 < α·q₁ < p₃`. -/
theorem p3_gt_one (h : Constraints α β n) : 1 < p3 α β n :=
  lt_trans (one_lt_alpha_mul_q1 h) (p3_gt_alpha_q1 h)

/-- `p₃ < β`: since `p₃ < α ≤ β`. -/
theorem p3_lt_beta (h : Constraints α β n) : p3 α β n < β :=
  lt_of_lt_of_le (p3_lt_alpha h) h.c1_mid

/-- The `r₁⁻` component of `V` at `(p₃,q₁)`: `r₁⁻ = p₃ + n·(1-q₁)`
(uses `p₃ < β` and `1-q₁ < 1 < p₃`). -/
theorem r1lo_p3_q1 (h : Constraints α β n) :
    r1lo β n (p3 α β n) (q1 α β n) = p3 α β n + n * (1 - q1 α β n) := by
  have hq1 := q1_lt_one h
  have hq1p := q1_pos h
  have hp3 := p3_gt_one h
  simp only [r1lo]
  rw [min_eq_left (le_of_lt (p3_lt_beta h)),
      max_eq_right (by linarith : (0:ℝ) ≤ 1 - q1 α β n),
      min_eq_right (by linarith : 1 - q1 α β n ≤ p3 α β n)]

/-- The `r₂⁺` component of `V` at `(p₃,q₁)`: `r₂⁺ = n·q₁` (uses `q₁ < 1`). -/
theorem r2hi_p3_q1 (h : Constraints α β n) :
    r2hi n (p3 α β n) (q1 α β n) = n * q1 α β n := by
  simp only [r2hi]
  rw [min_eq_left (le_of_lt (q1_lt_one h))]

/-- `r₂*(p₃) = n·(q₁·μ₃)` (uses `1-p₃ ≤ p₃/α ≤ 1` and `p₃/α = q₁·μ₃`). -/
theorem r2star_p3 (h : Constraints α β n) :
    r2star α n (p3 α β n) = n * (q1 α β n * μ3 α β n) := by
  have hα := alpha_pos h
  have hp3_1 := p3_gt_one h
  have hp3α : p3 α β n / α = q1 α β n * μ3 α β n := by
    simp only [p3]; field_simp
  have hle1 : p3 α β n / α ≤ 1 := by rw [hp3α]; linarith [q1_mul_mu3_lt_one h]
  have hle2 : 1 - p3 α β n ≤ p3 α β n / α := by
    have : 0 < p3 α β n / α := div_pos (by linarith) hα
    linarith
  simp only [r2star]
  rw [min_eq_right hle1, max_eq_right hle2, hp3α]

/-- Seller 2's ratio at `(p₃,q₃)` equals `μ₃`: `n·(q₁·μ₃)/(n·q₁) = μ₃`. -/
theorem ratio2_p3_q1 (h : Constraints α β n) :
    ratio (cap α β n) (r2star α n (p3 α β n)) (r2hi n (p3 α β n) (q1 α β n)) = μ3 α β n := by
  have hn := n_pos h
  have hq1 := q1_pos h
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn
  have hq1ne : q1 α β n ≠ 0 := ne_of_gt hq1
  have hden : n * q1 α β n ≠ 0 := mul_ne_zero hnne hq1ne
  rw [r2star_p3 h, r2hi_p3_q1 h, ratio, if_neg hden]
  field_simp

/-- Seller 1's ratio at `(p₃,q₃)` equals `μ₃`: `(n+α·q₁)/(p₃+n(1-q₁)) = μ₃`.
Multiplying out `q₁ = β/(α+n)` reduces to `L₂ = μ₃(αβμ₃+nL₁)`, i.e. the quadratic. -/
theorem ratio1_p3_q1 (h : Constraints α β n) :
    ratio (cap α β n) (r1star α β n (q1 α β n)) (r1lo β n (p3 α β n) (q1 α β n)) = μ3 α β n := by
  have hn := n_pos h
  have hq1lt := q1_lt_one h
  have hp3 := p3_gt_one h
  have hAnne : (α + n : ℝ) ≠ 0 := ne_of_gt (alpha_add_n_pos h)
  have hquad := mu3_quadratic h
  have hden_pos : 0 < p3 α β n + n * (1 - q1 α β n) := by
    have : 0 ≤ n * (1 - q1 α β n) := mul_nonneg hn.le (by linarith)
    linarith
  rw [r1star_q1 h, r1lo_p3_q1 h, ratio, if_neg (ne_of_gt hden_pos),
      div_eq_iff (ne_of_gt hden_pos)]
  simp only [p3, q1, L1, L2] at hquad ⊢
  field_simp at hquad ⊢
  linear_combination -hquad

/-- `μ(p₃, q₃) = μ₃` (thm:p3). Here `p₃ > α·q₃`, so `V` is the singleton
`{(r₁⁻, r₂⁺)}` and both best-response ratios equal `μ₃`. -/
theorem μ_p3_q3 (h : Constraints α β n) :
    μ α β n (p3 α β n) (q3 α β n) = μ3 α β n := by
  simp only [q3]
  -- `V` is the singleton `{(r₁⁻, r₂⁺)}` (branch `p > α·q`, since `p₃ > α·q₁ > 1`).
  have hV : V α β n (p3 α β n) (q1 α β n)
          = {(r1lo β n (p3 α β n) (q1 α β n), r2hi n (p3 α β n) (q1 α β n))} := by
    unfold V
    rw [if_neg (not_le.mpr (by linarith [p3_gt_one h, q1_pos h] :
          (1:ℝ) < p3 α β n + q1 α β n)),
        if_neg (not_lt.mpr (le_of_lt (p3_gt_alpha_q1 h))),
        if_pos (p3_gt_alpha_q1 h)]
  have hset : {m : ℝ | ∃ r1 r2, (r1, r2) ∈ V α β n (p3 α β n) (q1 α β n) ∧
                m = max (ratio (cap α β n) (r1star α β n (q1 α β n)) r1)
                        (ratio (cap α β n) (r2star α n (p3 α β n)) r2)}
            = {μ3 α β n} := by
    rw [hV]
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨r1, r2, ⟨rfl, rfl⟩, rfl⟩
      rw [ratio1_p3_q1 h, ratio2_p3_q1 h, max_self]
    · rintro rfl
      exact ⟨_, _, ⟨rfl, rfl⟩, by rw [ratio1_p3_q1 h, ratio2_p3_q1 h, max_self]⟩
  unfold μ
  rw [hset, csInf_singleton]

/-! ### Paper-facing statement of thm:p3 -/

/-- **thm:p3**:
1.  `p₃ ∈ (α·q₃, α)`,
2.  `μ(p₃, q₃) = μ₃`.
The paper's ratio equalities `r₁*(q₃)/r₁ = r₂*(p₃)/r₂ = μ₃` are `ratio1_p3_q1` and
`ratio2_p3_q1` (using `q₃ = q₁`), from which `μ(p₃, q₃) = μ₃` follows. -/
theorem thm_p3 (h : Constraints α β n) :
    p3 α β n ∈ Set.Ioo (α * q3 α β n) α ∧
    μ α β n (p3 α β n) (q3 α β n) = μ3 α β n :=
  ⟨⟨p3_gt_alpha_q1 h, p3_lt_alpha h⟩, μ_p3_q3 h⟩

/-! ## The candidate values `μᵢ` are below the cap `α·β + n`

These bounds let the case files prove the sharp form `μ(p,q) ≥ X` (rather than the
old workaround `μ(p,q) ≥ min (cap α β n) X`), since each intermediate bound `X`
is one of the `μᵢ` and sits strictly below the cap. -/

/-- `α ≤ cap = α·β + n` (since `β ≥ 1` and `n > 0`). A common final step. -/
theorem alpha_le_cap (h : Constraints α β n) : α ≤ cap α β n := by
  have hα := alpha_pos h
  have hβ : (1:ℝ) ≤ β := by linarith [h.c1_lo, h.c1_mid]
  have hn := n_pos h
  simp only [cap]
  nlinarith [mul_le_mul_of_nonneg_left hβ hα.le]

/-- `μ₂ ≤ cap` (thm:q2): `μ₂ = 1/q₂ < α ≤ cap`, using `1 < α·q₂`. -/
theorem μ2_le_cap (h : Constraints α β n) : μ2 α β n ≤ cap α β n := by
  have hq2 := q2_pos h
  have hlt : μ2 α β n < α := by
    simp only [μ2]
    rw [div_lt_iff₀ hq2]
    linarith [one_lt_alpha_mul_q2 h]
  linarith [alpha_le_cap h]

/-- `μ₃ ≤ cap` (thm:mu3): `μ₃ < 1/q₁ = (α+n)/β ≤ α+n ≤ cap`. -/
theorem μ3_le_cap (h : Constraints α β n) : μ3 α β n ≤ cap α β n := by
  have hβpos : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hα := alpha_pos h
  have hn := n_pos h
  have hstep : (1:ℝ) / q1 α β n ≤ cap α β n := by
    simp only [q1, one_div_div, cap]
    rw [div_le_iff₀ hβpos]
    nlinarith [mul_le_mul_of_nonneg_left h.c1_mid hα.le, h.c1_lo, h.c1_mid, hn,
      mul_pos hα hβpos]
  linarith [mu3_lt_one_div_q1 h, hstep]

/-- `μ₄ ≤ cap` (thm:mu4/case4): `μ₄ = 1 + βn/L₂ < 2 ≤ cap`, since `L₂ > βn`
(as `L₂ − βn = n·L₁ + αβ > 0`). -/
theorem μ4_le_cap (h : Constraints α β n) : μ4 α β n ≤ cap α β n := by
  have hβpos : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hα := alpha_pos h
  have hn := n_pos h
  have hL2 := L2_pos h
  have hbnL2 : β * n / L2 α β n < 1 := by
    rw [div_lt_one hL2]
    simp only [L2]
    have hexp : 0 < n * (α + n - β) := by nlinarith [hn, h.c1_hi]
    nlinarith [hexp, mul_pos hα hβpos]
  have hcap : (2:ℝ) ≤ cap α β n := by
    simp only [cap]
    nlinarith [mul_le_mul (h.c1_lo) (le_trans h.c1_lo h.c1_mid) (by norm_num : (0:ℝ) ≤ 2) hα.le, hn]
  simp only [μ4]
  linarith

/-- `ĉ₁ < α·β/2` (thm:p1). Since `ĉ₁·(n+1)·(α+n) = L₂` (as `n + α·q₁ = L₂/(α+n)`),
`L₂ < (n+1)·α·β` (Constraint c2: `n + α < α·β`) and `α + n > 2`, we get
`ĉ₁·2·(n+1) < ĉ₁·(n+1)·(α+n) = L₂ < (n+1)·α·β`, hence `ĉ₁ < α·β/2`. -/
theorem chat1_lt_half_alpha_beta (h : Constraints α β n) : chat1 α β n < α * β / 2 := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hβpos : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hn1 : (0:ℝ) < n + 1 := by linarith
  -- `ĉ₁·(n+1)·(α+n) = L₂`.
  have hchatL2 : chat1 α β n * (n + 1) * (α + n) = L2 α β n := by
    have hne : (α + n) ≠ 0 := ne_of_gt (alpha_add_n_pos h)
    simp only [chat1, q1, L2]; field_simp; ring
  -- `L₂ < (n+1)·α·β`, from `n + α < α·β`.
  have hL2ub : L2 α β n < (n + 1) * (α * β) := by
    simp only [L2]; nlinarith [h.c2, hn, mul_pos hn (show (0:ℝ) < α * β - α - n by linarith [h.c2])]
  -- `α + n > 2`, so `2·(n+1)·ĉ₁ < (α+n)·(n+1)·ĉ₁ = L₂ < (n+1)·αβ`.
  have hαn2 : (2:ℝ) < α + n := by linarith [h.c1_lo, hn]
  have hub : chat1 α β n * (n + 1) * 2 < (α * β / 2) * (n + 1) * 2 := by
    have hcpos : 0 < chat1 α β n * (n + 1) := mul_pos (by linarith [chat1_gt_one h]) hn1
    nlinarith [hchatL2, hL2ub, hcpos, mul_lt_mul_of_pos_left hαn2 hcpos]
  nlinarith [hub, hn1]

/-- `1/2 ≤ p₁` (thm:p1). Since `α·ĉ₁ > 2`, we have `√(1 + 4/(α·ĉ₁)) < √9 = 3`,
so `p₁ = 2/(1 + √…) > 2/4 = 1/2`. This is the clean form of `1/p₁ < 2`. -/
theorem p1_ge_half (h : Constraints α β n) : (1:ℝ) / 2 ≤ p1 α β n := by
  have hα := alpha_pos h
  have hk : 0 < α * chat1 α β n := alpha_mul_chat1_pos h
  -- `α·ĉ₁ ≥ 2`, so `4/(α·ĉ₁) ≤ 2` and the radicand is `≤ 9`.
  have hkey : (2:ℝ) ≤ α * chat1 α β n := by
    nlinarith [mul_nonneg (by linarith [h.c1_lo] : (0:ℝ) ≤ α - 2)
      (by linarith [chat1_gt_one h] : (0:ℝ) ≤ chat1 α β n - 1), h.c1_lo, chat1_gt_one h]
  have h4 : 4 / (α * chat1 α β n) ≤ 2 := by
    rw [div_le_iff₀ hk]; linarith
  have h9 : 1 + 4 / (α * chat1 α β n) ≤ (3:ℝ) ^ 2 := by norm_num; linarith
  have hs : Real.sqrt (1 + 4 / (α * chat1 α β n)) ≤ 3 := by
    calc Real.sqrt (1 + 4 / (α * chat1 α β n))
        ≤ Real.sqrt ((3:ℝ) ^ 2) := Real.sqrt_le_sqrt h9
      _ = 3 := by rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
  simp only [p1]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hs, Real.sqrt_nonneg (1 + 4 / (α * chat1 α β n))]

/-- `μ₁ ≤ cap` (thm:p1). `μ₁ = ĉ₁/p₁`; with `ĉ₁ < α·β/2` (`chat1_lt_half_alpha_beta`)
and `p₁ ≥ 1/2` (`p1_ge_half`), `μ₁ = ĉ₁/p₁ ≤ 2·ĉ₁ < α·β ≤ cap`. -/
theorem μ1_le_cap (h : Constraints α β n) : μ1 α β n ≤ cap α β n := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hβpos : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hp1 := p1_pos h
  have hcap : 0 < α * β + n := by positivity
  have hchat := chat1_lt_half_alpha_beta h
  have hhalf := p1_ge_half h
  simp only [μ1, cap]
  rw [div_le_iff₀ hp1]
  -- goal: `ĉ₁ ≤ (αβ + n)·p₁`. Since `p₁ ≥ 1/2`, RHS `≥ (αβ+n)/2 = αβ/2 + n/2 > ĉ₁`.
  nlinarith [mul_le_mul_of_nonneg_left hhalf hcap.le, hchat, hn]

end DataMktOligoHard
