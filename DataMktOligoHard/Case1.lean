module

public import DataMktOligoHard.Defs
import DataMktOligoHard.SpecialPoints
import DataMktOligoHard.Cap
import Mathlib.Tactic.LinearCombination

/-!
# Case 1 of the main reduction (case1.tex)

This file corresponds to the "Case 1: `p > α·q` and `p + q ≥ 1`" subsection.
In this region `V(p,q)` is the singleton `{(r₁⁻, r₂⁺)}`, so
`μ(p,q) = max(r₁*(q)/r₁⁻, r₂*(p)/r₂⁺)`.
-/

namespace DataMktOligoHard

variable {α β n : ℝ}

/-! ## `μ` as a max in the case-1 region -/

/-- `r₂*(p) = n` when `p ≥ α` (then `p/α ≥ 1`, so both `min(1,p/α) = 1` and
`max(1-p, 1) = 1`). -/
theorem r2star_eq_n (h : Constraints α β n) {p : ℝ} (hpα : α ≤ p) :
    r2star α n p = n := by
  have hα := alpha_pos h
  have h1 : (1:ℝ) ≤ p / α := by rw [le_div_iff₀ hα]; linarith
  have h2 : 1 - p ≤ 1 := by linarith [h.c1_lo]
  simp only [r2star]
  rw [min_eq_left h1, max_eq_right h2, mul_one]

/-- In the case-1 region (`p > α·q` and `p + q ≥ 1`, with `0 ≤ q`), `V` is the
singleton `{(r₁⁻, r₂⁺)}`, so `μ(p,q) = max(r₁*(q)/r₁⁻, r₂*(p)/r₂⁺)`.
At the boundary `p + q = 1`, `V` takes its `{(r₁⁻, r₂⁻)}` branch instead, but there
`r₂⁻ = r₂⁺` (since `1 - p = q ≤ 1`), so the singleton is the same. -/
theorem μ_eq_max_case1 (h : Constraints α β n) {p q : ℝ}
    (hq : 0 ≤ q) (hpq1 : 1 ≤ p + q) (hpaq : α * q < p) :
    μ α β n p q = max (ratio (cap α β n) (r1star α β n q) (r1lo β n p q))
                      (ratio (cap α β n) (r2star α n p) (r2hi n p q)) := by
  have hV : V α β n p q = {(r1lo β n p q, r2hi n p q)} := by
    rcases lt_or_eq_of_le hpq1 with hlt | heq
    · unfold V
      rw [if_neg (not_le.mpr hlt), if_neg (not_lt.mpr hpaq.le), if_pos hpaq]
    · have hp1 : (1:ℝ) - p = q := by linarith
      have hqlt1 : q < 1 := by
        have h0 : (0:ℝ) ≤ α * q := mul_nonneg (alpha_pos h).le hq
        linarith
      have hr2 : r2lo n p q = r2hi n p q := by
        simp only [r2lo, r2hi, hp1]
        rw [max_eq_right hq, min_self, min_eq_left (le_of_lt hqlt1)]
      unfold V
      rw [if_pos (le_of_eq heq.symm), hr2]
  have hset : {m : ℝ | ∃ r1 r2, (r1, r2) ∈ V α β n p q ∧
                m = max (ratio (cap α β n) (r1star α β n q) r1)
                        (ratio (cap α β n) (r2star α n p) r2)}
            = {max (ratio (cap α β n) (r1star α β n q) (r1lo β n p q))
                   (ratio (cap α β n) (r2star α n p) (r2hi n p q))} := by
    rw [hV]; ext m
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨r1, r2, ⟨rfl, rfl⟩, rfl⟩; rfl
    · rintro rfl; exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩
  unfold μ; rw [hset, csInf_singleton]

/-! ### thm:1.1 -/

/-- **thm:1.1**: if `p > α·q` and `p ≥ α`, then `μ(p,q) ≥ μ₂`. At the `q = 0` corner
seller 2 earns `0`, so `μ = cap`, and `μ₂ ≤ cap` (`μ2_le_cap`) closes it.

The paper also lists `p + q ≥ 1` (it defines the whole Case-1 region), but here that
hypothesis is redundant: with the standing price assumption `0 ≤ q` and `p ≥ α ≥ 2`
(c1) we already get `p + q ≥ 2 > 1`.

For `q ≤ q₂` seller 2's ratio `1/q ≥ 1/q₂ = μ₂` already suffices (with the `q = 0`
corner handled by `μ₂ ≤ cap`). For `q ≥ q₂` seller 1's ratio dominates: the monotone
chain `r₁⁻ ≤ β + n(1-q₂) = q₂(αq₂+n) ≤ q₂·r₁*(q)` gives `r₁*(q)/r₁⁻ ≥ 1/q₂ = μ₂`. -/
public theorem thm_1_1 (h : Constraints α β n) {p q : ℝ}
    (hq : 0 ≤ q) (hpaq : α * q < p) (hpα : α ≤ p) :
    μ2 α β n ≤ μ α β n p q := by
  have hn := n_pos h
  have hα := alpha_pos h
  have hpq1 : 1 < p + q := by linarith [h.c1_lo]
  rw [μ_eq_max_case1 h hq hpq1.le hpaq]
  rcases le_total q (q2 α β n) with hqq2 | hq2q
  · -- `q ≤ q₂`: seller 2's ratio.
    refine le_trans ?_ (le_max_right _ _)
    rcases eq_or_lt_of_le hq with hq0 | hqpos
    · -- `q = 0`: `r₂⁺ = 0`, ratio is `cap ≥ μ₂`.
      have hr : r2hi n p q = 0 := by
        rw [r2hi, ← hq0, min_eq_left (zero_le_one), mul_zero]
      rw [ratio, if_pos hr]
      exact μ2_le_cap h
    · -- `0 < q ≤ q₂ < 1`: ratio is `1/q ≥ 1/q₂ = μ₂`.
      have hq1 : q < 1 := lt_of_le_of_lt hqq2 (q2_lt_one h)
      rw [r2star_eq_n h hpα, r2hi, min_eq_left (le_of_lt hq1),
          ratio, if_neg (mul_ne_zero (ne_of_gt hn) (ne_of_gt hqpos))]
      simp only [μ2]
      rw [div_le_div_iff₀ (q2_pos h) (mul_pos hn hqpos), one_mul]
      exact mul_le_mul_of_nonneg_left hqq2 hn.le
  · -- `q₂ ≤ q`: seller 1's ratio.
    refine le_trans ?_ (le_max_left _ _)
    have hq2lt := q2_lt_one h
    have hαq2 := one_lt_alpha_mul_q2 h
    have hαq2β := alpha_mul_q2_lt_beta h
    have haq1 : (1:ℝ) ≤ α * q := by
      have : α * q2 α β n ≤ α * q := mul_le_mul_of_nonneg_left hq2q hα.le
      linarith
    -- `r₁*(q) ≥ min(β,αq) + n` (second `max` branch, since `αq ≥ 1`).
    have hM : min β (α * q) + n ≤ r1star α β n q := by
      simp only [r1star]
      rw [show min β (α * q) + n * min 1 (α * q) = min β (α * q) + n from by
            rw [min_eq_left haq1]; ring]
      exact le_max_right _ _
    -- `r₁⁻ ≤ β + n·max(0, 1-q)`.
    have hr1lo_ub : r1lo β n p q ≤ β + n * max 0 (1 - q) := by
      simp only [r1lo]
      have h2 := mul_le_mul_of_nonneg_left (min_le_right p (max 0 (1 - q))) hn.le
      linarith [min_le_right p β, h2]
    -- `q₂(αq₂+n) = β + n(1-q₂)` (the defining quadratic of `q₂`).
    have hqid : q2 α β n * (α * q2 α β n + n) = β + n * (1 - q2 α β n) := by
      linear_combination q2_quadratic h
    -- monotone chain: `β + n·max(0,1-q) ≤ q₂·(min(β,αq) + n)`.
    have hchain : β + n * max 0 (1 - q) ≤ q2 α β n * (min β (α * q) + n) := by
      have hmaxle : max 0 (1 - q) ≤ 1 - q2 α β n := by
        apply max_le
        · linarith [hq2lt]
        · linarith [hq2q]
      have hnmax : n * max 0 (1 - q) ≤ n * (1 - q2 α β n) :=
        mul_le_mul_of_nonneg_left hmaxle hn.le
      have hminge : α * q2 α β n ≤ min β (α * q) :=
        le_min hαq2β.le (mul_le_mul_of_nonneg_left hq2q hα.le)
      have hq2min : q2 α β n * (α * q2 α β n) ≤ q2 α β n * min β (α * q) :=
        mul_le_mul_of_nonneg_left hminge (q2_pos h).le
      nlinarith [hqid, hnmax, hq2min]
    -- `r₁⁻ > 0`.
    have hr1lo_pos : 0 < r1lo β n p q := by
      simp only [r1lo]
      have hm1 : α ≤ min p β := le_min (by linarith) h.c1_mid
      have hm2 : 0 ≤ n * min p (max 0 (1 - q)) :=
        mul_nonneg hn.le (le_min (by linarith [h.c1_lo]) (le_max_left _ _))
      linarith [h.c1_lo]
    -- assemble: `μ₂ = 1/q₂ ≤ r₁*(q)/r₁⁻`.
    rw [ratio, if_neg (ne_of_gt hr1lo_pos)]
    simp only [μ2]
    rw [div_le_div_iff₀ (q2_pos h) hr1lo_pos, one_mul]
    have hstep : q2 α β n * (min β (α * q) + n) ≤ q2 α β n * r1star α β n q :=
      mul_le_mul_of_nonneg_left hM (q2_pos h).le
    nlinarith [hr1lo_ub, hchain, hstep]

/-! ### thm:mu3-2 -/

/-- **thm:mu3-2**: `μ₃ < 1 + β/n` (paper's `1 + β/(n-1)`; our `n` is the paper's `n-1`).

`f(1 + β/n) > 0` is Constraint c4, and since `μ₃` is the positive root of the upward
parabola `f(x) = αβx² + n·L₁·x - L₂`, this places `μ₃` below `1 + β/n`. Concretely,
clearing the denominator, `((n+β) - n·μ₃)·(αβ((n+β)+n·μ₃) + n²·L₁) = β·(α(β+n)² - βn²)`,
whose RHS is `> 0` by c4 and whose second factor is `> 0`, forcing `n·μ₃ < n+β`. -/
theorem thm_mu3_2 (h : Constraints α β n) : μ3 α β n < 1 + β / n := by
  have hn := n_pos h
  have hn0 : (n:ℝ) ≠ 0 := hn.ne'
  have hα := alpha_pos h
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hL1 := L1_pos h
  have hpos := mu3_pos h
  have hquad := mu3_quadratic h
  -- second factor of the identity is positive
  have hbr : 0 < α * β * ((n + β) + n * μ3 α β n) + n ^ 2 * L1 α β n := by
    have h1 := mul_pos (mul_pos hα hβ)
      (by linarith [mul_pos hn hpos] : (0:ℝ) < (n + β) + n * μ3 α β n)
    nlinarith [mul_pos (mul_pos hn hn) hL1]
  -- the c4 quantity is positive
  have hc4pos : 0 < β * (α * (β + n) ^ 2 - β * n ^ 2) := mul_pos hβ (by linarith [h.c4])
  -- the factorization identity (uses `μ₃`'s defining quadratic)
  have hfact : ((n + β) - n * μ3 α β n) *
        (α * β * ((n + β) + n * μ3 α β n) + n ^ 2 * L1 α β n)
      = β * (α * (β + n) ^ 2 - β * n ^ 2) := by
    simp only [L1, L2] at hquad ⊢
    linear_combination (-n ^ 2) * hquad
  -- so the first factor is positive: `n·μ₃ < n+β`
  have hX : 0 < (n + β) - n * μ3 α β n := by nlinarith [hfact, hbr, hc4pos]
  have hrw : 1 + β / n - μ3 α β n = ((n + β) - n * μ3 α β n) / n := by
    field_simp
  rw [← sub_pos, hrw]
  exact div_pos hX hn

/-! ### thm:1.2

The `p ≤ α` sub-case. Both of the paper's contradiction branches reduce to the same
identity `f(μ₃) = 0`, read against a different lower bound of `r₁*(q)`. We package the
two "slope" quantities `K := αμ₃² - nμ₃ + n` and `M := α + nμ₃ - αμ₃²` and show each is
positive — these are the coefficients that make the monotone comparisons go through. -/

/-- `K := α·μ₃² - n·μ₃ + n > 0`. From `β·K = (α+n)(β + n - n·μ₃)` (the quadratic) with
`β + n - n·μ₃ > 0` (thm:mu3-2). -/
theorem mu3_K_pos (h : Constraints α β n) :
    0 < α * (μ3 α β n) ^ 2 - n * μ3 α β n + n := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hbn : 0 < β + n - n * μ3 α β n := by
    have h1 := thm_mu3_2 h
    have h2 : n * μ3 α β n < n * (1 + β / n) := mul_lt_mul_of_pos_left h1 hn
    have h3 : n * (1 + β / n) = n + β := by field_simp
    rw [h3] at h2; linarith
  have hE : β * (α * (μ3 α β n) ^ 2 - n * μ3 α β n + n)
      = (α + n) * (β + n - n * μ3 α β n) := by
    have hq := mu3_quadratic h
    simp only [L1, L2] at hq
    linear_combination hq
  nlinarith [hE, mul_pos (alpha_add_n_pos h) hbn, hβ]

/-- `M := α + n·μ₃ - α·μ₃² > 0`. From `β·M = (α+n)·n·(μ₃ - 1)` (the quadratic) with
`μ₃ > 1` (thm:mu3). -/
theorem mu3_M_pos (h : Constraints α β n) :
    0 < α + n * μ3 α β n - α * (μ3 α β n) ^ 2 := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hm := one_lt_mu3 h
  have hM : β * (α + n * μ3 α β n - α * (μ3 α β n) ^ 2)
      = (α + n) * n * (μ3 α β n - 1) := by
    have hq := mu3_quadratic h
    simp only [L1, L2] at hq
    linear_combination (-1) * hq
  nlinarith [hM, mul_pos (mul_pos (alpha_add_n_pos h) hn)
    (show (0:ℝ) < μ3 α β n - 1 by linarith), hβ]

/-- **thm:1.2**: if `p + q ≥ 1`, `p > α·q`, and `p ≤ α`, then `μ(p,q) ≥ μ₃`. At the
`q = 0` corner seller 2 earns `0`, so `μ = cap`, and `μ₃ ≤ cap` (`μ3_le_cap`) closes it.

At `q = 0` seller 2 earns `0`, so `ratio₂ = cap ≥ μ₃`. For `q > 0`, seller 2's
ratio is `p/(αq)`: if `p ≥ α·q·μ₃` this already gives `μ ≥ p/(αq) ≥ μ₃`. Otherwise
`p < α·μ₃·q`, and seller 1's ratio dominates: writing `r₁⁻ = p + n(1-q)` and using the
lower bounds `r₁*(q) ≥ β + n(1-q)` (for `q ≤ q₁`) or `r₁*(q) ≥ αq + n` (for `q ≥ q₁`),
the gap to `μ₃·r₁⁻` is `K·(β - q(α+n))` resp. `M·(q(α+n) - β)`, nonnegative by the sign
of `q - q₁`. -/
public theorem thm_1_2 (h : Constraints α β n) {p q : ℝ}
    (hq : 0 ≤ q) (hpq1 : 1 ≤ p + q) (hpaq : α * q < p) (hpα : p ≤ α) :
    μ3 α β n ≤ μ α β n p q := by
  rw [μ_eq_max_case1 h hq hpq1 hpaq]
  rcases eq_or_lt_of_le hq with hq0 | hqpos
  · -- `q = 0`: `r₂⁺ = 0`, so `ratio₂ = cap ≥ μ₃`.
    have hr2cap : ratio (cap α β n) (r2star α n p) (r2hi n p q) = cap α β n := by
      have hr : r2hi n p q = 0 := by rw [r2hi, ← hq0, min_eq_left zero_le_one, mul_zero]
      rw [ratio, if_pos hr]
    rw [hr2cap]
    exact le_trans (μ3_le_cap h) (le_max_right _ _)
  have hn := n_pos h
  have hα := alpha_pos h
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hμ3 := mu3_pos h
  have hp_pos : 0 < p := lt_of_le_of_lt (mul_nonneg hα.le hqpos.le) hpaq
  have hqlt1 : q < 1 := by
    have h1 : α * q < α * 1 := by rw [mul_one]; linarith
    exact lt_of_mul_lt_mul_left h1 hα.le
  -- exact value of `r₁⁻` in this region
  have hr1lo : r1lo β n p q = p + n * (1 - q) := by
    simp only [r1lo]
    rw [min_eq_left (le_trans hpα h.c1_mid),
        max_eq_right (by linarith : (0:ℝ) ≤ 1 - q),
        min_eq_right (by linarith : 1 - q ≤ p)]
  have hr1lo_pos : 0 < r1lo β n p q := by
    rw [hr1lo]; nlinarith [mul_pos hn (show (0:ℝ) < 1 - q by linarith)]
  -- seller 2's ratio is `p/(αq)`
  have hr2star : r2star α n p = n * (p / α) := by
    have hpα1 : p / α ≤ 1 := by rw [div_le_one hα]; exact hpα
    have hqd : q < p / α := by rw [lt_div_iff₀ hα]; linarith [hpaq]
    have h1p : 1 - p ≤ p / α := by linarith [hqd]
    simp only [r2star]
    rw [min_eq_right hpα1, max_eq_right h1p]
  have hr2hi : r2hi n p q = n * q := by
    simp only [r2hi]; rw [min_eq_left (le_of_lt hqlt1)]
  have hratio2 : ratio (cap α β n) (r2star α n p) (r2hi n p q) = p / (α * q) := by
    rw [hr2star, hr2hi, ratio, if_neg (mul_ne_zero (ne_of_gt hn) (ne_of_gt hqpos)),
        mul_div_mul_left (p / α) q (ne_of_gt hn), div_div]
  rcases le_total (α * μ3 α β n * q) p with hA | hB
  · -- `p ≥ α·q·μ₃`: seller 2's ratio already clears `μ₃`.
    refine le_trans ?_ (le_max_right _ _)
    rw [hratio2, le_div_iff₀ (mul_pos hα hqpos)]
    nlinarith [hA]
  · -- `p ≤ α·μ₃·q`: seller 1's ratio clears `μ₃`.
    have hpB' : p ≤ α * μ3 α β n * q := hB
    refine le_trans ?_ (le_max_left _ _)
    rw [ratio, if_neg (ne_of_gt hr1lo_pos), le_div_iff₀ hr1lo_pos, hr1lo]
    -- goal: `μ₃·(p + n(1-q)) ≤ r₁*(q)`
    rcases le_total q (q1 α β n) with hqq1 | hq1q
    · -- `q ≤ q₁`: use `r₁*(q) ≥ β + n(1-q)`.
      have hg1 : β + n * (1 - q) ≤ r1star α β n q := by
        simp only [r1star]
        rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - q)]
        exact le_max_left _ _
      have hqle : q * (α + n) ≤ β := by
        rw [q1, le_div_iff₀ (alpha_add_n_pos h)] at hqq1; exact hqq1
      have hS1 : (α + n) * ((β + n * (1 - q)) -
            (α * (μ3 α β n) ^ 2 * q + μ3 α β n * n * (1 - q)))
          = (α * (μ3 α β n) ^ 2 - n * μ3 α β n + n) * (β - q * (α + n)) := by
        have hq := mu3_quadratic h
        simp only [L1, L2] at hq
        linear_combination (-1) * hq
      have hexpr : 0 ≤ (β + n * (1 - q)) -
          (α * (μ3 α β n) ^ 2 * q + μ3 α β n * n * (1 - q)) := by
        have hrhs : 0 ≤ (α * (μ3 α β n) ^ 2 - n * μ3 α β n + n) * (β - q * (α + n)) :=
          mul_nonneg (mu3_K_pos h).le (by linarith [hqle])
        nlinarith [hS1, hrhs, alpha_add_n_pos h]
      calc μ3 α β n * (p + n * (1 - q))
          ≤ μ3 α β n * (α * μ3 α β n * q + n * (1 - q)) :=
            mul_le_mul_of_nonneg_left (by linarith [hpB']) hμ3.le
        _ = α * (μ3 α β n) ^ 2 * q + μ3 α β n * n * (1 - q) := by ring
        _ ≤ β + n * (1 - q) := by linarith [hexpr]
        _ ≤ r1star α β n q := hg1
    · -- `q ≥ q₁`: use `r₁*(q) ≥ αq + n`.
      have h1αq : 1 < α * q := by
        have h1 := lt_of_lt_of_le (one_div_alpha_lt_q1 h) hq1q
        rw [div_lt_iff₀ hα] at h1; linarith
      have hαqβ : α * q < β := by
        have h1 : α * q < α * 1 := by rw [mul_one]; linarith
        linarith [h.c1_mid]
      have hg2 : α * q + n ≤ r1star α β n q := by
        simp only [r1star]
        rw [min_eq_right (le_of_lt hαqβ), min_eq_left (le_of_lt h1αq), mul_one]
        exact le_max_right _ _
      have hqge : β ≤ q * (α + n) := by
        rw [q1, div_le_iff₀ (alpha_add_n_pos h)] at hq1q; exact hq1q
      have hS2 : (α + n) * ((α * q + n) -
            (α * (μ3 α β n) ^ 2 * q + μ3 α β n * n * (1 - q)))
          = (α + n * μ3 α β n - α * (μ3 α β n) ^ 2) * (q * (α + n) - β) := by
        have hq := mu3_quadratic h
        simp only [L1, L2] at hq
        linear_combination (-1) * hq
      have hexpr2 : 0 ≤ (α * q + n) -
          (α * (μ3 α β n) ^ 2 * q + μ3 α β n * n * (1 - q)) := by
        have hrhs : 0 ≤ (α + n * μ3 α β n - α * (μ3 α β n) ^ 2) * (q * (α + n) - β) :=
          mul_nonneg (mu3_M_pos h).le (by linarith [hqge])
        nlinarith [hS2, hrhs, alpha_add_n_pos h]
      calc μ3 α β n * (p + n * (1 - q))
          ≤ μ3 α β n * (α * μ3 α β n * q + n * (1 - q)) :=
            mul_le_mul_of_nonneg_left (by linarith [hpB']) hμ3.le
        _ = α * (μ3 α β n) ^ 2 * q + μ3 α β n * n * (1 - q) := by ring
        _ ≤ α * q + n := by linarith [hexpr2]
        _ ≤ r1star α β n q := hg2

/-- combination of thm_1_1 and thm_1_2 -/
public theorem thm_1 (h : Constraints α β n) {p q : ℝ}
    (hq : 0 ≤ q) (hpq1 : 1 ≤ p + q) (hpaq : α * q < p) :
    min (μ2 α β n) (μ3 α β n) ≤ μ α β n p q := by
    simp only [min_le_iff]
    by_cases hpα : α ≤ p
    · left ; exact thm_1_1 h hq hpaq hpα
    · right ; exact thm_1_2 h hq hpq1 hpaq (le_of_not_ge hpα)


end DataMktOligoHard
