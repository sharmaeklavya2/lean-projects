module

public import DataMktOligoHard.Defs
import DataMktOligoHard.SpecialPoints
import Mathlib.Tactic.LinearCombination

/-! ## The candidate values `μᵢ` are below the cap `α·β + n` -/

namespace DataMktOligoHard

variable {α β n : ℝ}

/-- `α ≤ cap = α·β + n` (since `β ≥ 1` and `n > 0`). A common final step. -/
theorem alpha_le_cap (h : Constraints α β n) : α ≤ cap α β n := by
  have hα := alpha_pos h
  have hβ : (1:ℝ) ≤ β := by linarith [h.c1_lo, h.c1_mid]
  have hn := n_pos h
  simp only [cap]
  nlinarith [mul_le_mul_of_nonneg_left hβ hα.le]

/-- `μ₂ ≤ cap` (thm:q2): `μ₂ = 1/q₂ < α ≤ cap`, using `1 < α·q₂`. -/
public theorem μ2_le_cap (h : Constraints α β n) : μ2 α β n ≤ cap α β n := by
  have hq2 := q2_pos h
  have hlt : μ2 α β n < α := by
    simp only [μ2]
    rw [div_lt_iff₀ hq2]
    linarith [one_lt_alpha_mul_q2 h]
  linarith [alpha_le_cap h]

/-- `μ₃ ≤ cap` (thm:mu3): `μ₃ < 1/q₁ = (α+n)/β ≤ α+n ≤ cap`. -/
public theorem μ3_le_cap (h : Constraints α β n) : μ3 α β n ≤ cap α β n := by
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
public theorem μ4_le_cap (h : Constraints α β n) : μ4 α β n ≤ cap α β n := by
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
public theorem μ1_le_cap (h : Constraints α β n) : μ1 α β n ≤ cap α β n := by
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
