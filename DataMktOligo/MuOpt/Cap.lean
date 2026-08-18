module

public import DataMktOligo.MuOpt.Revenue
public import DataMktOligo.MuOpt.ParamConstraints
public import DataMktOligo.MuOpt.Constants
import DataMktOligo.MuOpt.SpecialPointsProps
import Mathlib.Tactic.LinearCombination

/-! ## The candidate values `μᵢ` are below the cap `α·β + ν` -/

namespace DataMktOligo.MuOpt

variable {α β ν : ℝ}

/-- `α ≤ cap = α·β + ν` (since `β ≥ 1` and `ν > 0`). A common final step. -/
theorem alpha_le_cap (h : Constraints α β ν) : α ≤ cap α β ν := by
  have hα := alpha_pos h
  have hβ : (1:ℝ) ≤ β := by linarith [h.c1_lo, h.c1_mid]
  have hν := nu_pos h
  simp only [cap]
  nlinarith [mul_le_mul_of_nonneg_left hβ hα.le]

/-- `μ₂ ≤ cap` (thm:lne-cex:q2): `μ₂ = 1/q₂ < α ≤ cap`, using `1 < α·q₂`. -/
public theorem μ2_le_cap (h : Constraints α β ν) : μ2 α β ν ≤ cap α β ν := by
  have hq2 := q2_pos h
  have hlt : μ2 α β ν < α := by
    simp only [μ2]
    rw [div_lt_iff₀ hq2]
    linarith [one_lt_alpha_mul_q2 h]
  linarith [alpha_le_cap h]

/-- `μ₃ ≤ cap` (thm:lne-cex:mu3): `μ₃ < 1/q₁ = (α+ν)/β ≤ α+ν ≤ cap`. -/
public theorem μ3_le_cap (h : Constraints α β ν) : μ3 α β ν ≤ cap α β ν := by
  have hβpos : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hα := alpha_pos h
  have hν := nu_pos h
  have hstep : (1:ℝ) / q1 α β ν ≤ cap α β ν := by
    simp only [q1, one_div_div, cap]
    rw [div_le_iff₀ hβpos]
    nlinarith [mul_le_mul_of_nonneg_left h.c1_mid hα.le, h.c1_lo, h.c1_mid, hν,
      mul_pos hα hβpos]
  linarith [mu3_lt_one_div_q1 h, hstep]

/-- `μ₄ ≤ cap` (thm:lne-cex:mu4/case4): `μ₄ = 1 + βν/L₂ < 2 ≤ cap`, since `L₂ > βν`
(as `L₂ − βν = ν·L₁ + αβ > 0`). -/
public theorem μ4_le_cap (h : Constraints α β ν) : μ4 α β ν ≤ cap α β ν := by
  have hβpos : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hα := alpha_pos h
  have hν := nu_pos h
  have hL2 := L2_pos h
  have hbnL2 : β * ν / L2 α β ν < 1 := by
    rw [div_lt_one hL2]
    simp only [L2]
    have hexp : 0 < ν * (α + ν - β) := by nlinarith [hν, h.c1_hi]
    nlinarith [hexp, mul_pos hα hβpos]
  have hcap : (2:ℝ) ≤ cap α β ν := by
    simp only [cap]
    nlinarith [mul_le_mul (h.c1_lo) (le_trans h.c1_lo h.c1_mid) (by norm_num : (0:ℝ) ≤ 2) hα.le, hν]
  simp only [μ4]
  linarith

/-- `ĉ₁ < α·β/2` (thm:lne-cex:p1). Since `ĉ₁·(ν+1)·(α+ν) = L₂` (as `ν + α·q₁ = L₂/(α+ν)`),
`L₂ < (ν+1)·α·β` (Constraint c2: `ν + α < α·β`) and `α + ν > 2`, we get
`ĉ₁·2·(ν+1) < ĉ₁·(ν+1)·(α+ν) = L₂ < (ν+1)·α·β`, hence `ĉ₁ < α·β/2`. -/
theorem chat1_lt_half_alpha_beta (h : Constraints α β ν) : chat1 α β ν < α * β / 2 := by
  have hα := alpha_pos h
  have hν := nu_pos h
  have hβpos : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hν1 : (0:ℝ) < ν + 1 := by linarith
  -- `ĉ₁·(ν+1)·(α+ν) = L₂`.
  have hchatL2 : chat1 α β ν * (ν + 1) * (α + ν) = L2 α β ν := by
    have hne : (α + ν) ≠ 0 := ne_of_gt (alpha_add_nu_pos h)
    simp only [chat1, q1, L2]; field_simp; ring
  -- `L₂ < (ν+1)·α·β`, from `ν + α < α·β`.
  have hL2ub : L2 α β ν < (ν + 1) * (α * β) := by
    simp only [L2]; nlinarith [h.c2, hν, mul_pos hν (show (0:ℝ) < α * β - α - ν by linarith [h.c2])]
  -- `α + ν > 2`, so `2·(ν+1)·ĉ₁ < (α+ν)·(ν+1)·ĉ₁ = L₂ < (ν+1)·αβ`.
  have hαν2 : (2:ℝ) < α + ν := by linarith [h.c1_lo, hν]
  have hub : chat1 α β ν * (ν + 1) * 2 < (α * β / 2) * (ν + 1) * 2 := by
    have hcpos : 0 < chat1 α β ν * (ν + 1) := mul_pos (by linarith [chat1_gt_one h]) hν1
    nlinarith [hchatL2, hL2ub, hcpos, mul_lt_mul_of_pos_left hαν2 hcpos]
  nlinarith [hub, hν1]

/-- `1/2 ≤ p₁` (thm:lne-cex:p1). Since `α·ĉ₁ > 2`, we have `√(1 + 4/(α·ĉ₁)) < √9 = 3`,
so `p₁ = 2/(1 + √…) > 2/4 = 1/2`. This is the clean form of `1/p₁ < 2`. -/
theorem p1_ge_half (h : Constraints α β ν) : (1:ℝ) / 2 ≤ p1 α β ν := by
  have hα := alpha_pos h
  have hk : 0 < α * chat1 α β ν := alpha_mul_chat1_pos h
  -- `α·ĉ₁ ≥ 2`, so `4/(α·ĉ₁) ≤ 2` and the radicand is `≤ 9`.
  have hkey : (2:ℝ) ≤ α * chat1 α β ν := by
    nlinarith [mul_nonneg (by linarith [h.c1_lo] : (0:ℝ) ≤ α - 2)
      (by linarith [chat1_gt_one h] : (0:ℝ) ≤ chat1 α β ν - 1), h.c1_lo, chat1_gt_one h]
  have h4 : 4 / (α * chat1 α β ν) ≤ 2 := by
    rw [div_le_iff₀ hk]; linarith
  have h9 : 1 + 4 / (α * chat1 α β ν) ≤ (3:ℝ) ^ 2 := by norm_num; linarith
  have hs : Real.sqrt (1 + 4 / (α * chat1 α β ν)) ≤ 3 := by
    calc Real.sqrt (1 + 4 / (α * chat1 α β ν))
        ≤ Real.sqrt ((3:ℝ) ^ 2) := Real.sqrt_le_sqrt h9
      _ = 3 := by rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
  simp only [p1]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hs, Real.sqrt_nonneg (1 + 4 / (α * chat1 α β ν))]

/-- `μ₁ ≤ cap` (thm:lne-cex:p1). `μ₁ = ĉ₁/p₁`; with `ĉ₁ < α·β/2` (`chat1_lt_half_alpha_beta`)
and `p₁ ≥ 1/2` (`p1_ge_half`), `μ₁ = ĉ₁/p₁ ≤ 2·ĉ₁ < α·β ≤ cap`. -/
public theorem μ1_le_cap (h : Constraints α β ν) : μ1 α β ν ≤ cap α β ν := by
  have hα := alpha_pos h
  have hν := nu_pos h
  have hβpos : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hp1 := p1_pos h
  have hcap : 0 < α * β + ν := by positivity
  have hchat := chat1_lt_half_alpha_beta h
  have hhalf := p1_ge_half h
  simp only [μ1, cap]
  rw [div_le_iff₀ hp1]
  -- goal: `ĉ₁ ≤ (αβ + ν)·p₁`. Since `p₁ ≥ 1/2`, RHS `≥ (αβ+ν)/2 = αβ/2 + ν/2 > ĉ₁`.
  nlinarith [mul_le_mul_of_nonneg_left hhalf hcap.le, hchat, hν]

/-- `c* ≤ cap`, since `c*` is a minimum of the `μᵢ`, each of which is at most `cap`.

This is what makes `cap` invisible to users of the main result: any `c < c*` is
automatically within the range where the `x/0 = cap` convention is sound. -/
public theorem cStar_le_cap (h : Constraints α β ν) : cStar α β ν ≤ cap α β ν := by
  unfold cStar
  exact le_trans (min_le_left _ _) (μ1_le_cap h)

end DataMktOligo.MuOpt
