module

public import DataMktOligo.MuOpt.ParamConstraints
public import DataMktOligo.MuOpt.Constants

namespace DataMktOligo.MuOpt

/-- Evaluating cStar for a particular (α, β, ν). -/
public theorem cStar_specific {α β ν : ℝ} (hν : ν = 10)
  (hα : α = 0.733157 * ν) (hβ : β = 0.860399 * ν)
  : Constraints α β ν ∧ 1.363964 < cStar α β ν := by
  subst hν hα hβ
  constructor
  · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · unfold cStar
    simp only [lt_min_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- μ₁ = ĉ₁·(1+√S)/2,  S = 1 + 4/(α·ĉ₁); √S multiplies the symbolic ĉ₁, so
      -- under-approximate both factors by rationals and let `nlinarith` combine them.
      have hchat : (1.23996768 : ℝ) < chat1 (0.733157 * 10) (0.860399 * 10) 10 := by
        norm_num [chat1, q1]
      have hs : (1.19999998 : ℝ) <
          Real.sqrt (1 + 4 / ((0.733157 * 10) * chat1 (0.733157 * 10) (0.860399 * 10) 10)) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num [chat1, q1]
      unfold μ1 p1
      rw [div_div_eq_mul_div, lt_div_iff₀ (by norm_num)]
      nlinarith [hs, hchat, Real.sqrt_nonneg
        (1 + 4 / ((0.733157 * 10) * chat1 (0.733157 * 10) (0.860399 * 10) 10))]
    · -- μ₂ = 1/q₂ = (ν+√L₂)/(ν+β)
      have hpos : (0 : ℝ) < 10 + 0.860399 * 10 := by norm_num
      have key : (1.363964 * (10 + 0.860399 * 10) - 10 : ℝ) <
          Real.sqrt (L2 (0.733157 * 10) (0.860399 * 10) 10) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num [L2]
      unfold μ2 q2
      rw [one_div_div, lt_div_iff₀ hpos]
      linarith [key]
    · -- μ₃ = (√D - L₁·ν)/(2αβ)
      unfold μ3
      rw [lt_div_iff₀ (by norm_num), lt_sub_iff_add_lt, Real.lt_sqrt (by norm_num [L1])]
      norm_num [L1, L2]
    · -- μ₄ = 1 + βν/L₂ (no square root)
      norm_num [μ4, L2]

end DataMktOligo.MuOpt
