module

public import DataMktOligoHard.Defs
import DataMktOligoHard.SpecialPoints
import DataMktOligoHard.Case1
import DataMktOligoHard.Case2
import DataMktOligoHard.Case3
import DataMktOligoHard.Case4

public section

namespace DataMktOligoHard

variable (α β n : ℝ)

/-- **Main reduction** (thm:pq-redn, lower bound): under Constraints c1–c4, every
nonnegative price pair has `μ(p,q) ≥ cStar := min_i μᵢ`, so no `(cStar - ε)`-NE exists.
Together with the `μ_pᵢ_qᵢ` lemmas (which show the bound is attained), this gives
`inf_{p,q} μ = cStar`. -/
theorem cStar_le_μ (h : Constraints α β n) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    cStar α β n ≤ μ α β n p q ∧ μ_at_special α β n := by
  refine ⟨?_, μ_p1_q1 h, μ_p2_q2 h, μ_p3_q3 h, μ_p4_q4 h⟩
  unfold cStar
  simp only [min_le_iff]
  by_cases hpq : p + q ≤ 1
  · have h3 := thm_3 h hp hq hpq
    simp only [min_le_iff] at h3
    tauto
  · push Not at hpq
    rcases lt_trichotomy (α * q) p with hpaq | hpaq | hpaq
    · have h1 := thm_1 h hq hpq.le hpaq
      simp only [min_le_iff] at h1
      tauto
    · have h4 := thm_4 h (hpaq.symm) hpq
      simp only [min_le_iff] at h4
      tauto
    · have h2 := thm_2 h hp hq hpaq (hpq.le)
      left ; assumption

/-- **Headline instability bound** at a near-optimal parameter choice:
for `n = 10` poor buyers and `(α, β) = (0.733157n, 0.860399n)`, Constraints c1–c4 hold
and `cStar > 1.363964`. Combined with `cStar_le_μ`, this witnesses that no
`1.363964`-approximate Nash equilibrium exists. -/
theorem cStar_specific {α β n : ℝ} (hn : n = 10)
  (hα : α = 0.733157 * n) (hβ : β = 0.860399 * n)
  : Constraints α β n ∧ 1.363964 < cStar α β n := by
  subst hn hα hβ
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
    · -- μ₂ = 1/q₂ = (n+√L₂)/(n+β)
      have hpos : (0 : ℝ) < 10 + 0.860399 * 10 := by norm_num
      have key : (1.363964 * (10 + 0.860399 * 10) - 10 : ℝ) <
          Real.sqrt (L2 (0.733157 * 10) (0.860399 * 10) 10) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num [L2]
      unfold μ2 q2
      rw [one_div_div, lt_div_iff₀ hpos]
      linarith [key]
    · -- μ₃ = (√D - L₁·n)/(2αβ)
      unfold μ3
      rw [lt_div_iff₀ (by norm_num), lt_sub_iff_add_lt, Real.lt_sqrt (by norm_num [L1])]
      norm_num [L1, L2]
    · -- μ₄ = 1 + βn/L₂ (no square root)
      norm_num [μ4, L2]

end DataMktOligoHard
