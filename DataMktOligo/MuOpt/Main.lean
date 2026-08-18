module

public import DataMktOligo.MuOpt.Revenue
public import DataMktOligo.MuOpt.ParamConstraints
public import DataMktOligo.MuOpt.Constants
import DataMktOligo.MuOpt.SpecialPointsProps
import DataMktOligo.MuOpt.Case1
import DataMktOligo.MuOpt.Case2
import DataMktOligo.MuOpt.Case3
import DataMktOligo.MuOpt.Case4

public section

namespace DataMktOligo.MuOpt

variable (α β ν : ℝ)

public def μ_at_special : Prop :=
  μ α β ν (p1 α β ν) (q1 α β ν) = μ1 α β ν
  ∧ μ α β ν (p2 β) (q2 α β ν) = μ2 α β ν
  ∧ μ α β ν (p3 α β ν) (q3 α β ν) = μ3 α β ν
  ∧ μ α β ν (p4 α β ν) (q4 α β ν) = μ4 α β ν

/-- **Main reduction** (thm:pq-redn, lower bound): under Constraints c1–c4, every
nonnegative price pair has `μ(p,q) ≥ cStar := min_i μᵢ`, so no `(cStar - ε)`-NE exists.
Together with the `μ_pᵢ_qᵢ` lemmas (which show the bound is attained), this gives
`inf_{p,q} μ = cStar`. -/
public theorem cStar_le_μ (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    cStar α β ν ≤ μ α β ν p q ∧ μ_at_special α β ν := by
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

end DataMktOligo.MuOpt
