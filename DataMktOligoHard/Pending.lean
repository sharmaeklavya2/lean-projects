import DataMktOligoHard.Basic
import DataMktOligoHard.Case1
import DataMktOligoHard.Case2
import DataMktOligoHard.Case3
import DataMktOligoHard.Case4

namespace DataMktOligoHard

variable (α β n : ℝ)

/-- **Main reduction** (thm:pq-redn, lower bound): under Constraints c1–c4, every
nonnegative price pair has `μ(p,q) ≥ cStar := min_i μᵢ`, so no `(cStar - ε)`-NE exists.
Together with the `μ_pᵢ_qᵢ` lemmas (which show the bound is attained), this gives
`inf_{p,q} μ = cStar`. -/
theorem cStar_le_μ (h : Constraints α β n) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    cStar α β n ≤ μ α β n p q := by
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

end DataMktOligoHard
