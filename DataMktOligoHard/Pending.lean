import DataMktOligoHard.Basic

/-!
# Pending results (temporary parking file)

These results belong to subsections not yet formalized. They will move to their
own files once those subsections are done:

* `μ_p4_q4` → the case-4 (knife-edge `p = α·q`) file.
* `cStar_le_μ` → the final reduction file, which will import all four case files.

Both are `sorry` for now.
-/

namespace DataMktOligoHard

variable (α β n : ℝ)

/-- `μ(p₄, q₄) = μ₄` (deferred to case 4, since `p₄ = α·q₄` is on the knife-edge). -/
theorem μ_p4_q4 (h : Constraints α β n) :
    μ α β n (p4 α β n) (q4 α β n) = μ4 α β n := by
  sorry

/-- **Main reduction** (thm:pq-redn, lower bound): under Constraints c1–c4, every
nonnegative price pair has `μ(p,q) ≥ cStar := min_i μᵢ`, so no `(cStar - ε)`-NE exists.
Together with the `μ_pᵢ_qᵢ` lemmas (which show the bound is attained), this gives
`inf_{p,q} μ = cStar`. -/
theorem cStar_le_μ (h : Constraints α β n) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    cStar α β n ≤ μ α β n p q := by
  sorry

end DataMktOligoHard
