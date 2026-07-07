import DataMktOligoHard.Basic
import DataMktOligoHard.SpecialPoints
import Mathlib.Tactic.LinearCombination

/-!
# Case 4: the knife-edge `p = α·q` and `p + q > 1` (case4.tex)

On this region `V(p,q)` is a *segment*, not a singleton, so `μ` is a genuine
infimum. We reuse `Basic`'s revenue bounds `r1lo/r1hi/r2lo/r2hi` (the paper's
`r₁⁻,r₁⁺,r₂⁻,r₂⁺`) with the *same* `(p,q)` parameters, and only add:

* `sSum`, `d`: the sellers' total revenue and the common gap `r₁⁺-r₁⁻ = r₂⁺-r₂⁻`,
  generalized to all of `p+q ≥ 1` (revenue.tex observation);
* `r1c/r2c`: the segment's revenues parametrized by `z ∈ [0,1]`;
* `μz`: the paper's `μ(q,z)`, a reparametrization of `Basic.μ α β n (α·q) q`;
* `zhat/zstar`: the minimizing `z`.

## Status: definitions + `sorry`-stubbed statements (planning pass).
-/

namespace DataMktOligoHard

/-! ## Total revenue and gap on `p + q ≥ 1` (revenue.tex observation) -/

/-- Paper `s(q)`, generalized: the sellers' total revenue `min(p,β) + n` on
`p+q ≥ 1`. By the revenue.tex observation, `r₁⁻+r₂⁺ = r₁⁺+r₂⁻ = s`. -/
noncomputable def sSum (β n p : ℝ) : ℝ := min p β + n

/-- Paper `d(q)`, generalized: the common gap `r₁⁺-r₁⁻ = r₂⁺-r₂⁻`. -/
noncomputable def d (β n p q : ℝ) : ℝ := r1hi β n p q - r1lo β n p q

/-! ## The segment, parametrized by `z ∈ [0,1]` -/

/-- Seller 1's revenue `r₁(q,z) = r₁⁻ + z·d = (1-z)r₁⁻ + z·r₁⁺`. -/
noncomputable def r1c (β n p q z : ℝ) : ℝ := r1lo β n p q + z * d β n p q

/-- Seller 2's revenue `r₂(q,z) = r₂⁺ - z·d = z·r₂⁻ + (1-z)r₂⁺`. -/
noncomputable def r2c (β n p q z : ℝ) : ℝ := r2hi n p q - z * d β n p q

/-- Paper's `μ(q,z) = max(r₁*(q)/r₁(q,z), r₂*(p)/r₂(q,z))`, using the `cap`
convention for `·/0`. On the knife-edge this is `Basic.μ α β n p q` restricted
to the point of the segment indexed by `z`. -/
noncomputable def μz (α β n p q z : ℝ) : ℝ :=
  max (ratio (r1star α β n q) (r1c β n p q z))
      (ratio (r2star α n p) (r2c β n p q z))

/-- Paper `ẑ(q)`, the `z` where the two ratio curves cross. On the knife-edge
`p = α·q`, so we take `q` alone as the argument. -/
noncomputable def zhat (α β n q : ℝ) : ℝ :=
  r2star α n (α * q) * (r1star α β n q - r1lo β n (α * q) q)
    / ((r1star α β n q + r2star α n (α * q)) * d β n (α * q) q)

/-- Paper `z*(q) = min(1, ẑ(q))`, the `z` minimizing `μ(q,z)`. -/
noncomputable def zstar (α β n q : ℝ) : ℝ := min 1 (zhat α β n q)

/-! ## Statements to prove -/

variable {α β n : ℝ}

/-- **Observation** (revenue.tex): on `p+q ≥ 1`, `r₁⁻ + r₂⁺ = s`. -/
theorem r1lo_add_r2hi {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 1 ≤ p + q) :
    r1lo β n p q + r2hi n p q = sSum β n p := by
  sorry

/-- **Observation** (revenue.tex): on `p+q ≥ 1`, `r₁⁺ + r₂⁻ = s`. -/
theorem r1hi_add_r2lo {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 1 ≤ p + q) :
    r1hi β n p q + r2lo n p q = sSum β n p := by
  sorry

/-- **Observation** (case4.tex l.40): `d(p,q) > 0` on `p+q > 1` (with `0 < p`,
`0 < n`). The `p=0,q>1` corner has `d=0`, hence the `0 < p` hypothesis. -/
theorem d_pos (hn : 0 < n) {p q : ℝ} (hp : 0 < p) (hpq : 1 < p + q) :
    0 < d β n p q := by
  sorry

/-- **Observation** (case4.tex l.6): on the knife-edge, `p + q > 1` with
`p = α·q` gives `q > 1/(α+1)`. -/
theorem q_lb (h : Constraints α β n) {q : ℝ} (hpq : 1 < α * q + q) :
    1 / (α + 1) < q := by
  sorry

/-- **Bridge**: on the knife-edge, `Basic.V α β n p q` is the image of `[0,1]`
under `z ↦ (r₁(q,z), r₂(q,z))`, so `Basic.μ = ⨅ z ∈ [0,1], μz`.
*(Provisional — representation of the `z`-machinery still under discussion.)* -/
theorem μ_eq_inf_z (h : Constraints α β n) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpaq : p = α * q) (hpq1 : 1 < p + q) :
    μ α β n p q = sInf (Set.image (μz α β n p q) (Set.Icc 0 1)) := by
  sorry

/-- **thm:4.1** (closed form of the infimum over `z`). *(Provisional.)* -/
theorem thm_4_1 (h : Constraints α β n) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpaq : p = α * q) (hpq1 : 1 < p + q) :
    sInf (Set.image (μz α β n p q) (Set.Icc 0 1))
      = max ((r1star α β n q + r2star α n p) / sSum β n p)
            (r1star α β n q / r1hi β n p q) := by
  sorry

/-- **thm:mu4**: at the special point `(p₄,q₄) = (α·q₁, q₁)`, the case-4 value is
`μ₄`. *(Provisional.)* -/
theorem thm_mu4 (h : Constraints α β n) :
    sInf (Set.image (μz α β n (p4 α β n) (q1 α β n)) (Set.Icc 0 1)) = μ4 α β n := by
  sorry

/-- **thm:4.2** (the case-4 lower bound): on the knife-edge with `p+q>1`,
`inf_z μ(q,z) ≥ min(μ₂, μ₄)`. *(Provisional.)* -/
theorem thm_4_2 (h : Constraints α β n) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpaq : p = α * q) (hpq1 : 1 < p + q) :
    min (μ2 α β n) (μ4 α β n)
      ≤ sInf (Set.image (μz α β n p q) (Set.Icc 0 1)) := by
  sorry

/-- **thm:4** (paper-facing, `z`-free — same shape as `thm_2`/`thm_3`): on the
knife-edge `p = α·q` with `p + q > 1` (and `0 ≤ p, q`), `μ(p,q) ≥ min(μ₂,μ₄)`.
The `min cap` handles the `x/0` corners of the `cap` convention; downstream
`cStar ≤ cap` recovers `cStar ≤ μ`. Proved from `thm_4_2` via `μ_eq_inf_z`. -/
theorem thm_4 (h : Constraints α β n) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpaq : p = α * q) (hpq1 : 1 < p + q) :
    min cap (min (μ2 α β n) (μ4 α β n)) ≤ μ α β n p q := by
  sorry

end DataMktOligoHard
