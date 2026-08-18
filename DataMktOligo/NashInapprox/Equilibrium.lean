module

public import DataMktOligo.NashInapprox.Instance
public import DataMktOligo.LinDataMkt.Revenue
public import DataMktOligo.MuOpt.Defs

/-!
# The bridge: market revenue vs. the closed forms of `MuOpt`

`DataMktOligo.MuOpt` *stipulates* closed forms for the sellers' revenues, their best
responses, and the instability ratio `μ`. This file states that those stipulations are
correct: they agree with what the market of `DataMktOligo.LinDataMkt` actually produces for
the instance of `DataMktOligo.NashInapprox.Instance`.

Everything here is stated but not yet proved.

## Main results

* `V_nonempty`: some revenue vector is attainable, i.e. buyers do have demands.
* `mem_V_iff_mem_muOptV`: the market's valid-revenue set is `MuOpt.V`.
* `bestResponseRevenue_seller0`, `bestResponseRevenue_seller1`: the sellers' best-response
  revenues are `MuOpt.r1star` and `MuOpt.r2star`.
* `not_isApproxNE_of_lt_μ`: if `μ(p,q)` exceeds `c`, then `(p,q)` is not a `c`-approximate
  Nash equilibrium. This is the direction the main result needs.

## The `cap` convention

`MuOpt.μ` uses a finite `cap` in place of `∞` for the `x/0` convention, whereas
`LinDataMkt.IsApproxNE` is stated multiplicatively and never divides. The two agree only
for `c < cap`, which is why `not_isApproxNE_of_lt_μ` carries that hypothesis; it is the
same soundness restriction already documented in `DataMktOligo.MuOpt.Cap`.
-/

@[expose] public section

namespace DataMktOligo.NashInapprox

open DataMktOligo.MuOpt (Constraints cap μ r1star r2star)

variable {α β ν : ℝ}

/-! ### Demands exist -/

/-- Every buyer has at least one demand at nonnegative prices, so the set of valid revenue
vectors is nonempty.

This matters for the `μ` comparison: `LinDataMkt.IsApproxNE` quantifies over `r ∈ V`, so an
empty `V` would make every price vector vacuously an equilibrium, while `MuOpt.μ` is an
`sInf`, which returns `0` on the empty set. A witness comes from
`LinDataMkt.isDemand_of_isGreedy`. -/
theorem V_nonempty (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (LinDataMkt.V (inst h) ![p, q]).Nonempty := by
  sorry

/-! ### The valid-revenue set -/

/-- **The closed form for `V` is correct.** A pair of seller revenues is attainable in the
market exactly when it lies in `MuOpt.V`.

Stated componentwise rather than as an equality of sets: the market's revenue vectors live
in `Fin 2 → ℝ` and `MuOpt.V`'s live in `ℝ × ℝ`, and every downstream use has a concrete `r`
in hand and wants its two components. -/
theorem mem_V_iff_mem_muOptV (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {r : Fin 2 → ℝ} :
    r ∈ LinDataMkt.V (inst h) ![p, q] ↔ (r 0, r 1) ∈ DataMktOligo.MuOpt.V α β ν p q := by
  sorry

/-! ### Best-response revenues -/

/-- **The closed form for `r₁*` is correct**: seller `0`'s best-response revenue, given that
seller `1` charges `q`, is `MuOpt.r1star`. Note it does not depend on seller `0`'s own
current price `p`. -/
theorem bestResponseRevenue_seller0 (h : Constraints α β ν) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    LinDataMkt.bestResponseRevenue (inst h) ![p, q] 0 = r1star α β ν q := by
  sorry

/-- **The closed form for `r₂*` is correct**: seller `1`'s best-response revenue, given that
seller `0` charges `p`, is `MuOpt.r2star`. -/
theorem bestResponseRevenue_seller1 (h : Constraints α β ν) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    LinDataMkt.bestResponseRevenue (inst h) ![p, q] 1 = r2star α ν p := by
  sorry

/-! ### `μ` bounds approximate equilibria -/

/-- **The bridge to the optimization problem.** If the instability ratio at `(p,q)` exceeds
`c`, then `(p,q)` is not a `c`-approximate Nash equilibrium.

Only this direction is needed, and only this direction is sound under the `cap` convention;
see the module docstring. -/
theorem not_isApproxNE_of_lt_μ (h : Constraints α β ν) {p q c : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hcap : c < cap α β ν) (hc : c < μ α β ν p q) :
    ¬ LinDataMkt.IsApproxNE (inst h) ![p, q] c := by
  sorry

end DataMktOligo.NashInapprox
