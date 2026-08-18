module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# Data-market oligopoly: inapproximability of approximate Nash equilibria
-/

@[expose] public section

namespace DataMktOligoHard

variable (α β ν : ℝ)

/-! ## Closed-form expressions for revenue

The parameters `α, β` and `ν` are fixed. Here `ν` denotes the the number of *poor* buyers.
We keep them as plain functions of `(p, q)`. -/

/-- Seller 1's revenue when poor buyers are forced to buy seller 2's dataset first.
`r₁⁻(p,q) = min(p,β) + ν·min(p, max(0, 1-q))`. (thm:r-lo-hi) -/
noncomputable def r1lo (p q : ℝ) : ℝ :=
  min p β + ν * min p (max 0 (1 - q))

/-- Seller 1's revenue when poor buyers are forced to buy her dataset first.
`r₁⁺(p,q) = min(p,β) + ν·min(p, 1)`. (thm:r-lo-hi) -/
noncomputable def r1hi (p _q : ℝ) : ℝ :=
  min p β + ν * min p 1

/-- Seller 2's revenue when poor buyers are forced to buy seller 1's dataset first.
`r₂⁻(p,q) = ν·min(q, max(0, 1-p))`. (thm:r-lo-hi) -/
noncomputable def r2lo (p q : ℝ) : ℝ :=
  ν * min q (max 0 (1 - p))

/-- Seller 2's revenue when poor buyers are forced to buy her dataset first.
`r₂⁺(p,q) = ν·min(q, 1)`. (thm:r-lo-hi) -/
noncomputable def r2hi (_p q : ℝ) : ℝ :=
  ν * min q 1

/-! The valid-revenue set `V(p,q)`:

* If `p + q ≤ 1`: `{(r₁⁻, r₂⁻)}`.
* If `p < α·q`  : `{(r₁⁺, r₂⁻)}`.
* If `p > α·q`  : `{(r₁⁻, r₂⁺)}`.
* If `p = α·q` and `p + q > 1`: the segment with `r₁⁻ ≤ r₁ ≤ r₁⁺`,
  `r₂⁻ ≤ r₂ ≤ r₂⁺`, and `r₁ + r₂ = min(p,β) + ν`.

`V` is a singleton _except_ on the knife-edge `p = α·q ∧ p + q > 1`. -/

open Classical in
/-- The set of valid seller-revenue pairs `(r₁, r₂)` at prices `(p, q)`. -/
noncomputable def V (p q : ℝ) : Set (ℝ × ℝ) :=
  if p + q ≤ 1 then {(r1lo β ν p q, r2lo ν p q)}
  else if p < α * q then {(r1hi β ν p q, r2lo ν p q)}
  else if p > α * q then {(r1lo β ν p q, r2hi ν p q)}
  else -- p = α·q and p + q > 1: the interpolating segment
    {rr | r1lo β ν p q ≤ rr.1 ∧ rr.1 ≤ r1hi β ν p q ∧
          r2lo ν p q ≤ rr.2 ∧ rr.2 ≤ r2hi ν p q ∧
          rr.1 + rr.2 = min p β + ν}

/-! Best-response revenues (thm:rstar) -/

/-- Seller 1's best-response revenue given `q`:
`r₁*(q) = max(β + ν·max(0,1-q), min(β, α·q) + ν·min(1, α·q))`. -/
noncomputable def r1star (q : ℝ) : ℝ :=
  max (β + ν * max 0 (1 - q)) (min β (α * q) + ν * min 1 (α * q))

/-- Seller 2's best-response revenue given `p`:
`r₂*(p) = ν·max(1 - p, min(1, p/α))`. -/
noncomputable def r2star (p : ℝ) : ℝ :=
  ν * max (1 - p) (min 1 (p / α))
  -- α > 0 (see `Constraints.c1_lo`), so division is well-defined.

/-! ### The instability ratio `μ`

`μ(p,q) := inf_{(r₁,r₂) ∈ V} max(r₁*/r₁, r₂*/r₂)` with the convention `x/0 = ∞`
(a seller earning `0` against a positive best response is maximally unstable).
Since `ℝ` has no `∞` in Lean, we replace it by a finite cap `cap`.
This keeps `μ` in `ℝ`, keeps the "convert the NE problem into a 2-D optimization of
`μ`" narrative explicit, and is sound for the lower bound: we only ever compare `μ`
against values `< cap`; see `Cap.lean`. -/

/-- The best-response ratio `r*/r`, with `r*/0` read as `fallback`
(the `x/0 = ∞` convention, made finite by substituting `fallback` for `∞`). -/
noncomputable def ratio (fallback rstar r : ℝ) : ℝ :=
  if r = 0 then fallback else rstar / r

/-- Finite stand-in for `∞` in the `x/0 = ∞` convention, used as `ratio`'s
`fallback` inside `μ`. Any value `≥ min_i μᵢ` that stays above every intermediate
`μ(p,q) ≥ X` bound in the case analysis works; `α·β + ν` gives ample headroom
(each `μᵢ < α·β` under the constraints, e.g. `μ₁ = ĉ₁/p₁ ≤ 2·ĉ₁ < α·β`, and `ν > 0`).
It is deliberately a function of `α, β, ν` so the *value* can be enlarged later
(e.g. to `ν²` or `(α+ν)(β+ν)`) without touching any call site. -/
noncomputable def cap : ℝ := α * β + ν

/-- The instability ratio `μ(p,q) = inf_{(r₁,r₂) ∈ V} max(r₁*/r₁, r₂*/r₂)`
(revenue.tex), with `x/0` read as `cap`. `(p,q)` is a `c`-NE iff `μ(p,q) ≤ c`
(for `c < cap`); minimizing `μ` over prices is the core optimization problem. -/
noncomputable def μ (p q : ℝ) : ℝ :=
  sInf {m : ℝ | ∃ r1 r2, (r1, r2) ∈ V α β ν p q ∧
                m = max (ratio (cap α β ν) (r1star α β ν q) r1)
                        (ratio (cap α β ν) (r2star α ν p) r2)}

/-! ## Inapproximability -/

/-- The four constraints on α, β, and ν (items c1–c4). -/
structure Constraints (α β ν : ℝ) : Prop where
  /-- c1: `2 ≤ α ≤ β < α + ν`. -/
  c1_lo : 2 ≤ α
  c1_mid : α ≤ β
  c1_hi : β < α + ν
  /-- c2: `α + ν < α·β`. -/
  c2 : α + ν < α * β
  /-- c3: `(α + ν)³ > β·(α·β + 2ν·(α + ν))`. -/
  c3 : (α + ν) ^ 3 > β * (α * β + 2 * ν * (α + ν))
  /-- c4: `α·(β + ν)² > β·ν²`. -/
  c4 : α * (β + ν) ^ 2 > β * ν ^ 2

/-- `L₁ := α + ν - β`. Positive by Constraint c1 (`β < α + ν`). -/
noncomputable def L1 : ℝ := α + ν - β

/-- `L₂ := ν² + αν + αβ`. Positive (all terms are, since `ν > 0`). -/
noncomputable def L2 : ℝ := ν ^ 2 + α * ν + α * β

/-! The four candidate points. Auxiliary `q₁` and `ĉ₁` are shared.
In the definition of `pᵢ`, `qᵢ`, `μᵢ`, division is well-defined since
each numerator and denominator is positive.
-/

/-- `q₁ := β / (α + ν)`. -/
noncomputable def q1 : ℝ := β / (α + ν)

/-- `ĉ₁ := (ν + α·q₁) / (ν + 1)`. -/
noncomputable def chat1 : ℝ := (ν + α * q1 α β ν) / (ν + 1)

/-- `p₁ := 2 / (1 + √(1 + 4/(α·ĉ₁)))`. -/
noncomputable def p1 : ℝ := 2 / (1 + Real.sqrt (1 + 4 / (α * chat1 α β ν)))

/-- `μ₁ := ĉ₁ / p₁`. -/
noncomputable def μ1 : ℝ := chat1 α β ν / p1 α β ν

/-- `p₂ := β`. -/
noncomputable def p2 : ℝ := β

/-- `q₂ := (ν + β) / (ν + √L₂)`. -/
noncomputable def q2 : ℝ := (ν + β) / (ν + Real.sqrt (L2 α β ν))

/-- `μ₂ := 1 / q₂`. -/
noncomputable def μ2 : ℝ := 1 / q2 α β ν

/-- `μ₃ := (√(ν²L₁² + 4αβL₂) - L₁ν) / (2αβ)`. -/
noncomputable def μ3 : ℝ :=
  (Real.sqrt (ν ^ 2 * (L1 α β ν) ^ 2 + 4 * α * β * L2 α β ν) - L1 α β ν * ν) / (2 * α * β)

/-- `p₃ := α·q₁·μ₃`. -/
noncomputable def p3 : ℝ := α * q1 α β ν * μ3 α β ν

/-- `q₃ := q₁`. -/
noncomputable def q3 : ℝ := q1 α β ν

/-- `q₄ := q₁`. -/
noncomputable def q4 : ℝ := q1 α β ν

/-- `p₄ := α·q₁`. -/
noncomputable def p4 : ℝ := α * q1 α β ν

/-- `μ₄ := 1 + βν / L₂`. -/
noncomputable def μ4 : ℝ := 1 + β * ν / L2 α β ν

/-- The set of four candidate points `P = {(pᵢ, qᵢ)}`. -/
noncomputable def candidatePoints : Finset (ℝ × ℝ) :=
  {(p1 α β ν, q1 α β ν), (p2 β, q2 α β ν), (p3 α β ν, q3 α β ν), (p4 α β ν, q4 α β ν)}

/-- The inapproximability constant `c* := min(μ₁,μ₂,μ₃,μ₄)`. The main result
(`cStar_le_μ`, in `Pending`) is that `μ(p,q) ≥ cStar` for all nonnegative `p, q`. -/
noncomputable def cStar : ℝ := min (μ1 α β ν) (min (μ2 α β ν) (min (μ3 α β ν) (μ4 α β ν)))

def μ_at_special : Prop :=
  μ α β ν (p1 α β ν) (q1 α β ν) = μ1 α β ν
  ∧ μ α β ν (p2 β) (q2 α β ν) = μ2 α β ν
  ∧ μ α β ν (p3 α β ν) (q3 α β ν) = μ3 α β ν
  ∧ μ α β ν (p4 α β ν) (q4 α β ν) = μ4 α β ν

end DataMktOligoHard
