import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Data-market oligopoly: inapproximability of approximate Nash equilibria
-/

namespace DataMktOligoHard

variable (α β n : ℝ)

/-! ## Closed-form expressions for revenue

The parameters `α, β` and `n` are fixed. Here `n` denotes the paper's `n_p`,
the number of *poor* buyers (the paper's total buyer count is `n_p + 1 = n + 1`).
We keep them as plain functions of `(p, q)`. -/

/-- Seller 1's revenue when poor buyers are forced to buy seller 2's dataset first.
`r₁⁻(p,q) = min(p,β) + n·min(p, max(0, 1-q))`. (thm:r-lo-hi) -/
noncomputable def r1lo (p q : ℝ) : ℝ :=
  min p β + n * min p (max 0 (1 - q))

/-- Seller 1's revenue when poor buyers are forced to buy her dataset first.
`r₁⁺(p,q) = min(p,β) + n·min(p, 1)`. (thm:r-lo-hi) -/
noncomputable def r1hi (p _q : ℝ) : ℝ :=
  min p β + n * min p 1

/-- Seller 2's revenue when poor buyers are forced to buy seller 1's dataset first.
`r₂⁻(p,q) = n·min(q, max(0, 1-p))`. (thm:r-lo-hi) -/
noncomputable def r2lo (p q : ℝ) : ℝ :=
  n * min q (max 0 (1 - p))

/-- Seller 2's revenue when poor buyers are forced to buy her dataset first.
`r₂⁺(p,q) = n·min(q, 1)`. (thm:r-lo-hi) -/
noncomputable def r2hi (_p q : ℝ) : ℝ :=
  n * min q 1

/-! The valid-revenue set `V(p,q)`:

* If `p + q ≤ 1`: `{(r₁⁻, r₂⁻)}`.
* If `p < α·q`  : `{(r₁⁺, r₂⁻)}`.
* If `p > α·q`  : `{(r₁⁻, r₂⁺)}`.
* If `p = α·q` and `p + q > 1`: the segment with `r₁⁻ ≤ r₁ ≤ r₁⁺`,
  `r₂⁻ ≤ r₂ ≤ r₂⁺`, and `r₁ + r₂ = min(p,β) + n`.

`V` is a singleton _except_ on the knife-edge `p = α·q ∧ p + q > 1`. -/

open Classical in
/-- The set of valid seller-revenue pairs `(r₁, r₂)` at prices `(p, q)`. -/
noncomputable def V (p q : ℝ) : Set (ℝ × ℝ) :=
  if p + q ≤ 1 then {(r1lo β n p q, r2lo n p q)}
  else if p < α * q then {(r1hi β n p q, r2lo n p q)}
  else if p > α * q then {(r1lo β n p q, r2hi n p q)}
  else -- p = α·q and p + q > 1: the interpolating segment
    {rr | r1lo β n p q ≤ rr.1 ∧ rr.1 ≤ r1hi β n p q ∧
          r2lo n p q ≤ rr.2 ∧ rr.2 ≤ r2hi n p q ∧
          rr.1 + rr.2 = min p β + n}

/-! Best-response revenues (thm:rstar) -/

/-- Seller 1's best-response revenue given `q`:
`r₁*(q) = max(β + n·max(0,1-q), min(β, α·q) + n·min(1, α·q))`. -/
noncomputable def r1star (q : ℝ) : ℝ :=
  max (β + n * max 0 (1 - q)) (min β (α * q) + n * min 1 (α * q))

/-- Seller 2's best-response revenue given `p`:
`r₂*(p) = n·max(1 - p, min(1, p/α))`. -/
noncomputable def r2star (p : ℝ) : ℝ :=
  n * max (1 - p) (min 1 (p / α))

/-! ### The instability ratio `μ`

`μ(p,q) := inf_{(r₁,r₂) ∈ V} max(r₁*/r₁, r₂*/r₂)` with the convention `x/0 = ∞`
(a seller earning `0` against a positive best response is maximally unstable).
Since `ℝ` has no `∞` in Lean, we replace it by a finite cap `cap`.
This keeps `μ` in `ℝ`, keeps the "convert the NE problem into a 2-D optimization of
`μ`" narrative explicit, and is sound for the lower bound: we only ever compare `μ`
against values `< cap`, and `min(cap, μ) ≥ c ↔ μ ≥ c` whenever `c < cap`. -/

/-- Finite stand-in for `∞` in the `x/0 = ∞` convention. Any constant `≥ min_i μᵢ`
works; `2` suffices because `min_i μᵢ ≤ μ₄ < 2` holds under Constraint c1
(`β < α + n` gives `β(n - α) < n(n + α)`). -/
noncomputable def cap : ℝ := 2

/-- The best-response ratio `r*/r`, with `r*/0` read as `cap`
(the `x/0 = ∞` convention, made finite). -/
noncomputable def ratio (rstar r : ℝ) : ℝ := if r = 0 then cap else rstar / r

/-- The instability ratio `μ(p,q) = inf_{(r₁,r₂) ∈ V} max(r₁*/r₁, r₂*/r₂)`
(revenue.tex), with `x/0` read as `cap`. `(p,q)` is a `c`-NE iff `μ(p,q) ≤ c`
(for `c < cap`); minimizing `μ` over prices is the core optimization problem. -/
noncomputable def μ (p q : ℝ) : ℝ :=
  sInf {m : ℝ | ∃ r1 r2, (r1, r2) ∈ V α β n p q ∧
                m = max (ratio (r1star α β n q) r1) (ratio (r2star α n p) r2)}

/-! ## Inapproximability -/

/-- The four constraints on α, β, and n (items c1–c4). -/
structure Constraints (α β n : ℝ) : Prop where
  /-- c1: `2 ≤ α ≤ β < α + n`. -/
  c1_lo : 2 ≤ α
  c1_mid : α ≤ β
  c1_hi : β < α + n
  /-- c2: `α + n < α·β`. -/
  c2 : α + n < α * β
  /-- c3: `(α + n)³ > β·(α·β + 2n·(α + n))`. -/
  c3 : (α + n) ^ 3 > β * (α * β + 2 * n * (α + n))
  /-- c4: `α·(β + n)² > β·n²`. -/
  c4 : α * (β + n) ^ 2 > β * n ^ 2

/-- `L₁ := α + n - β`. Positive by Constraint c1 (`β < α + n`). -/
noncomputable def L1 : ℝ := α + n - β

/-- `L₂ := n² + αn + αβ`. Positive (all terms are, since `n > 0`). -/
noncomputable def L2 : ℝ := n ^ 2 + α * n + α * β

/-! The four candidate points. Auxiliary `q₁` and `ĉ₁` are shared. -/

/-- `q₁ := β / (α + n)`. -/
noncomputable def q1 : ℝ := β / (α + n)

/-- `ĉ₁ := (n + α·q₁) / (n + 1)`. -/
noncomputable def chat1 : ℝ := (n + α * q1 α β n) / (n + 1)

/-- `p₁ := 2 / (1 + √(1 + 4/(α·ĉ₁)))`. -/
noncomputable def p1 : ℝ := 2 / (1 + Real.sqrt (1 + 4 / (α * chat1 α β n)))

/-- `μ₁ := ĉ₁ / p₁`. -/
noncomputable def μ1 : ℝ := chat1 α β n / p1 α β n

/-- `p₂ := β`. -/
noncomputable def p2 : ℝ := β

/-- `q₂ := (n + β) / (n + √L₂)`. -/
noncomputable def q2 : ℝ := (n + β) / (n + Real.sqrt (L2 α β n))

/-- `μ₂ := 1 / q₂`. -/
noncomputable def μ2 : ℝ := 1 / q2 α β n

/-- `μ₃ := (√(n²L₁² + 4αβL₂) - L₁n) / (2αβ)`. -/
noncomputable def μ3 : ℝ :=
  (Real.sqrt (n ^ 2 * (L1 α β n) ^ 2 + 4 * α * β * L2 α β n) - L1 α β n * n) / (2 * α * β)

/-- `p₃ := α·q₁·μ₃`. -/
noncomputable def p3 : ℝ := α * q1 α β n * μ3 α β n

/-- `q₃ := q₁`. -/
noncomputable def q3 : ℝ := q1 α β n

/-- `q₄ := q₁`. -/
noncomputable def q4 : ℝ := q1 α β n

/-- `p₄ := α·q₁`. -/
noncomputable def p4 : ℝ := α * q1 α β n

/-- `μ₄ := 1 + βn / L₂`. -/
noncomputable def μ4 : ℝ := 1 + β * n / L2 α β n

/-- The set of four candidate points `P = {(pᵢ, qᵢ)}`. -/
noncomputable def candidatePoints : Finset (ℝ × ℝ) :=
  {(p1 α β n, q1 α β n), (p2 β, q2 α β n), (p3 α β n, q3 α β n), (p4 α β n, q4 α β n)}

/-- The inapproximability constant `c* := min(μ₁,μ₂,μ₃,μ₄)`. The main result
(`cStar_le_μ`, in `Pending`) is that `μ(p,q) ≥ cStar` for all nonnegative `p, q`. -/
noncomputable def cStar : ℝ := min (μ1 α β n) (min (μ2 α β n) (min (μ3 α β n) (μ4 α β n)))

end DataMktOligoHard
