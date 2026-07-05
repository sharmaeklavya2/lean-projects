import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

-- Written by Claude. Unreviewed by human.

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

/-! ### Stability

`(p,q)` is a `c`-NE iff no seller can improve her revenue by more than a factor
of `c`, for *every* valid revenue split. Stated multiplicatively (division-free)
to correctly handle `rⱼ = 0`. (revenue.tex, lines 72–73.) -/

/-- `(p, q)` is a `c`-approximate Nash equilibrium. -/
def IsCNE (c p q : ℝ) : Prop :=
  ∀ r1 r2, (r1, r2) ∈ V α β n p q → r1star α β n q ≤ c * r1 ∧ r2star α n p ≤ c * r2

/-- The instability ratio `μ(p,q) = inf { c ≥ 0 | (p,q) is a c-NE }`.

At the four candidate points revenues are positive, so this agrees with the
paper's `inf max(r₁*/r₁, r₂*/r₂)`. -/
noncomputable def μ (p q : ℝ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ IsCNE α β n c p q}

/-! ## Section: Inapproximability (inapprox.tex)

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

/-- `q₂ := (n + β) / (√(n² + α·(n + β)) + n)`. -/
noncomputable def q2 : ℝ := (n + β) / (Real.sqrt (n ^ 2 + α * (n + β)) + n)

/-- `μ₂ := 1 / q₂`. -/
noncomputable def μ2 : ℝ := 1 / q2 α β n

/-- `μ₃ := (√((1 - (β-α)/n)² + 4(αβ/n²)(1 + α/n + αβ/n²)) - (1 - (β-α)/n)) / (2αβ/n²)`. -/
noncomputable def μ3 : ℝ :=
  let A := 1 - (β - α) / n
  let B := α * β / n ^ 2
  (Real.sqrt (A ^ 2 + 4 * B * (1 + α / n + B)) - A) / (2 * B)

/-- `p₃ := α·q₁·μ₃`. -/
noncomputable def p3 : ℝ := α * q1 α β n * μ3 α β n

/-- `q₃ := q₁`. -/
noncomputable def q3 : ℝ := q1 α β n

/-- `q₄ := q₁`. -/
noncomputable def q4 : ℝ := q1 α β n

/-- `p₄ := α·q₁`. -/
noncomputable def p4 : ℝ := α * q1 α β n

/-- `μ₄ := 1 + βn / (n² + nα + αβ)`. -/
noncomputable def μ4 : ℝ := 1 + β * n / (n ^ 2 + n * α + α * β)

/-- The set of four candidate points `P = {(pᵢ, qᵢ)}`. -/
noncomputable def candidatePoints : Finset (ℝ × ℝ) :=
  {(p1 α β n, q1 α β n), (p2 β, q2 α β n), (p3 α β n, q3 α β n), (p4 α β n, q4 α β n)}

/-! ### Main reduction lemma (thm:pq-redn)

Under the constraints, the infimum of `μ` over all prices collapses to the minimum
of `μ` over the four candidate points, and `μ(pᵢ, qᵢ) = μᵢ`. -/

/-- `μ(pᵢ, qᵢ) = μᵢ` for the four candidate points. -/
theorem μ_p1_q1 (h : Constraints α β n) :
    μ α β n (p1 α β n) (q1 α β n) = μ1 α β n := by
  sorry

theorem μ_p2_q2 (h : Constraints α β n) :
    μ α β n (p2 β) (q2 α β n) = μ2 α β n := by
  sorry

theorem μ_p3_q3 (h : Constraints α β n) :
    μ α β n (p3 α β n) (q3 α β n) = μ3 α β n := by
  sorry

theorem μ_p4_q4 (h : Constraints α β n) :
    μ α β n (p4 α β n) (q4 α β n) = μ4 α β n := by
  sorry

/-- **Main reduction** (thm:pq-redn): under Constraints c1–c4, the infimum of `μ`
over all nonnegative prices equals the minimum of `μ` over the four candidate points. -/
theorem inf_μ_eq_min_candidates (h : Constraints α β n) :
    sInf {m : ℝ | ∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧ m = μ α β n p q} =
      min (μ1 α β n) (min (μ2 α β n) (min (μ3 α β n) (μ4 α β n))) := by
  sorry

end DataMktOligoHard
