module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt

/-! # Constants used in the inapproximability factor -/

@[expose] public section

namespace DataMktOligo.MuOpt

variable (α β ν : ℝ)

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

/-- The inapproximability constant `c* := min(μ₁,μ₂,μ₃,μ₄)`. -/
noncomputable def cStar : ℝ := min (μ1 α β ν) (min (μ2 α β ν) (min (μ3 α β ν) (μ4 α β ν)))

end DataMktOligo.MuOpt
