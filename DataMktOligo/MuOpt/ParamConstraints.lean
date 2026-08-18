module

public import Mathlib.Data.Real.Basic

/-! # Constraints on parameters used in the example instance -/

namespace DataMktOligo.MuOpt

variable (α β ν : ℝ)

/-- The four constraints on α, β, and ν (items c1–c4). -/
public structure Constraints (α β ν : ℝ) : Prop where
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

end DataMktOligo.MuOpt
