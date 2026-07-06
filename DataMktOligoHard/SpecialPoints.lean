import DataMktOligoHard.Basic

/-!
# Properties of the special points (sp-props.tex)

This file corresponds to the "Properties of the Special Points" subsection.
It establishes the interval bounds and defining identities of the special points
`(pᵢ, qᵢ)` and proves `μ(pᵢ, qᵢ) = μᵢ` for `i ∈ {1, 2, 3}`.
(The `i = 4` case is on the knife-edge `p = α·q` and is deferred to the case-4 file.)

(Notation: this section transcribes old-paper text, where the poor-buyer count is
written `n - 1`; that is our Lean `n`. In particular the paper's `n·ĉ₁` is our
`(n + 1)·chat1 = n + α·q1`.)
-/

namespace DataMktOligoHard

variable (α β n : ℝ)

/-- `μ(p₁, q₁) = μ₁` (thm:p1). Here `p₁ < α·q₁`, so `V` is the singleton
`{(r₁⁺, r₂⁻)}` and both best-response ratios equal `μ₁`. -/
theorem μ_p1_q1 (h : Constraints α β n) :
    μ α β n (p1 α β n) (q1 α β n) = μ1 α β n := by
  sorry

/-- `μ(p₂, q₂) = μ₂` (thm:q2), where `p₂ = β`. Here `p₂ > α·q₂`, so `V` is the
singleton `{(r₁⁻, r₂⁺)}` and both best-response ratios equal `μ₂`. -/
theorem μ_p2_q2 (h : Constraints α β n) :
    μ α β n (p2 β) (q2 α β n) = μ2 α β n := by
  sorry

/-- `μ(p₃, q₃) = μ₃` (thm:p3). Here `p₃ > α·q₃`, so `V` is the singleton
`{(r₁⁻, r₂⁺)}` and both best-response ratios equal `μ₃`. -/
theorem μ_p3_q3 (h : Constraints α β n) :
    μ α β n (p3 α β n) (q3 α β n) = μ3 α β n := by
  sorry

end DataMktOligoHard
