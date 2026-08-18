module

public import DataMktOligo.LinDataMkt.Defs
public import DataMktOligo.MuOpt.ParamConstraints
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The two-seller data market instance

Two sellers, each owning one dataset, and two *kinds* of buyers.

* The **poor** buyer (index `0`) has budget `1` and values the datasets at `α` and `1`.
  There are `ν` copies of her, recorded as her weight.
* The **rich** buyer (index `1`) has budget `β` and values the datasets at `β` and `0`.
  There is one of her.
-/

@[expose] public section

namespace DataMktOligo.NashInapprox

open DataMktOligo.LinDataMkt DataMktOligo.MuOpt

variable {α β ν : ℝ}

/-! ### Nonnegativity facts extracted from `Constraints` -/

theorem alpha_nonneg (h : Constraints α β ν) : 0 ≤ α := by linarith [h.c1_lo]
theorem beta_nonneg (h : Constraints α β ν) : 0 ≤ β := by linarith [h.c1_lo, h.c1_mid]
theorem nu_nonneg (h : Constraints α β ν) : 0 ≤ ν := by linarith [h.c1_mid, h.c1_hi]

/-! ### The instance -/

/-- It is parameterized by a proof of `Constraints` only to discharge the nonnegativity fields.
Since `Constraints` is a `Prop`, proof irrelevance makes `inst h₁` and `inst h₂`
definitionally equal, so the choice of proof never matters downstream. -/
noncomputable def inst (h : Constraints α β ν) : Instance 2 2 where
  b := ![1, β]
  τ := ![![α, 1], ![β, 0]]
  w := ![ν, 1]
  b_nonneg := by
    intro i; fin_cases i
    · norm_num
    · simpa using beta_nonneg h
  τ_nonneg := by
    intro i j; fin_cases i <;> fin_cases j
    · simpa using alpha_nonneg h
    · norm_num
    · simpa using beta_nonneg h
    · norm_num
  w_nonneg := by
    intro i; fin_cases i
    · simpa using nu_nonneg h
    · norm_num

/-- Prices are written as the vector literal `![p, q]`:
seller `0` charges `p` and seller `1` charges `q`. -/
theorem isNonnegVector_prices {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    IsNonnegVector ![p, q] := by
  intro j; fin_cases j
  · simpa using hp
  · simpa using hq

/-! ### Component lemmas

Stated so that later files never unfold `inst` directly. -/

@[simp] theorem inst_b_poor (h : Constraints α β ν) : (inst h).b 0 = 1 := rfl
@[simp] theorem inst_b_rich (h : Constraints α β ν) : (inst h).b 1 = β := rfl

@[simp] theorem inst_tau_poor_0 (h : Constraints α β ν) : (inst h).τ 0 0 = α := rfl
@[simp] theorem inst_tau_poor_1 (h : Constraints α β ν) : (inst h).τ 0 1 = 1 := rfl
@[simp] theorem inst_tau_rich_0 (h : Constraints α β ν) : (inst h).τ 1 0 = β := rfl
@[simp] theorem inst_tau_rich_1 (h : Constraints α β ν) : (inst h).τ 1 1 = 0 := rfl

@[simp] theorem inst_w_poor (h : Constraints α β ν) : (inst h).w 0 = ν := rfl
@[simp] theorem inst_w_rich (h : Constraints α β ν) : (inst h).w 1 = 1 := rfl

/-- Both buyers have strictly positive budgets. -/
theorem inst_b_pos (h : Constraints α β ν) (i : Fin 2) : 0 < (inst h).b i := by
  fin_cases i
  · norm_num
  · simpa using (by linarith [h.c1_lo, h.c1_mid] : (0:ℝ) < β)

end DataMktOligo.NashInapprox
