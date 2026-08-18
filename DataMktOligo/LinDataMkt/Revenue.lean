module

public import DataMktOligo.LinDataMkt.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Revenue and the sellers' pricing game

Given prices, each buyer picks some element of her demand correspondence, and the sellers
collect revenue. Since demand is multi-valued, so is revenue: `DataMktOligo.LinDataMkt.V p`
is the set of revenue vectors attainable at prices `p`, one for each way buyers break ties.

The sellers are thereby engaged in a pricing game, whose approximate equilibria are
`DataMktOligo.LinDataMkt.IsApproxNE`.

## Main definitions

* `DataMktOligo.LinDataMkt.revenue`: sellers' revenues from a profile of purchases.
* `DataMktOligo.LinDataMkt.V`: the set of valid revenue vectors at given prices.
* `DataMktOligo.LinDataMkt.bestResponseRevenue`: the best revenue a seller can get by
  unilaterally repricing.
* `DataMktOligo.LinDataMkt.IsApproxNE`: whether a price vector is an approximate Nash equilibrium
  of the pricing game.
-/

@[expose] public section

namespace DataMktOligo.LinDataMkt

variable {n m : ℕ} (mkt : Instance n m) (p : Fin m → ℝ)

/-- Seller `j`'s total revenue when each buyer `i` purchases `x i`. -/
def revenue (x : Fin n → Fin m → ℝ) : Fin m → ℝ :=
  fun j => ∑ i, mkt.w i * (p j * x i j)

/-- A profile in which every buyer purchases some bundle she demands. -/
def IsDemandProfile (x : Fin n → Fin m → ℝ) : Prop := ∀ i, IsDemand mkt p i (x i)

/-- The set of *valid* revenue vectors at prices `p`: those arising from some profile of
buyer demands. It is a set rather than a single vector precisely because of tie-breaking -/
def V : Set (Fin m → ℝ) :=
  {r | ∃ x : Fin n → Fin m → ℝ, IsDemandProfile mkt p x ∧ r = revenue mkt p x}

/-- Redundant lemma to help with backward/forward compatibility if we change the definition of V. -/
theorem mem_V_iff {r : Fin m → ℝ} :
    r ∈ V mkt p ↔ ∃ x, IsDemandProfile mkt p x ∧ r = revenue mkt p x := Iff.rfl

/-! ### The pricing game -/

variable (j : Fin m)

/-- The revenues seller `j` can obtain by unilaterally deviating from `p` to another price,
holding all other sellers' prices fixed. -/
def deviationRevenues : Set ℝ :=
  {rj | ∃ pj' : ℝ, 0 ≤ pj' ∧ ∃ r ∈ V mkt (Function.update p j pj'), rj = r j}

/-- Seller `j`'s best achievable revenue when unilaterally deviating from `p`.
This is a supremum, not a maximum: it need not be attained, since a seller may want to
undercut a rival by an infinitesimal amount. -/
noncomputable def bestResponseRevenue : ℝ := sSup (deviationRevenues mkt p j)

/-- The prices `p` form a `c`-approximate Nash equilibrium: no seller can unilaterally
deviate to improve her revenue by more than a factor of `c`, no matter how buyers break ties. -/
def IsApproxNE (c : ℝ) : Prop :=
  IsNonnegVector p ∧ ∀ r ∈ V mkt p, ∀ j, bestResponseRevenue mkt p j ≤ c * r j

/-! ### Basic properties -/

theorem revenue_nonneg {x : Fin n → Fin m → ℝ} (hp : IsNonnegVector p)
    (hx : IsDemandProfile mkt p x) (j : Fin m) : 0 ≤ revenue mkt p x j := by
  refine Finset.sum_nonneg fun i _ => mul_nonneg (mkt.w_nonneg i) ?_
  exact mul_nonneg (hp j) ((mem_unitCube_iff.1 (hx i).1.1) j).1

theorem nonneg_of_mem_V {r : Fin m → ℝ} (hp : IsNonnegVector p) (hr : r ∈ V mkt p) (j : Fin m) :
    0 ≤ r j := by
  obtain ⟨x, hx, rfl⟩ := hr
  exact revenue_nonneg mkt p hp hx j

/-! ### Revenue is bounded by the total budget

No seller can extract more than the buyers collectively have to spend, whatever the prices.
These results are not required for the paper's main theorems; they exist just to certify that
`bestResponseRevenue` is a genuine supremum rather than a junk value, so the lean theorem
statements mean what we think they mean.
-/

/-- The total money in the market: `∑ i, w i * b i`. -/
def totalBudget : ℝ := ∑ i, mkt.w i * mkt.b i

/-- A buyer never spends more than her budget on any single dataset. -/
public theorem spend_le_budget (hp : IsNonnegVector p) {i : Fin n} {x : Fin m → ℝ}
    (hx : x ∈ affordableSet mkt p i) (j : Fin m) : p j * x j ≤ mkt.b i := by
  refine le_trans ?_ hx.2.1
  exact Finset.single_le_sum
    (f := fun k => p k * x k)
    (fun k _ => mul_nonneg (hp k) ((mem_unitCube_iff.1 hx.1) k).1) (Finset.mem_univ j)

public theorem revenue_le_totalBudget {x : Fin n → Fin m → ℝ} (hp : IsNonnegVector p)
    (hx : IsDemandProfile mkt p x) (j : Fin m) : revenue mkt p x j ≤ totalBudget mkt := by
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_left (spend_le_budget mkt p hp (hx i).1 j) (mkt.w_nonneg i)

public theorem le_totalBudget_of_mem_V {r : Fin m → ℝ} (hp : IsNonnegVector p) (hr : r ∈ V mkt p)
    (j : Fin m) : r j ≤ totalBudget mkt := by
  obtain ⟨x, hx, rfl⟩ := hr
  exact revenue_le_totalBudget mkt p hp hx j

/-- Replacing one price of a nonnegative vector by a nonnegative price keeps it nonnegative. -/
private theorem isNonnegVector_update (hp : IsNonnegVector p) {pj' : ℝ} (hpj' : 0 ≤ pj') :
    IsNonnegVector (Function.update p j pj') := by
  intro k
  rcases eq_or_ne k j with rfl | hkj
  · simpa using hpj'
  · simpa [Function.update_of_ne hkj] using hp k

/-- The revenues available to a deviating seller are bounded above, so her
`bestResponseRevenue` is a genuine supremum. -/
public theorem bddAbove_deviationRevenues (hp : IsNonnegVector p) :
    BddAbove (deviationRevenues mkt p j) := by
  refine ⟨totalBudget mkt, ?_⟩
  rintro _ ⟨pj', hpj', r, hr, rfl⟩
  exact le_totalBudget_of_mem_V mkt _ (isNonnegVector_update p j hp hpj') hr j

/-- Seller `j` can always deviate to her current price, so her best response revenue is at
least any revenue she currently earns. -/
public theorem le_bestResponseRevenue_of_mem_V {r : Fin m → ℝ} (hp : IsNonnegVector p)
    (hr : r ∈ V mkt p) : r j ≤ bestResponseRevenue mkt p j := by
  refine le_csSup (bddAbove_deviationRevenues mkt p j hp) ⟨p j, hp j, r, ?_, rfl⟩
  simpa [Function.update_eq_self] using hr

end DataMktOligo.LinDataMkt
