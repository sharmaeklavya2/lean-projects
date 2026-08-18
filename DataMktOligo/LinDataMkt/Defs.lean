module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Data markets with linear utilities

A data marketplace instance `([n], [m], (τᵢⱼ), (bᵢ), (wᵢ))` has `n` buyers and `m` sellers,
each seller owning a single dataset. Buyers may purchase arbitrary fractions of datasets.

This file sets up instances and the demand correspondence under linear (uniform) pricing:
an `x` fraction of a dataset priced `p` costs `p * x`.

## Main definitions

* `DataMktOligo.LinDataMkt.Instance`: a data market instance.
* `DataMktOligo.LinDataMkt.util`: a buyer's (linear) utility for a bundle.
* `DataMktOligo.LinDataMkt.affordableSet`: the bundles a buyer is permitted to buy at given prices.
* `DataMktOligo.LinDataMkt.IsDemand`: a buyer's demand, i.e. an affordable
  utility-maximizing bundle.
-/

@[expose] public section

namespace DataMktOligo.LinDataMkt

/-- A data marketplace instance with `n` buyers and `m` sellers.

Buyer `i` has budget `b i`, values the entire dataset `j` at `τ i j`, and has multiplicity `w i`.
Utilities are linear: a bundle `z ∈ [0,1]^m` is worth `∑ j, τ i j * z j` to buyer `i`.

The weight `w i` is the number of copies of buyer `i` present in the market.
It is a real rather than a natural, since every quantity of interest is continuous in it. -/
structure Instance (n m : ℕ) where
  b : Fin n → ℝ  -- Buyer `i`'s budget.
  τ : Fin n → Fin m → ℝ  -- Buyer `i`'s value for the entire dataset `j`.
  w : Fin n → ℝ  -- Buyer `i`'s weight, i.e. her multiplicity.
  b_nonneg : ∀ i, 0 ≤ b i
  τ_nonneg : ∀ i j, 0 ≤ τ i j
  w_nonneg : ∀ i, 0 ≤ w i

/-- The set of all possible bundles, i.e., the unit hypercube `[0,1]^m`.
Here `z j` is the fraction of dataset `j` held. -/
def unitCube (m : ℕ) : Set (Fin m → ℝ) := {z | ∀ j, z j ∈ Set.Icc (0 : ℝ) 1}

/-- Redundant lemma to help with backward/forward compatibility
if we change the definition of unitCube. -/
theorem mem_unitCube_iff {m : ℕ} {z : Fin m → ℝ} :
    z ∈ unitCube m ↔ ∀ j, z j ∈ Set.Icc (0 : ℝ) 1 := Iff.rfl

variable {n m : ℕ} (mkt : Instance n m) (p : Fin m → ℝ) (i : Fin n)

/-- Buyer `i`'s utility for a bundle `z`. -/
def util (z : Fin m → ℝ) : ℝ := ∑ j, mkt.τ i j * z j

/-- The cost of the bundle `z` under linear prices `p`. -/
def cost (z : Fin m → ℝ) : ℝ := ∑ j, p j * z j

/-- The bundles buyer `i` is permitted to buy at prices `p`:
costing at most her budget, and supported on datasets of positive value to her.
The last condition is a modelling assumption, not a consequence of optimality. -/
def affordableSet : Set (Fin m → ℝ) :=
  {z ∈ unitCube m | cost p z ≤ mkt.b i ∧ ∀ j, 0 < z j → 0 < mkt.τ i j}

/-- Buyer `i`'s *demand* at prices `p`: an affordable bundle maximizing her utility. -/
def IsDemand (z : Fin m → ℝ) : Prop :=
  z ∈ affordableSet mkt p i ∧ ∀ y ∈ affordableSet mkt p i, util mkt i y ≤ util mkt i z

def demand : Set (Fin m → ℝ) := {z | IsDemand mkt p i z}

theorem mem_demand_iff {z : Fin m → ℝ} : z ∈ demand mkt p i ↔ IsDemand mkt p i z := Iff.rfl

/-! ### Basic properties -/

theorem cost_zero : cost p 0 = 0 := by simp [cost]

/-- Buying nothing is always permitted. -/
theorem zero_mem_affordableSet : (0 : Fin m → ℝ) ∈ affordableSet mkt p i := by
  refine ⟨mem_unitCube_iff.2 fun j => ?_, ?_, ?_⟩ <;> simp [cost_zero, mkt.b_nonneg i]

theorem util_zero : util mkt i 0 = 0 := by simp [util]

/-- A demand is worth at least nothing, since buying nothing is an option. -/
theorem util_nonneg_of_isDemand {z : Fin m → ℝ} (hz : IsDemand mkt p i z) :
    0 ≤ util mkt i z := by
  simpa [util_zero] using hz.2 0 (zero_mem_affordableSet mkt p i)

end DataMktOligo.LinDataMkt
