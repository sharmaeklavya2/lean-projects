module

public import LinDataMkt.Defs

/-!
# Demand as fractional knapsack

A buyer facing linear prices solves a fractional knapsack problem: maximize
`∑ j, τ i j * x j` subject to `∑ j, p j * x j ≤ b i` and `x ∈ [0,1]^m`.
Its solutions are exactly the greedy ones, consuming datasets in non-increasing order
of *bang-per-buck* `τ i j / p j`.

## Main results

* `LinDataMkt.isDemand_iff`: an affordable bundle is a demand iff it admits no improving
  swap and leaves no idle budget. This is a local, permutation-free characterization.
* `LinDataMkt.isDemand_of_isGreedy`: consuming greedily in bang-per-buck order, in the
  sense of `LinDataMkt.IsGreedy`, produces a demand. This is the paper's phrasing.
-/

@[expose] public section

namespace LinDataMkt

variable {n m : ℕ} (mkt : Instance n m) (p : Fin m → ℝ) (i : Fin n)

/-- Buyer `i` weakly prefers dataset `k`'s bang-per-buck to dataset `j`'s, i.e.
`τ i j / p j ≤ τ i k / p k`.

Stated multiplicatively so that it is meaningful at zero prices and so that proofs need no
division lemmas; the two forms agree whenever `p j` and `p k` are positive. -/
def bpbLE (j k : Fin m) : Prop := mkt.τ i j * p k ≤ mkt.τ i k * p j

/-- The bundle `x` admits no improving swap: buyer `i` never holds a positive amount of a
dataset `k` while some strictly better bang-per-buck dataset `j` still has room to spare. -/
def NoImprovingSwap (x : Fin m → ℝ) : Prop :=
  ∀ j k, 0 < x k → x j < 1 → bpbLE mkt p i j k

/-- The bundle `x` leaves no idle budget: either it exhausts buyer `i`'s budget,
or it already contains all of every dataset she values. -/
def Saturated (x : Fin m → ℝ) : Prop :=
  cost p x = mkt.b i ∨ ∀ j, 0 < mkt.τ i j → x j = 1

/-- **Characterization of demand.** An affordable bundle is utility-maximizing exactly when
it admits no improving swap and leaves no idle budget. -/
public theorem isDemand_iff (hp : ∀ j, 0 < p j) (x : Fin m → ℝ) :
    IsDemand mkt p i x ↔
      x ∈ affordableSet mkt p i ∧ NoImprovingSwap mkt p i x ∧ Saturated mkt p i x := by
  sorry

/-- The bundle `x` is the greedy bundle for the consumption order `σ`: buyer `i` buys as
much of `σ 0` as she can, then as much of `σ 1` as she can, and so on, skipping datasets of
no value to her.

The `min 1 (max 0 ·)` clamps the purchase to `[0,1]`, and the subtracted sum is what she has
already spent on datasets earlier in the order. -/
def IsGreedy (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ) : Prop :=
  ∀ j, x (σ j) =
    if 0 < mkt.τ i (σ j) then
      min 1 (max 0 ((mkt.b i - ∑ k ∈ Finset.univ.filter (· < j), p (σ k) * x (σ k)) / p (σ j)))
    else 0

/-- **Greedy is optimal.** If `σ` orders the datasets by non-increasing bang-per-buck, then
the greedy bundle for `σ` is a demand. -/
public theorem isDemand_of_isGreedy (hp : ∀ j, 0 < p j) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ j k, j ≤ k → bpbLE mkt p i (σ k) (σ j))
    (x : Fin m → ℝ) (hx : IsGreedy mkt p i σ x) :
    IsDemand mkt p i x := by
  sorry

end LinDataMkt
