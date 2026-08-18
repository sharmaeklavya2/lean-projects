module

public import DataMktOligo.LinDataMkt.Defs

/-!
# Demand as fractional knapsack

A buyer facing linear prices solves a fractional knapsack problem: maximize
`∑ j, τ i j * x j` subject to `∑ j, p j * x j ≤ b i` and `x ∈ [0,1]^m`.
Its solutions are exactly the greedy ones, consuming datasets in non-increasing order
of *bang-per-buck* `τ i j / p j`.

## Main results

* `DataMktOligo.LinDataMkt.isDemand_iff`: an affordable bundle is a demand iff it admits
  no improving swap and leaves no idle budget. This is a local, permutation-free
  characterization.
* `DataMktOligo.LinDataMkt.isDemand_of_isGreedy`: consuming greedily in bang-per-buck order, in the
  sense of `DataMktOligo.LinDataMkt.IsGreedy`, produces a demand. This is the paper's phrasing.
-/

@[expose] public section

namespace DataMktOligo.LinDataMkt

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
it admits no improving swap and leaves no idle budget.

Prices need only be *nonnegative*; what the proof needs instead is a *positive budget*.
Both hypotheses are necessary. With a negative price the buyer is paid to take a dataset
and `cost` stops being monotone. With `b i = 0` the characterization is false: one buyer,
one free dataset (`p = 0`) of value `1`, and `x = ![1/2]` satisfies all three conditions on
the right — `Saturated` via `cost p x = 0 = b i` — yet buying the whole dataset is
affordable and strictly better.

Positive budget rules that out: if a valuable dataset `j` is free and `x j < 1`, then
`Saturated`'s second disjunct fails outright, while its first gives `cost p x = b i > 0`,
so some `k` has `p k > 0` and `x k > 0`, and `NoImprovingSwap` on `(j, k)` demands
`τ i j * p k ≤ τ i k * p j = 0` — impossible. Hence free valuable datasets are fully
bought, and the usual exchange argument applies to the rest. -/
public theorem isDemand_iff (hp : IsNonnegVector p) (hb : 0 < mkt.b i) (x : Fin m → ℝ) :
    IsDemand mkt p i x ↔
      x ∈ affordableSet mkt p i ∧ NoImprovingSwap mkt p i x ∧ Saturated mkt p i x := by
  sorry

/-- The bundle `x` is the greedy bundle for the consumption order `σ`: buyer `i` buys as
much of `σ 0` as she can, then as much of `σ 1` as she can, and so on, skipping datasets of
no value to her.

The `min 1 (max 0 ·)` clamps the purchase to `[0,1]`, and the subtracted sum is what she has
already spent on datasets earlier in the order.

A dataset of no value is skipped. A *free* dataset of positive value is taken in full: the
division branch would give the wrong answer there, since Lean's `x / 0 = 0` would make the
buyer skip a dataset that costs her nothing. -/
def IsGreedy (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ) : Prop :=
  ∀ j, x (σ j) =
    if 0 < mkt.τ i (σ j) then
      if p (σ j) = 0 then 1
      else
        min 1 (max 0
          ((mkt.b i - ∑ k ∈ Finset.univ.filter (· < j), p (σ k) * x (σ k)) / p (σ j)))
    else 0

/-- **Greedy is optimal.** If `σ` orders the datasets by non-increasing bang-per-buck, then
the greedy bundle for `σ` is a demand. -/
public theorem isDemand_of_isGreedy (hp : IsNonnegVector p) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ j k, j ≤ k → bpbLE mkt p i (σ k) (σ j))
    (x : Fin m → ℝ) (hx : IsGreedy mkt p i σ x) :
    IsDemand mkt p i x := by
  sorry

end DataMktOligo.LinDataMkt
