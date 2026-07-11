module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public import BinPack.Harmonic.Syl
public import BinPack.NextFit

meta import Mathlib.Data.Rat.Floor

@[expose] public section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

def rawcat (x : α) : ℕ :=
  (⌊1/x⌋.toNat)

def cat (M : ℕ) (x : α) : ℕ :=
  -- M ≥ 1 and x ∈ (0, 1]
  -- category of an item of size x
  min M (⌊1/x⌋.toNat)

def wh (M : ℕ) (x : α) : α :=
  -- M ≥ 1 and x ∈ (0, 1]
  -- harmonic weight of an item of size x
  if x ≤ 1/M then M * x / (M-1) else 1 / (⌊1/x⌋.toNat)

/-! ## The target bound `Q M`

`T n` sums the reciprocals of the first `n` modified Sylvester numbers, and `Q M`
is the harmonic algorithm's asymptotic approximation factor. These are kept over
`ℚ` (not the generic `α`) so specific values stay `#eval`-computable; the weight
bound casts them to `ℝ` where needed. -/

/-- `T n = ∑_{i<n} 1 / syl (i+1)`: the sum of reciprocals of the first `n`
modified Sylvester numbers. -/
def T (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, 1 / syl (i + 1)

/-- `Q M` is the (conjectured) asymptotic approximation factor of the harmonic
algorithm with parameter `M`: with `i` the modified Sylvester inverse of `M`,
`Q M = T i + (1/(M-1)) / syl i`. -/
def Q (M : ℕ) : ℚ :=
  let i := syl_inv_fast M
  T i + (1 / (M-1)) / (syl i)

/-! ## The harmonic algorithm

The harmonic algorithm groups items by their category `cat M` and packs each group
independently with next-fit, then concatenates the resulting bins. Because two
items in the same category `c` each have size `> 1/(c+1)`, a next-fit bin of that
category is packed tightly — this is what yields the ratio-`1` counting argument
(with additive constant `M-1`, one nearly-empty bin per category). The definition
is generic in `α`/`β`; the approximation analysis specializes to `α = β = ℝ`. -/

/-- The harmonic algorithm with parameter `M`: for each category `c ∈ {1, …, M}`,
next-fit the items whose category is `c`, and concatenate the bins across
categories. Items outside categories `1..M` (only possible for ill-formed sizes,
i.e. `size x > 1` or `size x ≤ 0`) are dropped; on a `ValidInput` instance every
item has a category in `1..M`, so the packing covers all items. -/
def harmonicPack (size : β → α) (M : ℕ) (l : List β) : Packing β :=
  (List.range M).flatMap fun c =>
    nextFit size (l.filter fun x => cat M (size x) == c + 1)

set_option linter.style.nativeDecide false in
example : harmonicPack (id : ℚ → ℚ) 5 [1, 0.5, 0.33, 0.25, 0.2]
    = [[1], [0.5], [0.33], [0.25], [0.2]] := by native_decide
