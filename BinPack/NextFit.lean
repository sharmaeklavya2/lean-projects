module

public import BinPack.Common
meta import Mathlib.Algebra.Field.Rat

@[expose] public section

/-!
# Next-fit

Next-fit keeps only the most-recently-opened bin available.
Its analysis rests on the fact that any two adjacent bins have loads summing to more than `1`
(the first item of a new bin did not fit in the previous one), giving the `2·OPT + 1` bound.

The body is an order-of-arrival fold. Internal bin orientation (it prepends,
so bins come out reversed) is irrelevant to `IsPacking`, which only asks for a
`Perm`; it will matter only when we recover item *indices*.
-/

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*}

/-- Place `x` in the currently-open bin (the head) if it fits there,
else close that bin and open a new one. Only the most-recent bin is considered,
which is what distinguishes next-fit from first-fit's full scan. -/
def insertNext (size : β → α) (x : β) : List (List β) → List (List β)
  | [] => [[x]]
  | b :: rest =>
      if binLoad size b + size x ≤ 1 then (x :: b) :: rest
      else [x] :: b :: rest

/-- Next-fit: keep only the most-recent bin open (head of the list).
If the item fits there, add it; otherwise close it and open a new bin. -/
def nextFit (size : β → α) (l : List β) : Packing β :=
  l.foldl (fun bins x => insertNext size x bins) []

theorem nextFit_isPacking (size : β → α) (l : List β) :
    IsPacking size l (nextFit size l) := by
  sorry

theorem nextFit_ratio (size : β → α) (l : List β) :
    (nextFit size l).length ≤ 2 * optimum size l + 1 := by
  sorry

-- Examples of invoking nextFit
-- Note that the list of bins (and the items within) are output in reverse

set_option linter.style.nativeDecide false in
example : nextFit (id : ℚ → ℚ) [0.3, 0.2, 0.5, 0.6, 0.5]
    = [[0.5], [0.6], [0.5, 0.2, 0.3]] := by native_decide

-- packing integer-sized items into a bin of capacity 10
set_option linter.style.nativeDecide false in
example : nextFit (fun (i : ℕ) => (i : ℚ) / 10) [6, 7, 4, 3]
    = [[3, 4], [7], [6]] := by native_decide

end
