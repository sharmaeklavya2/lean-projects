module

public import BinPack.Common
-- public import Mathlib.Data.List.Sort
meta import Mathlib.Algebra.Field.Rat

@[expose] public section

/-!
# First-fit

First-fit scans *all* open bins and packs each item in the first that has room.
-/

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*}

/-- Insert `x` into the first bin (front-to-back) that has room,
else append a fresh bin at the end. -/
def insertFirst (size : β → α) (x : β) : List (List β) → List (List β)
  | [] => [[x]]
  | b :: rest =>
      if binLoad size b + size x ≤ 1 then (b ++ [x]) :: rest
      else b :: insertFirst size x rest

/-- First-fit: place each item in the first bin that fits. -/
def firstFit (size : β → α) (l : List β) : Packing β :=
  l.foldl (fun bins x => insertFirst size x bins) []

theorem firstFit_isPacking (size : β → α) (l : List β) :
    IsPacking size l (firstFit size l) := by
  sorry

/-- Implementation view: the caller reads `.id` off the output bins.
Required for first-fit, whose output order does not recover indices by position. -/
abbrev firstFitItems : List (Item α) → Packing (Item α) := firstFit Item.size

-- packing integer-sized items into a bin of capacity 10
set_option linter.style.nativeDecide false in
example : firstFit (fun (i : ℕ) => (i : ℚ) / 10) [6, 7, 4, 3]
    = [[6, 4], [7, 3]] := by native_decide

end
