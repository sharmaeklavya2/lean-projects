module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Lattice

@[expose] public section

/-!
# Bin packing: shared vocabulary

This file sets up the vocabulary common to every bin-packing algorithm. The
individual algorithms live in their own files (`BinPack.NextFit`,
`BinPack.FirstFit`), each importing this one.

Items are generic (`β`) with a `size : β → α` projection, `α` an ordered field
(instantiate `α := ℝ` or `α := ℚ`). Take `β := α, size := id` for identity-free
mathematical reasoning; take `β := Item α` when an implementation needs to read
off *which* item went where.
-/

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*}

/-- A packing is a list of bins. -/
abbrev Packing (β : Type*) := List (List β)

/-- The load of a bin is the total size of its items. -/
def binLoad (size : β → α) (b : List β) : α := (b.map size).sum

/-- `p` is a valid packing of `input`: every item is placed exactly once
(`perm`, a multiset equality) and no bin overflows capacity `1` (`fits`). -/
structure IsPacking (size : β → α) (input : List β) (p : Packing β) : Prop where
  /-- The items of `p` are a rearrangement of `input`. -/
  perm : List.Perm p.flatten input
  /-- No bin exceeds capacity `1`. -/
  fits : ∀ b ∈ p, binLoad size b ≤ 1

/-- The optimum: the fewest bins in any valid packing of `l`. -/
noncomputable def optimum (size : β → α) (l : List β) : ℕ :=
  sInf { n | ∃ p : Packing β, IsPacking size l p ∧ p.length = n }

/-- A well-formed instance: every item has size in `(0, 1]`. The upper bound is
what makes a packing *possible* (an item bigger than a bin can never fit); the
lower bound (positivity) is the standing assumption that bin loads strictly grow. -/
def ValidInput (size : β → α) (l : List β) : Prop :=
  ∀ x ∈ l, 0 < size x ∧ size x ≤ 1

/-- An item carrying an identifier alongside its size. Instantiate `β := Item α`
when the caller must read off *which* item went where. Genericize `id`'s type if
you prefer strings or handles. -/
structure Item (α : Type*) where
  id : ℕ
  size : α

end
