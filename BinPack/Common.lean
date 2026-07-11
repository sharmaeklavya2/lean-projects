module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Algebra.Order.BigOperators.Group.List

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

/-! ## Weight functions

The reusable engine for approximation ratios. Assign each item a *weight*
`wt : β → α`. To bound an algorithm by `ratio · wbound · OPT + const` it suffices
to show two independent facts:

* **(algorithm fact)** the algorithm uses fewer than `ratio · totalWeight + const`
  bins, and
* **(weight fact, `IsWeighting`)** any single bin's items weigh at most `wbound`.

`length_lt_opt` combines these into the ratio bound. The weight fact is a
property of `wt` alone (proved once per weight function); the algorithm fact is
the per-algorithm counting argument. Keeping `ratio` (algorithm) and `wbound`
(weight function) separate lets one reuse a single `IsWeighting` proof across
algorithms with different `ratio`s. -/

/-- Total weight of a list of items. -/
def totalWeight (wt : β → α) (l : List β) : α := (l.map wt).sum

/-- `wt` is a *weighting* with per-bin bound `wbound` (for capacity-`1` bins): any
bin of items with total size `≤ 1` has total weight `≤ wbound`. This is the fact
one proves about the weight function, independent of any algorithm or instance. -/
def IsWeighting (size wt : β → α) (wbound : α) : Prop :=
  ∀ b : List β, binLoad size b ≤ 1 → totalWeight wt b ≤ wbound

/-- The total weight of the items is at most `wbound` times the number of bins in
*any* valid packing (each bin weighs `≤ wbound`, and the packing's bins partition
the items). No positivity of weights is needed. -/
theorem weight_le_opt (size wt : β → α) (wbound : α) (l : List β)
    (hw : IsWeighting size wt wbound) (q : Packing β) (hq : IsPacking size l q) :
    totalWeight wt l ≤ wbound * q.length := by
  have hsplit : totalWeight wt l = (q.map (fun b => totalWeight wt b)).sum := by
    have hperm := (hq.perm.map wt).sum_eq
    simp only [totalWeight]
    rw [← hperm]
    simp [List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
  rw [hsplit]
  have hb : ∀ x ∈ q.map (fun b => totalWeight wt b), x ≤ wbound := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨b, hbq, rfl⟩ := hx
    exact hw b (hq.fits b hbq)
  have h := List.sum_le_card_nsmul (q.map (fun b => totalWeight wt b)) wbound hb
  rw [List.length_map, nsmul_eq_mul, mul_comm] at h
  exact h

/-- **The weighting method.** Two separate quantities combine here: `wbound` is a
property of the *weight function* (any one bin weighs `≤ wbound`, i.e.
`IsWeighting`), while `ratio` is a property of the *algorithm* (it uses fewer than
`ratio · totalWeight + const` bins). Then the packing uses fewer than
`ratio · wbound · OPT + const` bins. -/
theorem length_lt_opt (size wt : β → α) (ratio wbound const : α) (l : List β) (p : Packing β)
    (hratio : 0 ≤ ratio)
    (hp : IsPacking size l p)
    (hw : IsWeighting size wt wbound)
    (halg : (p.length : α) < ratio * totalWeight wt l + const) :
    (p.length : α) < ratio * wbound * optimum size l + const := by
  have hne : {n | ∃ p' : Packing β, IsPacking size l p' ∧ p'.length = n}.Nonempty :=
    ⟨p.length, p, hp, rfl⟩
  obtain ⟨q, hq, hqlen⟩ := Nat.sInf_mem hne
  have hqlen' : q.length = optimum size l := hqlen
  have hw' := weight_le_opt size wt wbound l hw q hq
  have hopt : (optimum size l : α) = (q.length : α) := by rw [hqlen']
  rw [hopt, mul_assoc]
  exact halg.trans_le (add_le_add (mul_le_mul_of_nonneg_left hw' hratio) (le_refl const))

end
