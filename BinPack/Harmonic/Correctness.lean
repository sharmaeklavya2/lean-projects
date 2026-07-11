module

public import BinPack.Harmonic.Core
import Mathlib.Data.List.Perm.Basic

/-!
# Correctness of `harmonicPack`

`harmonicPack` produces a valid packing (`IsPacking`) of any `ValidInput` instance,
for any category count `M ≥ 1`. The two obligations of `IsPacking` split cleanly
along the algorithm's structure:

* **`fits`** (no bin overflows): each bin comes from a per-category `nextFit`, and
  `nextFit_isPacking` already guarantees its bins fit — the filtered sublist is
  still `ValidInput`.
* **`perm`** (every item placed once): next-fit permutes each category's items, and
  the categories `1..M` partition the input — every valid item has exactly one
  category in that range (`cat_mem_Icc`), so concatenating the categories recovers
  the whole multiset.
-/

@[expose] public section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
variable {β : Type*}

/-- Flatten commutes with an outer `flatMap` whose branches are themselves lists of
lists: `(L.flatMap f).flatten = L.flatMap (fun x => (f x).flatten)`. -/
private theorem flatten_flatMap {γ δ : Type*} (L : List γ) (f : γ → List (List δ)) :
    (L.flatMap f).flatten = L.flatMap (fun x => (f x).flatten) := by
  induction L with
  | nil => simp
  | cons a as ih => rw [List.flatMap_cons, List.flatten_append, ih, List.flatMap_cons]

/-- A well-formed item's category lies in `{1, …, M}` (needs `1 ≤ M`). This is what
makes the categories `1..M` cover every item of a `ValidInput` instance. -/
theorem cat_mem_Icc (size : β → α) (M : ℕ) (hM : 1 ≤ M) (x : β)
    (hpos : 0 < size x) (hle : size x ≤ 1) :
    1 ≤ cat M (size x) ∧ cat M (size x) ≤ M := by
  have hinv : (1 : α) ≤ 1 / size x := by rw [le_div_iff₀ hpos, one_mul]; exact hle
  have hfloor : (1 : ℤ) ≤ ⌊1 / size x⌋ := Int.le_floor.mpr (by exact_mod_cast hinv)
  have hraw : 1 ≤ (⌊1 / size x⌋).toNat := by
    have := Int.toNat_le_toNat hfloor; simpa using this
  refine ⟨?_, Nat.min_le_left _ _⟩
  simp only [cat]
  exact Nat.le_min.mpr ⟨hM, hraw⟩

omit [IsStrictOrderedRing α] in
/-- The count of `a` in one category's filtered sublist: the whole count of `a` if
`a`'s category is that one, else `0`. -/
private theorem count_filter_cat [BEq β] [LawfulBEq β]
    (size : β → α) (M c : ℕ) (l : List β) (a : β) :
    (l.filter (fun x => cat M (size x) == c + 1)).count a
      = if cat M (size a) == c + 1 then l.count a else 0 := by
  by_cases h : (cat M (size a) == c + 1) = true
  · rw [if_pos h]; exact List.count_filter h
  · rw [if_neg h, List.count_eq_zero]
    intro hmem
    rw [List.mem_filter] at hmem
    exact h hmem.2

/-- The indicator sum `∑_{c<M} (if k = c+1 then N else 0)` collapses to `N` exactly
when `k ∈ {1, …, M}`. Used to evaluate `count` across the category partition. -/
private theorem sum_indicator (k N : ℕ) : ∀ M,
    ((List.range M).map (fun c => if k = c + 1 then N else 0)).sum
      = if 1 ≤ k ∧ k ≤ M then N else 0 := by
  intro M
  induction M with
  | zero => simp only [List.range_zero, List.map_nil, List.sum_nil]; split_ifs <;> omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    split_ifs <;> omega

/-- **`harmonicPack` is correct**: on any `ValidInput` instance with `M ≥ 1` it
produces a valid packing. -/
public theorem harmonicPack_isPacking (size : β → α) (M : ℕ) (hM : 1 ≤ M)
    (l : List β) (hl : ValidInput size l) :
    IsPacking size l (harmonicPack size M l) := by
  classical
  -- Every filtered sublist is still ValidInput (filter keeps a subset).
  have hvalid : ∀ c, ValidInput size (l.filter (fun x => cat M (size x) == c + 1)) :=
    fun c x hx => hl x (List.mem_of_mem_filter hx)
  refine ⟨?_, ?_⟩
  · -- perm: (harmonicPack …).flatten ~ l
    unfold harmonicPack
    rw [flatten_flatMap]
    -- replace each next-fit packing by its category's items (perm per branch)
    refine (List.Perm.flatMap_left _
      (fun c _ => (nextFit_isPacking size _ (hvalid c)).perm)).trans ?_
    -- the categories 1..M partition l — proved via counts
    rw [List.perm_iff_count]
    intro a
    rw [List.count_flatMap]
    have hmap : List.map (List.count a ∘ fun c => l.filter fun x => cat M (size x) == c + 1)
          (List.range M)
        = List.map (fun c => if cat M (size a) = c + 1 then l.count a else 0) (List.range M) := by
      apply List.map_congr_left
      intro c _
      simp only [Function.comp_apply, count_filter_cat, beq_iff_eq]
    rw [hmap, sum_indicator]
    by_cases ha : a ∈ l
    · obtain ⟨hpos, hle⟩ := hl a ha
      obtain ⟨h1, h2⟩ := cat_mem_Icc size M hM a hpos hle
      rw [if_pos ⟨h1, h2⟩]
    · rw [List.count_eq_zero.mpr ha]; simp
  · -- fits: every bin comes from some category's next-fit, which never overflows
    intro b hb
    unfold harmonicPack at hb
    rw [List.mem_flatMap] at hb
    obtain ⟨c, _, hb⟩ := hb
    exact (nextFit_isPacking size _ (hvalid c)).fits b hb
