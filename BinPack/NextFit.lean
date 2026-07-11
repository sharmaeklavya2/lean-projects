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

-- Examples of invoking nextFit
-- Note that the list of bins (and the items within) are output in reverse

set_option linter.style.nativeDecide false in
example : nextFit (id : ℚ → ℚ) [0.3, 0.2, 0.5, 0.6, 0.5]
    = [[0.5], [0.6], [0.5, 0.2, 0.3]] := by native_decide

-- packing integer-sized items into a bin of capacity 10
set_option linter.style.nativeDecide false in
example : nextFit (fun (i : ℕ) => (i : ℚ) / 10) [6, 7, 4, 3]
    = [[3, 4], [7], [6]] := by native_decide

/-! ## Proof that `nextFit` produces a valid packing -/

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- Load of a bin with one more item on top. -/
theorem binLoad_cons (size : β → α) (x : β) (b : List β) :
    binLoad size (x :: b) = size x + binLoad size b := by
  simp [binLoad]

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem binLoad_singleton (size : β → α) (x : β) : binLoad size [x] = size x := by
  simp [binLoad]

omit [IsStrictOrderedRing α] in
/-- Inserting one item prepends it to the flattened contents — the same in both
branches (grow the open bin, or open a new one), so `insertNext` never drops or
duplicates an item. -/
theorem insertNext_flatten (size : β → α) (x : β) (p : List (List β)) :
    (insertNext size x p).flatten = x :: p.flatten := by
  rcases p with _ | ⟨b, rest⟩
  · rfl
  · simp only [insertNext]
    split <;> simp

omit [IsStrictOrderedRing α] in
/-- Folding `insertNext` over `l` yields the reversed input (each item is
prepended), on top of whatever the accumulator already held. -/
theorem foldl_insertNext_flatten (size : β → α) (l : List β) (acc : List (List β)) :
    (l.foldl (fun p x => insertNext size x p) acc).flatten = l.reverse ++ acc.flatten := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldl_cons, List.reverse_cons]
      rw [ih (insertNext size a acc), insertNext_flatten]
      simp

omit [IsStrictOrderedRing α] in
/-- Inserting an item of size `≤ 1` into a packing whose bins all have load `≤ 1`
keeps every load `≤ 1`: growing the open bin is guarded by the `if`, and a fresh
bin's load is exactly `size x ≤ 1`. -/
theorem insertNext_fits (size : β → α) (x : β) (p : List (List β))
    (hx : size x ≤ 1) (hp : ∀ b ∈ p, binLoad size b ≤ 1) :
    ∀ c ∈ insertNext size x p, binLoad size c ≤ 1 := by
  rcases p with _ | ⟨b, rest⟩
  · intro c hc
    simp only [insertNext, List.mem_singleton] at hc
    subst hc
    rw [binLoad_singleton]; exact hx
  · simp only [insertNext]
    split
    · rename_i h
      intro c hc
      rw [List.mem_cons] at hc
      rcases hc with rfl | hc
      · rw [binLoad_cons, add_comm]; exact h
      · exact hp c (List.mem_cons.mpr (Or.inr hc))
    · intro c hc
      rw [List.mem_cons] at hc
      rcases hc with rfl | hc
      · rw [binLoad_singleton]; exact hx
      · exact hp c hc

omit [IsStrictOrderedRing α] in
/-- The load invariant lifts across the whole fold. -/
theorem foldl_insertNext_fits (size : β → α) (l : List β) (acc : List (List β))
    (hl : ∀ x ∈ l, size x ≤ 1) (hacc : ∀ b ∈ acc, binLoad size b ≤ 1) :
    ∀ b ∈ l.foldl (fun p x => insertNext size x p) acc, binLoad size b ≤ 1 := by
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons a t ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro x hx; exact hl x (List.mem_cons.mpr (Or.inr hx))
      · exact insertNext_fits size a acc (hl a (List.mem_cons.mpr (Or.inl rfl))) hacc

omit [IsStrictOrderedRing α] in
/-- Next-fit produces a valid packing on any well-formed instance. -/
theorem nextFit_isPacking (size : β → α) (l : List β) (hl : ValidInput size l) :
    IsPacking size l (nextFit size l) := by
  constructor
  · show List.Perm (nextFit size l).flatten l
    simp only [nextFit]
    rw [foldl_insertNext_flatten]
    simp only [List.flatten_nil, List.append_nil]
    exact List.reverse_perm l
  · intro b hb
    simp only [nextFit] at hb
    exact foldl_insertNext_fits size l [] (fun x hx => (hl x hx).2) (by simp) b hb

/-! ## Proof of `nextFit`'s approximation ratio -/

theorem nextFit_ratio (size : β → α) (l : List β) (hl : ValidInput size l) :
    (nextFit size l).length ≤ 2 * optimum size l + 1 := by
  sorry

end
