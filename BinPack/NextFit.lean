module

public import BinPack.Common
public import Mathlib.Tactic.Linarith
meta import Mathlib.Algebra.Field.Rat

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
@[expose]
public def insertNext (size : β → α) (x : β) : List (List β) → List (List β)
  | [] => [[x]]
  | b :: rest =>
      if binLoad size b + size x ≤ 1 then (x :: b) :: rest
      else [x] :: b :: rest

/-- Next-fit: keep only the most-recent bin open (head of the list).
If the item fits there, add it; otherwise close it and open a new bin. -/
@[expose]
public def nextFit (size : β → α) (l : List β) : Packing β :=
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
public theorem nextFit_isPacking (size : β → α) (l : List β) (hl : ValidInput size l) :
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

/-! ## Proof of `nextFit`'s approximation ratio

The bound `length ≤ 2·OPT` comes from the weighting method with `wt := size`
(so `wbound = 1`) and algorithm ratio `2`. The algorithm fact (`nextFit_halg`)
is the classic adjacency argument: consecutive bins have loads summing to `> 1`,
so `k` bins force total size `> (k-1)/2`, i.e. `k < 2·(total) + 1`. Because
`length` and `OPT` are naturals, that strict `< 2·OPT + 1` sharpens to `≤ 2·OPT`. -/

/-- Load of the currently-open (head) bin; `0` if there are no bins. -/
def headLoad (size : β → α) : List (List β) → α
  | [] => 0
  | b :: _ => binLoad size b

/-- Total load across all bins. -/
def packLoad (size : β → α) (bins : List (List β)) : α := (bins.map (binLoad size)).sum

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem packLoad_cons (size : β → α) (b : List β) (rest : List (List β)) :
    packLoad size (b :: rest) = binLoad size b + packLoad size rest := by
  simp [packLoad]

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- `packLoad` is the total weight (with `wt := size`) of the flattened bins. -/
theorem packLoad_eq (size : β → α) (bins : List (List β)) :
    packLoad size bins = totalWeight size bins.flatten := by
  simp only [packLoad, totalWeight, List.map_flatten, List.sum_flatten,
    List.map_map, Function.comp_def]
  rfl

/-- The next-fit invariant, single step. Writing `P bins` for the load bound and
`Q bins` for "the open bin is nonempty", inserting one item of positive size
preserves `P ∧ Q`. `P` is what will yield the `2·(total) + 1` bound; `Q` supplies
the strictness (the final open bin carries positive load). -/
theorem insertNext_bound (size : β → α) (x : β) (bins : List (List β)) (hs : 0 < size x)
    (hP : (bins.length : α) ≤ 2 * packLoad size bins - headLoad size bins + 1)
    (hQ : bins = [] ∨ 0 < headLoad size bins) :
    ((insertNext size x bins).length : α)
        ≤ 2 * packLoad size (insertNext size x bins) - headLoad size (insertNext size x bins) + 1
      ∧ (insertNext size x bins = [] ∨ 0 < headLoad size (insertNext size x bins)) := by
  rcases bins with _ | ⟨b, rest⟩
  · refine ⟨?_, Or.inr ?_⟩
    · simp only [insertNext, packLoad, headLoad, binLoad_singleton,
        List.length_cons, List.length_nil, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      push_cast; linarith
    · simp only [insertNext, headLoad, binLoad_singleton]; linarith
  · have hb : 0 < binLoad size b := by
      rcases hQ with h | h
      · exact absurd h (by simp)
      · simpa [headLoad] using h
    rw [packLoad_cons] at hP
    simp only [headLoad] at hP
    push_cast [List.length_cons] at hP
    simp only [insertNext]
    split
    · rename_i hfit
      refine ⟨?_, Or.inr ?_⟩
      · simp only [headLoad, packLoad_cons, binLoad_cons]
        push_cast [List.length_cons]; linarith
      · simp only [headLoad, binLoad_cons]; linarith
    · rename_i hnofit
      have hnofit' : 1 < binLoad size b + size x := not_le.mp hnofit
      refine ⟨?_, Or.inr ?_⟩
      · simp only [headLoad, packLoad_cons, binLoad_singleton]
        push_cast [List.length_cons]; linarith
      · simp only [headLoad, binLoad_singleton]; linarith

/-- Lift the single-step invariant across the whole fold. -/
theorem foldl_insertNext_bound (size : β → α) :
    ∀ (l : List β) (acc : List (List β)), (∀ x ∈ l, 0 < size x) →
      ((acc.length : α) ≤ 2 * packLoad size acc - headLoad size acc + 1
        ∧ (acc = [] ∨ 0 < headLoad size acc)) →
      (((l.foldl (fun p x => insertNext size x p) acc).length : α)
          ≤ 2 * packLoad size (l.foldl (fun p x => insertNext size x p) acc)
              - headLoad size (l.foldl (fun p x => insertNext size x p) acc) + 1
        ∧ ((l.foldl (fun p x => insertNext size x p) acc) = []
            ∨ 0 < headLoad size (l.foldl (fun p x => insertNext size x p) acc))) := by
  intro l
  induction l with
  | nil => intro acc _ h; simpa using h
  | cons a t ih =>
      intro acc hl ⟨hP, hQ⟩
      simp only [List.foldl_cons]
      exact ih _ (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
        (insertNext_bound size a acc (hl a (List.mem_cons.mpr (Or.inl rfl))) hP hQ)

omit [IsStrictOrderedRing α] in
/-- `packLoad` of a next-fit packing is the total size of the items. -/
theorem packLoad_nextFit (size : β → α) (l : List β) :
    packLoad size (nextFit size l) = totalWeight size l := by
  rw [packLoad_eq]
  have hfl : (nextFit size l).flatten = l.reverse := by
    simp only [nextFit]; rw [foldl_insertNext_flatten]; simp
  rw [hfl]
  simp [totalWeight, List.map_reverse, List.sum_reverse]

/-- The algorithm fact: next-fit uses strictly fewer than `2·(total size) + 1`
bins. This is the adjacency argument, packaged via the fold invariant. -/
public theorem nextFit_halg (size : β → α) (l : List β) (hl : ValidInput size l) :
    ((nextFit size l).length : α) < 2 * totalWeight size l + 1 := by
  have hpos : ∀ x ∈ l, 0 < size x := fun x hx => (hl x hx).1
  have hbase :
      (([] : List (List β)).length : α)
          ≤ 2 * packLoad size ([] : List (List β)) - headLoad size ([] : List (List β)) + 1
        ∧ (([] : List (List β)) = [] ∨ 0 < headLoad size ([] : List (List β))) :=
    ⟨by simp [packLoad, headLoad], Or.inl rfl⟩
  obtain ⟨hP, hQ⟩ := foldl_insertNext_bound size l [] hpos hbase
  rw [show l.foldl (fun p x => insertNext size x p) [] = nextFit size l from rfl] at hP hQ
  rw [packLoad_nextFit] at hP
  rcases hQ with hnil | hhead
  · have htot : totalWeight size l = 0 := by rw [← packLoad_nextFit, hnil]; simp [packLoad]
    rw [hnil, htot]; simp
  · linarith [hP, hhead]

omit [IsStrictOrderedRing α] in
/-- `size` is trivially a weighting with per-bin bound `1`: a bin of total size
`≤ 1` has total weight (= size) `≤ 1`. The competitive factor `2` comes entirely
from the algorithm fact `nextFit_halg`, not from the weight function. -/
theorem isWeighting_size (size : β → α) : IsWeighting size size 1 := fun _ hb => hb

/-- **Next-fit is 2-competitive.** The weighting method with `wt := size`
(so `wbound = 1`) and algorithm ratio `2` gives `length < 2·1·OPT + 1`; since
`length` and `OPT` are naturals, this sharpens to `length ≤ 2·OPT`. -/
public theorem nextFit_ratio (size : β → α) (l : List β) (hl : ValidInput size l) :
    (nextFit size l).length ≤ 2 * optimum size l := by
  have main := length_lt_opt size size 2 1 1 l (nextFit size l)
    (by norm_num) (nextFit_isPacking size l hl) (isWeighting_size size) (nextFit_halg size l hl)
  simp only [mul_one] at main
  have hcast : ((nextFit size l).length : α) < ((2 * optimum size l + 1 : ℕ) : α) := by
    push_cast; linarith
  have hnat : (nextFit size l).length < 2 * optimum size l + 1 := by exact_mod_cast hcast
  omega
