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

/-- Implementation view: the caller reads `.id` off the output bins.
Required for first-fit, whose output order does not recover indices by position. -/
abbrev firstFitItems : List (Item α) → Packing (Item α) := firstFit Item.size

-- packing integer-sized items into a bin of capacity 10
set_option linter.style.nativeDecide false in
example : firstFit (fun (i : ℕ) => (i : ℚ) / 10) [6, 7, 4, 3]
    = [[6, 4], [7, 3]] := by native_decide

/-! ## Proof that `firstFit` produces a valid packing -/

omit [IsStrictOrderedRing α]

omit [LinearOrder α] in
/-- Appending an item to a bin adds its size to the load. -/
theorem binLoad_append (size : β → α) (b : List β) (x : β) :
    binLoad size (b ++ [x]) = binLoad size b + size x := by
  simp [binLoad, List.map_append, List.sum_append]

/-- `insertFirst` merely rearranges the items, adding `x`. -/
theorem insertFirst_flatten_perm (size : β → α) (x : β) (bins : List (List β)) :
    List.Perm (insertFirst size x bins).flatten (bins.flatten ++ [x]) := by
  induction bins with
  | nil => simp [insertFirst]
  | cons b rest ih =>
      unfold insertFirst
      by_cases h : binLoad size b + size x ≤ 1
      · simp only [h, if_true, List.flatten_cons]
        -- (b ++ [x]) ++ rest.flatten  ~  (b ++ rest.flatten) ++ [x]
        have e1 : (b ++ [x]) ++ rest.flatten = b ++ ([x] ++ rest.flatten) := by
          rw [List.append_assoc]
        have e2 : (b ++ rest.flatten) ++ [x] = b ++ (rest.flatten ++ [x]) := by
          rw [List.append_assoc]
        rw [e1, e2]
        exact List.perm_append_comm.append_left b
      · simp only [h, if_false, List.flatten_cons]
        rw [List.append_assoc]
        exact ih.append_left b

/-- `insertFirst` preserves the "every bin fits" invariant, given `size x ≤ 1`. -/
theorem insertFirst_fits (size : β → α) (x : β) (bins : List (List β))
    (hbins : ∀ b ∈ bins, binLoad size b ≤ 1) (hx : size x ≤ 1) :
    ∀ b ∈ insertFirst size x bins, binLoad size b ≤ 1 := by
  induction bins with
  | nil =>
      intro b hb
      simp only [insertFirst, List.mem_singleton] at hb
      subst hb
      simpa [binLoad] using hx
  | cons c rest ih =>
      unfold insertFirst
      by_cases h : binLoad size c + size x ≤ 1
      · simp only [h, if_true]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · rw [binLoad_append]; exact h
        · exact hbins b (List.mem_cons_of_mem c hb)
      · simp only [h, if_false]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hbins b (List.mem_cons_self)
        · exact ih (fun b' hb' => hbins b' (List.mem_cons_of_mem c hb')) b hb

/-- Folding `insertFirst` over `l` rearranges the accumulator's items with `l`. -/
theorem foldl_insertFirst_flatten_perm (size : β → α) (l : List β) (acc : List (List β)) :
    List.Perm (l.foldl (fun bins x => insertFirst size x bins) acc).flatten (acc.flatten ++ l) := by
  induction l generalizing acc with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldl_cons]
      refine (ih (insertFirst size x acc)).trans ?_
      -- (insertFirst x acc).flatten ++ rest  ~  acc.flatten ++ (x :: rest)
      have heq : acc.flatten ++ (x :: rest) = (acc.flatten ++ [x]) ++ rest := by simp
      rw [heq]
      exact (insertFirst_flatten_perm size x acc).append_right rest

/-- Folding `insertFirst` over `l` preserves the "every bin fits" invariant. -/
theorem foldl_insertFirst_fits (size : β → α) (l : List β) (acc : List (List β))
    (hacc : ∀ b ∈ acc, binLoad size b ≤ 1) (hl : ∀ x ∈ l, size x ≤ 1) :
    ∀ b ∈ l.foldl (fun bins x => insertFirst size x bins) acc, binLoad size b ≤ 1 := by
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons x rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact insertFirst_fits size x acc hacc (hl x List.mem_cons_self)
      · exact fun y hy => hl y (List.mem_cons_of_mem x hy)

/-- First-fit produces a valid packing on any well-formed instance. -/
theorem firstFit_isPacking (size : β → α) (l : List β) (hl : ValidInput size l) :
    IsPacking size l (firstFit size l) := by
  refine ⟨?_, ?_⟩
  · have := foldl_insertFirst_flatten_perm size l []
    simpa [firstFit] using this
  · have := foldl_insertFirst_fits size l [] (by simp) (fun x hx => (hl x hx).2)
    simpa [firstFit] using this

end
