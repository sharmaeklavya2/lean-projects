import BinTree.Core

/-
Turns a list into a height-balanced tree by putting the middle element
at the root and recursing on the two halves.

Note the recursion is *well-founded*, not structural:
we recurse on `take k` and the tail of `drop k`, which are not sub-terms of the input,
so we discharge termination via `termination_by`/`decreasing_by` on the list length.
-/
def BinTree.build {α : Type} : List α → BinTree α
  | [] => .nil
  | x :: xs =>
    let n := (x :: xs).length
    match hd : (x :: xs).drop (n / 2) with
    | [] => .nil  -- unreachable: k < length, so `drop k` is non-empty
    | m :: rest => .node m (build ((x :: xs).take (n / 2))) (build rest)
termination_by l => l.length
decreasing_by
  · simp only [List.length_take, List.length_cons]
    omega
  · have h1 : ((x :: xs).drop (n / 2)).length = n - n / 2 :=
      List.length_drop
    rw [hd, List.length_cons] at h1
    omega

-- Sanity check: a list gets rebuilt into a bushy tree.
-- (`build` is well-founded, so it doesn't reduce by `rfl`; `native_decide` evaluates it.)
example : (BinTree.build [1, 2, 3, 4, 5, 6, 7]).height = 3 := by native_decide

/-- `build` is a right inverse of `flatten`: rebuilding from a list's elements
    reproduces exactly that list, in order. The crux is `take k ++ drop k = id`. -/
theorem BinTree.flatten_build (list : List α) : (BinTree.build list).flatten = list := by
  fun_induction BinTree.build list with
  | case1 => rfl
  | case2 x xs n hd =>
    -- Unreachable: `drop (n/2)` of a non-empty list can't be `[]`. Derive the contradiction.
    exfalso
    have hdrop : ((x :: xs).drop (n / 2)).length = n - n / 2 := List.length_drop
    rw [hd] at hdrop
    have hn : n = xs.length + 1 := List.length_cons
    simp only [List.length_nil] at hdrop
    omega
  | case3 x xs n m rest hd ih2 ih1 =>
    -- flatten (node m L R) = L.flatten ++ m :: R.flatten; IHs give back `take` and `rest`.
    simp only [BinTree.flatten, ih1, ih2]
    -- goal: take (n/2) (x::xs) ++ m :: rest = x :: xs; undo `hd`, then take/drop recombine.
    rw [← hd, List.take_append_drop]

/-- The rebuilt tree has exactly as many nodes as the list has elements.
    Now a one-step corollary: `size = flatten.length` and `build` round-trips. -/
theorem BinTree.build_size (list : List α) : (BinTree.build list).size = list.length := by
  rw [← BinTree.flatten_length]
  rw [BinTree.flatten_build]

theorem BinTree.build_is_size_balanced (list : List α) : (BinTree.build list).is_size_balanced := by
  fun_induction BinTree.build list with
  | case1 => simp only [BinTree.is_size_balanced]
  | case2 x xs n hd => simp only [BinTree.is_size_balanced]
  | case3 x xs n m rest hd ih2 ih1 =>
    -- Subtrees are balanced by IH; their sizes are the half-lengths, which differ by ≤ 1.
    simp only [BinTree.is_size_balanced, BinTree.build_size]
    simp only [List.length_take]
    have hdrop : ((x :: xs).drop (n / 2)).length = n - n / 2 := List.length_drop
    rw [hd, List.length_cons] at hdrop
    have hn : n = xs.length + 1 := List.length_cons
    exact ⟨ih2, ih1, by omega, by omega⟩
