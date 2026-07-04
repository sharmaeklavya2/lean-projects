inductive BinTree (α : Type) where
  | nil
  | node (value : α) (l r : BinTree α)

def BinTree.size {α : Type} : BinTree α → Nat
  | nil => 0
  | node _ l r => l.size + r.size + 1

def BinTree.height {α : Type} : BinTree α → Nat
  | nil => 0
  | node _ l r => max l.height r.height + 1

/- Example:
  3
 / \
1   5
     \
      6
should have size 4 and height 3
-/
def BinTree.demoTree : BinTree Nat :=
  BinTree.node 3
    (BinTree.node 1 BinTree.nil BinTree.nil)
    (BinTree.node 5
      BinTree.nil (BinTree.node 6 BinTree.nil BinTree.nil))

example : BinTree.demoTree.size = 4 := by rfl
example : BinTree.demoTree.height = 3 := by rfl

theorem BinTree.size_ub_height (tree: BinTree α)
    : tree.size ≤ 2 ^ tree.height - 1 := by
  induction tree with
  | nil =>
    rw [BinTree.size, BinTree.height]
    decide
  | node _ l r ihl ihr =>
    rw [BinTree.size, BinTree.height]
    /-
    We will let omega handle the arithmetic.
    But omega only works on linear terms.
    So we first prove the relevant facts containing exponents
    in `have` statements. Then omega can use them.

    The `have` statements are written by AI.
    We don't need to know why they are true.
    -/
    have hl : 2 ^ l.height ≤ 2 ^ (max l.height r.height) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hr : 2 ^ r.height ≤ 2 ^ (max l.height r.height) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpow : 2 ^ (max l.height r.height + 1) = 2 ^ (max l.height r.height) * 2 :=
      Nat.pow_succ 2 (max l.height r.height)
    have hposl : 1 ≤ 2 ^ l.height := Nat.one_le_two_pow
    have hposr : 1 ≤ 2 ^ r.height := Nat.one_le_two_pow
    omega

def BinTree.flatten {α : Type} : BinTree α → List α
  | nil => []
  | node v l r => flatten l ++ (v :: (flatten r))

example : BinTree.demoTree.flatten = [1, 3, 5, 6] := by rfl

/-
Left rotation. Takes a tree `(a B (c D E))` and returns `(c (a B D) E)`:

     a                    c
    / \                  / \
   B   c      ─────►    a   E
      / \              / \
     D   E            B   D
-/
def BinTree.rotate_left {α : Type} : BinTree α → BinTree α
  | node a b (node c d e) => node c (node a b d) e
  | tree => tree

-- Rotation preserves infix order
theorem BinTree.rotate_left_order (tree : BinTree α)
    : tree.rotate_left.flatten = tree.flatten := by
  match tree with
  | nil => rfl
  | node _ _ nil => rfl
  | node _u _a (node _v _b _c) =>
    rw [BinTree.rotate_left]
    simp only [BinTree.flatten]
    simp only [List.append_assoc, List.cons_append]

/-
Right rotation. Takes a tree `(a (b C D) E)` and returns `(b C (a D E))`:

     a                    b
    / \                  / \
   b   E      ─────►    C   a
  / \                      / \
 C   D                    D   E
-/
def BinTree.rotate_right {α : Type} : BinTree α → BinTree α
  | node a (node b c d) e => node b c (node a d e)
  | tree => tree

-- Rotation preserves infix order
theorem BinTree.rotate_right_order (tree : BinTree α)
    : tree.rotate_right.flatten = tree.flatten := by
  match tree with
  | nil => rfl
  | node _ nil _ => rfl
  | node _u (node _v _a _b) _c =>
    rw [BinTree.rotate_right]
    simp only [BinTree.flatten]
    simp only [List.append_assoc, List.cons_append]

/-- Fully-recursive balance: *every* node's subtrees differ in size by ≤ 1. -/
def BinTree.is_size_balanced {α : Type} : BinTree α → Prop
  | nil => True
  | node _ l r => l.is_size_balanced ∧ r.is_size_balanced ∧ l.size ≤ r.size + 1 ∧ r.size ≤ l.size + 1

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
    | m :: rest => .node m (BinTree.build ((x :: xs).take (n / 2))) (BinTree.build rest)
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

/-- A tree's node count equals the length of its in-order flattening:
    `flatten` emits exactly one element per node. True for *every* tree. -/
theorem BinTree.flatten_length (t : BinTree α) : t.flatten.length = t.size := by
  induction t with
  | nil => rfl
  | node v l r ihl ihr =>
    rw [BinTree.flatten, BinTree.size]
    rw [List.length_append, List.length_cons]
    rw [ihl, ihr]
    rw [Nat.add_assoc]

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
