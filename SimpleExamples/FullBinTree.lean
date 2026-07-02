inductive FullBinTree (α : Type) where
  | leaf (value: α): FullBinTree α
  | cons (value: α) (left right : FullBinTree α) : FullBinTree α

def FullBinTree.size {α : Type} : FullBinTree α → Nat
  | leaf _ => 1
  | cons _ left right => left.size + right.size + 1

def FullBinTree.height {α : Type} : FullBinTree α → Nat
  | leaf _ => 0
  | cons _ left right => max left.height right.height + 1

/- Example:
 3
/ \
1  5
  / \
 4   6
should have size 5 and height 2
-/
def demoTree : FullBinTree Nat :=
  FullBinTree.cons 3
    (FullBinTree.leaf 1)
    (FullBinTree.cons 5
      (FullBinTree.leaf 4) (FullBinTree.leaf 6))

example : demoTree.size = 5 := by rfl
example : demoTree.height = 2 := by rfl

theorem FullBinTree.size_ub_height (tree: FullBinTree α)
    : tree.size ≤ 2 ^ (tree.height + 1) - 1 := by
  induction tree with
  | leaf _ =>
    rw [FullBinTree.size, FullBinTree.height]
    decide
  | cons _ l r ihl ihr =>
    rw [FullBinTree.size, FullBinTree.height]
    /-
    We will let omega handle the arithmetic.
    But omega only works on linear terms.
    So we first prove the relevant facts containing exponents
    in `have` statements. Then omega can use them.

    The `have` statements are written by AI.
    We don't need to know why they are true.
    -/
    have hl : 2 ^ (l.height + 1) ≤ 2 ^ (max l.height r.height + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hr : 2 ^ (r.height + 1) ≤ 2 ^ (max l.height r.height + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpow : 2 ^ (max l.height r.height + 1 + 1) = 2 ^ (max l.height r.height + 1) * 2 :=
      Nat.pow_succ 2 (max l.height r.height + 1)
    have hposl : 1 ≤ 2 ^ (l.height + 1) := Nat.one_le_two_pow
    have hposr : 1 ≤ 2 ^ (r.height + 1) := Nat.one_le_two_pow
    omega
