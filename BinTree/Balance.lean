import BinTree.Core

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
