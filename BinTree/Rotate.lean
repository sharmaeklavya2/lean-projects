import BinTree.Core

namespace BinTree

/-
Left rotation. Takes a tree `(a B (c D E))` and returns `(c (a B D) E)`:

     a                    c
    / \                  / \
   B   c      ─────►    a   E
      / \              / \
     D   E            B   D
-/
def rotate_left {α : Type} : BinTree α → BinTree α
  | node a b (node c d e) => node c (node a b d) e
  | tree => tree

-- Rotation preserves infix order
theorem rotate_left_order (tree : BinTree α)
    : tree.rotate_left.flatten = tree.flatten := by
  match tree with
  | nil => rfl
  | node _ _ nil => rfl
  | node _u _a (node _v _b _c) =>
    rw [rotate_left]
    simp only [flatten]
    simp only [List.append_assoc, List.cons_append]

/-
Right rotation. Takes a tree `(a (b C D) E)` and returns `(b C (a D E))`:

     a                    b
    / \                  / \
   b   E      ─────►    C   a
  / \                      / \
 C   D                    D   E
-/
def rotate_right {α : Type} : BinTree α → BinTree α
  | node a (node b c d) e => node b c (node a d e)
  | tree => tree

-- Rotation preserves infix order
theorem rotate_right_order (tree : BinTree α)
    : tree.rotate_right.flatten = tree.flatten := by
  match tree with
  | nil => rfl
  | node _ nil _ => rfl
  | node _u (node _v _a _b) _c =>
    rw [rotate_right]
    simp only [flatten]
    simp only [List.append_assoc, List.cons_append]

end BinTree
