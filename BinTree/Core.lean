inductive BinTree (α : Type) where
  | nil
  | node (value : α) (l r : BinTree α)

namespace BinTree

def flatten {α : Type} : BinTree α → List α
  | nil => []
  | node v l r => flatten l ++ (v :: (flatten r))

def size {α : Type} : BinTree α → Nat
  | nil => 0
  | node _ l r => l.size + r.size + 1

def height {α : Type} : BinTree α → Nat
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
def demoTree : BinTree Nat :=
  node 3
    (node 1 nil nil)
    (node 5
      nil (node 6 nil nil))

example : demoTree.flatten = [1, 3, 5, 6] := by rfl
example : demoTree.size = 4 := by rfl
example : demoTree.height = 3 := by rfl

theorem flatten_length (t : BinTree α) : t.flatten.length = t.size := by
  induction t with
  | nil => rfl
  | node v l r ihl ihr =>
    rw [flatten, size]
    rw [List.length_append, List.length_cons]
    rw [ihl, ihr]
    rw [Nat.add_assoc]

def is_size_balanced {α : Type} : BinTree α → Prop
  | nil => True
  | node _ l r => (l.is_size_balanced
    ∧ r.is_size_balanced
    ∧ l.size ≤ r.size + 1
    ∧ r.size ≤ l.size + 1)

def is_height_balanced {α : Type} : BinTree α → Prop
  | nil => True
  | node _ l r => (l.is_height_balanced
    ∧ r.is_height_balanced
    ∧ l.height ≤ r.height + 1
    ∧ r.height ≤ l.height + 1)

end BinTree
