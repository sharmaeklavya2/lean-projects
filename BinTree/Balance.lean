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
    They are easy to prove, so we don't care how they are formalized in lean.
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

/-
Lower bound counterpart to `size_ub_height`, but only for *size-balanced* trees:
such a tree of height `h` has at least `2^(h-1)` nodes, i.e. `2^h ≤ 2 * size`.

To avoid natural-number subtraction and keep everything `omega`-friendly, we
package two facts:
  * `2 ^ height ≤ 2 * size + 1`  — holds for every size-balanced tree (incl. nil), and
  * `1 ≤ size → 2 ^ height ≤ 2 * size` — the sharper, parity-free bound for non-nil trees.
The second fact is what makes the induction go through: when we bound a node by its
taller child, the "+1" slack from a leaf would break the arithmetic, but the sharp
bound on a non-empty child does not.
-/
theorem BinTree.pow_height_le_size (t : BinTree α) (hb : t.is_size_balanced)
    : 2 ^ t.height ≤ 2 * t.size + 1 ∧ (1 ≤ t.size → 2 ^ t.height ≤ 2 * t.size) := by
  -- Proof written by Claude. Not reviewed or edited.
  induction t with
  | nil =>
    refine ⟨?_, ?_⟩
    · rw [BinTree.height, BinTree.size]
      decide
    · intro h
      rw [BinTree.size] at h
      omega
  | node v l r ihl ihr =>
    rw [BinTree.is_size_balanced] at hb
    obtain ⟨hbl, hbr, hlr, hrl⟩ := hb
    obtain ⟨Al, Bl⟩ := ihl hbl
    obtain ⟨Ar, Br⟩ := ihr hbr
    rw [BinTree.size, BinTree.height]
    -- The key sharp bound; the two returned facts follow from it immediately.
    have key : 2 ^ (max l.height r.height + 1) ≤ 2 * (l.size + r.size + 1) := by
      rw [Nat.pow_succ]
      -- 2 ^ height is monotone in height, so `2 ^ (max ..)` is the taller child's power.
      rcases Nat.le_total l.height r.height with hh | hh
      · rw [Nat.max_eq_right hh]
        rcases Nat.eq_zero_or_pos r.size with hz | hz
        · omega                     -- r empty: `Ar` gives `2 ^ r.height ≤ 1`
        · have hb2 := Br hz; omega  -- r non-empty: sharp bound + balance `r ≤ l + 1`
      · rw [Nat.max_eq_left hh]
        rcases Nat.eq_zero_or_pos l.size with hz | hz
        · omega
        · have hb2 := Bl hz; omega
    exact ⟨by omega, fun _ => key⟩

theorem height_diff_ub_size_diff
  (t1 t2 : BinTree α) (d : Nat) (hd : d ≤ 1)
  (h1 : t1.is_size_balanced) (h2 : t2.is_size_balanced)
  (hsd1 : t1.size ≤ t2.size) (hsd2 : t2.size ≤ t1.size + d)
  : t1.height ≤ t2.height ∧ t2.height ≤ t1.height + d
  := by
  -- Proof written by Claude. Not reviewed or edited.
  -- Sandwich `2 ^ height` between size-based bounds for each tree.
  have hpos1 : 1 ≤ 2 ^ t1.height := Nat.one_le_two_pow
  have hpos2 : 1 ≤ 2 ^ t2.height := Nat.one_le_two_pow
  have U1 := BinTree.size_ub_height t1              -- t1.size ≤ 2 ^ t1.height - 1
  have U2 := BinTree.size_ub_height t2
  have Lo1 : 2 ^ t1.height ≤ 2 * t1.size + 1 := (BinTree.pow_height_le_size t1 h1).1
  have Lo2 : 2 ^ t2.height ≤ 2 * t2.size + 1 := (BinTree.pow_height_le_size t2 h2).1
  refine ⟨?_, ?_⟩
  · -- t1.height ≤ t2.height : a taller t1 would force t1.size > t2.size.
    rcases Nat.lt_or_ge t2.height t1.height with hc | hc
    · exfalso
      have hp : 2 ^ (t2.height + 1) ≤ 2 ^ t1.height :=
        Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at hp
      omega
    · exact hc
  · -- t2.height ≤ t1.height + d : t2 taller by ≥ d+1 would force t2.size too large.
    rcases Nat.lt_or_ge (t1.height + d) t2.height with hc | hc
    · exfalso
      obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
      · have hp : 2 ^ (t1.height + 1) ≤ 2 ^ t2.height :=
          Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.pow_succ] at hp
        omega
      · have hp : 2 ^ (t1.height + 2) ≤ 2 ^ t2.height :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have he : 2 ^ (t1.height + 2) = 2 ^ t1.height * 4 := by rw [Nat.pow_add]
        omega
    · exact hc

/-
A size-balanced tree is also height-balanced. The recursive balancedness goals
follow from the induction hypotheses; the per-node height-difference bound is
exactly `height_diff_ub_size_diff` at `d = 1`, applied to the two children.
Since that lemma expects its trees ordered by size, we case on `Nat.le_total`.
-/
theorem BinTree.sizebal_imp_heightbal (t : BinTree α)
    (hb : t.is_size_balanced) : t.is_height_balanced := by
  induction t with
  | nil => simp only [BinTree.is_height_balanced]
  | node v l r ihl ihr =>
    rw [BinTree.is_size_balanced] at hb
    rw [BinTree.is_height_balanced]
    obtain ⟨hbl, hbr, hlr, hrl⟩ := hb
    refine ⟨?_, ?_, ?_⟩
    · exact ihl hbl
    · exact ihr hbr
    · rcases Nat.le_total l.size r.size with h | h
      · have htemp1 := height_diff_ub_size_diff l r 1 (by decide) hbl hbr h (by assumption)
        omega
      · have := height_diff_ub_size_diff r l 1 (by decide) hbr hbl h (by assumption)
        omega
