import Mathlib.Algebra.Ring.Parity  -- for Odd
import Mathlib.Tactic.Ring  -- for the ring tactic

lemma simplify_product (a b : Int)
    : (2 * a + 1) * (2 * b + 1)
      = 2 * (2 * a * b + a + b) + 1
    := by
  ring

theorem odd_times_odd_is_odd (m n : Int)
    (hM : Odd m) (hN : Odd n)
    : Odd (m * n) := by
  unfold Odd at hM
  obtain ⟨a, hA⟩ := hM
  rw [hA]
  unfold Odd at hN
  obtain ⟨b, hB⟩ := hN
  rw [hB]
  exact ⟨2 * a * b + a + b, simplify_product a b⟩
