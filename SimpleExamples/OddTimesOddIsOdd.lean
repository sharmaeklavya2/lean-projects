def Odd (n: Int) : Prop := ∃ k, n = 2 * k + 1

theorem simplify_product (a b : Int)
    : (2 * a + 1) * (2 * b + 1)
      = 2 * (a * (2 * b + 1) + b) + 1
    := calc
  (2 * a + 1) * (2 * b + 1)
      = (2 * a) * (2 * b + 1) + 1 * (2 * b + 1)  := by rw [Int.add_mul]
    _ = 2 * (a * (2 * b + 1)) + (2 * b + 1)  := by rw [Int.mul_assoc, Int.one_mul]
    _ = (2 * (a * (2 * b + 1)) + 2 * b) + 1  := by rw [Int.add_assoc]
    _ = 2 * (a * (2 * b + 1) + b) + 1  := by rw [←Int.mul_add]

theorem odd_times_odd_is_odd (m n : Int)
    (hM : Odd m) (hN : Odd n)
    : Odd (m * n) := by
  unfold Odd at hM
  obtain ⟨a, hA⟩ := hM
  rw [hA]
  unfold Odd at hN
  obtain ⟨b, hB⟩ := hN
  rw [hB]
  exact ⟨a * (2 * b + 1) + b, simplify_product a b⟩
