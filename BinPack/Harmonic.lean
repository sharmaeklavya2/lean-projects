import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.BigOperators

import BinPack.Syl

/- Definitions -/

noncomputable def rawcat (x : ℝ) : ℕ :=
  (⌊1/x⌋.toNat)

noncomputable def cat (M : ℕ) (x : ℝ) : ℕ :=
  -- M ≥ 1 and x ∈ (0, 1]
  -- category of an item of size x
  min M (⌊1/x⌋.toNat)

noncomputable def wh (M : ℕ) (x : ℝ) : ℝ :=
  -- M ≥ 1 and x ∈ (0, 1]
  -- harmonic weight of an item of size x
  if x ≤ 1/M then M * x / (M-1) else 1 / (⌊1/x⌋.toNat)


def T (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, 1 / syl (i + 1)

def T2 (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, 1 / (syl (i + 1) + 1)

def Q (M : ℕ) :=
  let i := syl_inv_fast M
  T i + (1 / (M-1)) / (syl i)

structure HarmonicBoundPreconds (M : ℕ) (y : List ℝ) : Prop where
  hM : M ≥ 2
  hyb : ∀ z ∈ y, (0 < z ∧ z ≤ 1)
  hySum : y.sum ≤ 1

/- Lemmas -/

theorem T2_simp (n : ℕ) :
    T2 n = 1 - 1 / (syl (n + 1)) := by
  -- telescoping: 1/(kⱼ+1) = g j - g (j+1) with g j = 1 / syl (j+1),
  -- since syl (j+2) = syl (j+1) * (syl (j+1) + 1)
  have key : ∀ i, (1 : ℚ) / (syl (i + 1) + 1)
      = (fun j => (1 : ℚ) / syl (j + 1)) i - (fun j => (1 : ℚ) / syl (j + 1)) (i + 1) := by
    intro i
    have hkpos : (0 : ℚ) < syl (i + 1) := by exact_mod_cast syl_pos i
    have hk : (syl (i + 1) : ℚ) ≠ 0 := hkpos.ne'
    have hsucc : (syl (i + 2) : ℚ) = (syl (i + 1) : ℚ) * ((syl (i + 1) : ℚ) + 1) := by
      have : syl (i + 2) = syl (i + 1) * (syl (i + 1) + 1) := rfl
      rw [this]; push_cast; ring
    simp only
    rw [show i + 1 + 1 = i + 2 from rfl, hsucc]
    field_simp
    ring
  unfold T2
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_range_sub']
  simp [syl]

-- From `rawcat x = k` (with `x ∈ (0,1]`), the floor characterization pins `1/x`
-- into `[k, k+1)`.
theorem rawcat_bounds (x : ℝ) (k : ℕ) (hx0 : 0 < x) (hx1 : x ≤ 1) (hk : rawcat x = k) :
    (k : ℝ) ≤ 1 / x ∧ 1 / x < k + 1 := by
  have hinv : (1 : ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx0, one_mul]; exact hx1
  have hfloor_pos : (1 : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.mpr (by exact_mod_cast hinv)
  have hnn : (0 : ℤ) ≤ ⌊1 / x⌋ := by omega
  have heq : ⌊1 / x⌋ = (k : ℤ) := by
    have : (⌊1 / x⌋.toNat : ℤ) = ⌊1 / x⌋ := Int.toNat_of_nonneg hnn
    rw [rawcat] at hk
    omega
  have hbounds := Int.floor_eq_iff.mp heq
  refine ⟨by exact_mod_cast hbounds.1, ?_⟩
  have := hbounds.2
  push_cast at this ⊢
  linarith

-- Lower bound: a small item (`x ≤ 1/m`) has raw category at least `m`.
theorem rawcat_ge (x : ℝ) (m : ℕ) (hx0 : 0 < x) (hxm : x ≤ 1 / (m : ℝ)) (hm : 0 < m) :
    m ≤ rawcat x := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hinv : (m : ℝ) ≤ 1 / x := by
    rw [le_div_iff₀ hx0]
    rw [le_div_iff₀ hmR] at hxm
    nlinarith [hxm]
  have hfloor : (m : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.mpr (by exact_mod_cast hinv)
  have hz : (0 : ℤ) ≤ ⌊1 / x⌋ := le_trans (by exact_mod_cast Nat.zero_le m) hfloor
  rw [rawcat, Int.le_toNat hz]
  exact hfloor

-- `rawcat` is antitone: a bigger item has a smaller (or equal) raw category.
theorem rawcat_anti (x x' : ℝ) (hx0 : 0 < x) (hle : x ≤ x') : rawcat x' ≤ rawcat x := by
  rw [rawcat, rawcat]
  exact Int.toNat_le_toNat (Int.floor_mono (one_div_le_one_div_of_le hx0 hle))

-- `T` is monotone.
theorem T_mono {a b : ℕ} (hab : a ≤ b) : (T a : ℝ) ≤ (T b : ℝ) := by
  have h : T a ≤ T b := by
    unfold T
    rw [← Finset.sum_range_add_sum_Ico _ hab]
    have : (0 : ℚ) ≤ ∑ j ∈ Finset.Ico a b, (1 : ℚ) / (syl (j + 1)) :=
      Finset.sum_nonneg (fun j _ => by positivity)
    linarith
  exact_mod_cast h

-- Two steps of `T`: `T t + (1 + 1/(k+1))·(1/k) = T (t+2)` where `k = syl (t+1)`.
theorem T_step2 (t : ℕ) :
    (T t : ℝ) + (1 + 1 / ((syl (t + 1) : ℝ) + 1)) * (1 / ((syl (t + 1)) : ℝ))
      = (T (t + 2) : ℝ) := by
  have h1 : (T (t + 2) : ℝ) = (T t : ℝ) + 1 / (syl (t + 1) : ℝ) + 1 / (syl (t + 2) : ℝ) := by
    have h0 : T (t + 2) = T t + 1 / (syl (t + 1)) + 1 / (syl (t + 2)) := by
      unfold T; rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [h0]; push_cast; ring
  have hs2 : (syl (t + 2) : ℝ) = (syl (t + 1) : ℝ) * ((syl (t + 1) : ℝ) + 1) := by
    have : syl (t + 2) = syl (t + 1) * (syl (t + 1) + 1) := rfl
    rw [this]; push_cast; ring
  have hk0 : (0 : ℝ) < (syl (t + 1) : ℝ) := by exact_mod_cast syl_pos t
  rw [h1, hs2]; field_simp; ring

-- For case 3a: `T c + (1/(M-1))·(1/syl c)` is monotone in `c` while `syl c ≤ M-1`.
theorem T_aux_mono (M a : ℕ) (ha1 : 1 ≤ a) (hM1 : (0 : ℝ) < (M : ℝ) - 1) :
    ∀ b, a ≤ b → (∀ m, a ≤ m → m < b → syl m ≤ M - 1) →
    (T a : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl a))
      ≤ (T b : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl b)) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ c hac ih =>
    intro hsyl
    have ih' := ih (fun m ham hmc => hsyl m ham (by omega))
    -- c ≥ 1 (since a ≤ c, 1 ≤ a), so write c = d + 1 to let `syl` reduce
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show c ≠ 0 by omega)
    have hsc0 : (0 : ℝ) < (syl (d + 1) : ℝ) := by exact_mod_cast syl_pos d
    have hsc1 : (0 : ℝ) < (syl (d + 1) : ℝ) + 1 := by linarith
    have hscM : (syl (d + 1) : ℝ) ≤ (M : ℝ) - 1 := by
      have hnat : syl (d + 1) ≤ M - 1 := hsyl (d + 1) hac (by omega)
      have hM2 : 1 ≤ M := by
        have : (1 : ℝ) ≤ (M : ℝ) := by linarith [hM1]
        exact_mod_cast this
      have hcast : (syl (d + 1) : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [Nat.cast_sub hM2] at hcast; push_cast at hcast; linarith
    have hT : (T (d + 1 + 1) : ℝ) = (T (d + 1) : ℝ) + 1 / (syl (d + 1 + 1) : ℝ) := by
      have h0 : T (d + 1 + 1) = T (d + 1) + 1 / (syl (d + 1 + 1)) := by
        unfold T; rw [Finset.sum_range_succ]
      rw [h0]; push_cast; ring
    have hs : (syl (d + 1 + 1) : ℝ) = (syl (d + 1) : ℝ) * ((syl (d + 1) : ℝ) + 1) := by
      have : syl (d + 1 + 1) = syl (d + 1) * (syl (d + 1) + 1) := rfl
      rw [this]; push_cast; ring
    have hDne := ne_of_gt hM1
    have hstep : (T (d + 1) : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl (d + 1)))
        ≤ (T (d + 1 + 1) : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl (d + 1 + 1))) := by
      rw [hT, hs]
      have hcore : (1 / ((M : ℝ) - 1)) * (1 / (syl (d + 1) : ℝ))
          ≤ 1 / ((syl (d + 1) : ℝ) * ((syl (d + 1) : ℝ) + 1))
            + (1 / ((M : ℝ) - 1)) * (1 / ((syl (d + 1) : ℝ) * ((syl (d + 1) : ℝ) + 1))) := by
        rw [← sub_nonneg]
        have e : 1 / ((syl (d + 1) : ℝ) * ((syl (d + 1) : ℝ) + 1))
              + (1 / ((M : ℝ) - 1)) * (1 / ((syl (d + 1) : ℝ) * ((syl (d + 1) : ℝ) + 1)))
              - (1 / ((M : ℝ) - 1)) * (1 / (syl (d + 1) : ℝ))
            = ((M : ℝ) - (syl (d + 1) : ℝ) - 1)
                / (((M : ℝ) - 1) * (syl (d + 1) : ℝ) * ((syl (d + 1) : ℝ) + 1)) := by
          field_simp; ring
        rw [e]
        exact div_nonneg (by linarith [hscM]) (le_of_lt (mul_pos (mul_pos hM1 hsc0) hsc1))
      linarith [hcore]
    linarith [ih', hstep]

-- Per-item bound for case 3b: every tail item weighs at most (1 + 1/(k+1))·size.
theorem wh_tail_le (M k : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hkM : (k : ℝ) + 1 ≤ (M : ℝ) - 1) (hM1 : (0 : ℝ) < (M : ℝ) - 1)
    (hc : k + 1 ≤ rawcat x) :
    wh M x ≤ (1 + 1 / ((k : ℝ) + 1)) * x := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hexp : (1 + 1 / ((k : ℝ) + 1)) = ((k : ℝ) + 2) / ((k : ℝ) + 1) := by field_simp; ring
  by_cases hb : x ≤ 1 / (M : ℝ)
  · rw [wh, if_pos hb]
    have hratio : (M : ℝ) / ((M : ℝ) - 1) ≤ 1 + 1 / ((k : ℝ) + 1) := by
      rw [hexp, div_le_div_iff₀ hM1 hk1]; nlinarith [hkM]
    calc (M : ℝ) * x / ((M : ℝ) - 1) = ((M : ℝ) / ((M : ℝ) - 1)) * x := by ring
      _ ≤ (1 + 1 / ((k : ℝ) + 1)) * x := mul_le_mul_of_nonneg_right hratio hx0.le
  · rw [wh, if_neg hb]
    have hck : (k : ℝ) + 1 ≤ (rawcat x : ℝ) := by exact_mod_cast hc
    obtain ⟨hb1, hb2⟩ := rawcat_bounds x (rawcat x) hx0 hx1 rfl
    have hcpos : (0 : ℝ) < (rawcat x : ℝ) := by linarith
    change (1 : ℝ) / (rawcat x : ℝ) ≤ (1 + 1 / ((k : ℝ) + 1)) * x
    have hxc : 1 / ((rawcat x : ℝ) + 1) < x := by
      rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hx0] at hb2; nlinarith [hb2]
    have hA : (1 : ℝ) / (rawcat x : ℝ) ≤ (1 + 1 / ((k : ℝ) + 1)) / ((rawcat x : ℝ) + 1) := by
      rw [div_le_div_iff₀ hcpos (by positivity), one_mul, add_mul, one_mul]
      have hsub : (1 : ℝ) ≤ 1 / ((k : ℝ) + 1) * (rawcat x : ℝ) := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hk1, one_mul]; exact hck
      linarith [hsub]
    have hB : (1 + 1 / ((k : ℝ) + 1)) / ((rawcat x : ℝ) + 1) ≤ (1 + 1 / ((k : ℝ) + 1)) * x := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hxc.le (by positivity)
    linarith [hA, hB]

-- For an early item (`syl (j+1) < M`), its size exceeds `1/(syl(j+1)+1)` and its
-- harmonic weight is exactly `1/syl(j+1)` (it lands in the `else` branch of `wh`).
theorem elem_facts (M j : ℕ) (x : ℝ)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hrc : rawcat x = syl (j + 1)) (hk : syl (j + 1) < M) :
    (1 : ℝ) / (syl (j + 1) + 1) ≤ x ∧ wh M x = (1 : ℝ) / (syl (j + 1)) := by
  set k := syl (j + 1) with hkdef
  obtain ⟨hb1, hb2⟩ := rawcat_bounds x k hx0 hx1 hrc
  have hkpos : (0 : ℝ) < k := by
    have hk1 : 0 < k := by rw [hkdef]; exact syl_pos j
    exact_mod_cast hk1
  have hxgt : 1 / ((k : ℝ) + 1) < x := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hx0] at hb2
    nlinarith [hb2]
  have hkM : (k : ℝ) + 1 ≤ M := by exact_mod_cast (by omega : k + 1 ≤ M)
  have hrecip : 1 / (M : ℝ) ≤ 1 / ((k : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hkM
  have hcond : ¬ x ≤ 1 / (M : ℝ) := by push Not; linarith
  refine ⟨le_of_lt hxgt, ?_⟩
  rw [wh, if_neg hcond]
  have hfloor : (⌊1 / x⌋.toNat : ℝ) = (k : ℝ) := by
    rw [rawcat] at hrc; exact_mod_cast hrc
  rw [hfloor]

-- A list's sum equals the `Finset.range` sum of its (defaulted) entries.
theorem list_sum_eq_range (l : List ℝ) :
    l.sum = ∑ j ∈ Finset.range l.length, l.getD j 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.sum_cons, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring

theorem harmonic_bound_helper (M i t : ℕ) (y : List ℝ)
  (h : HarmonicBoundPreconds M y)
  (hi1 : i ≥ 2) (hi2 : syl (i - 1) < M ∧ M ≤ syl i)
  (hySort : y.SortedGE)
  (ht1 : t ≤ y.length) (ht2 : t + 1 ≤ i)
  (ht3 : ∀ j, (hj : j < t) → rawcat (y[j]'(by omega)) = syl (j + 1))
  (ht4 : (h : t + 1 ≤ y.length ∧ t + 1 ≤ i - 1)
    → rawcat (y[t]'(by omega)) ≠ syl (t + 1))
  : (y.map (wh M)).sum ≤ T i + (1 / (M - 1)) / (syl i) := by
  -- Each of the first `t` items has size > 1/(syl(j+1)+1) and weight 1/syl(j+1),
  -- because `syl(j+1) ≤ syl(i-1) < M` puts it in the `else` branch of `wh`.
  have hper : ∀ j ∈ Finset.range t,
      (1 : ℝ) / (syl (j + 1) + 1) ≤ y.getD j 0
        ∧ wh M (y.getD j 0) = (1 : ℝ) / (syl (j + 1)) := by
    intro j hjmem
    have hj : j < t := Finset.mem_range.mp hjmem
    have hjlen : j < y.length := by omega
    rw [List.getD_eq_getElem y 0 hjlen]
    obtain ⟨hx0, hx1⟩ := h.hyb _ (List.getElem_mem hjlen)
    have hrc : rawcat (y[j]'hjlen) = syl (j + 1) := ht3 j hj
    have hk : syl (j + 1) < M :=
      lt_of_le_of_lt (syl_le (by omega : j + 1 ≤ i - 1)) hi2.1
    exact elem_facts M j _ hx0 hx1 hrc hk
  -- (1) the first `t` item sizes sum to more than `T2 t`
  have hsum_ge : (T2 t : ℝ) ≤ ∑ j ∈ Finset.range t, y.getD j 0 := by
    have hcast : (T2 t : ℝ) = ∑ j ∈ Finset.range t, (1 : ℝ) / (syl (j + 1) + 1) := by
      rw [T2, Rat.cast_sum]; exact Finset.sum_congr rfl (fun j _ => by push_cast; ring)
    rw [hcast]
    exact Finset.sum_le_sum (fun j hjmem => (hper j hjmem).1)
  -- (2) the first `t` item weights sum to exactly `T t`
  have hsum_eq : (∑ j ∈ Finset.range t, wh M (y.getD j 0)) = (T t : ℝ) := by
    have hcast : (T t : ℝ) = ∑ j ∈ Finset.range t, (1 : ℝ) / (syl (j + 1)) := by
      rw [T, Rat.cast_sum]; exact Finset.sum_congr rfl (fun j _ => by push_cast; ring)
    rw [hcast]
    exact Finset.sum_congr rfl (fun j hjmem => (hper j hjmem).2)
  -- (3) the remaining items `[t, n)` sum to at most `1/syl(t+1)`, since the head
  -- already accounts for `T2 t = 1 - 1/syl(t+1)` of the total mass `≤ 1`.
  have hbridge := list_sum_eq_range y
  set n := y.length with hn
  have hsplit :
      ∑ j ∈ Finset.range n, y.getD j 0
        = (∑ j ∈ Finset.range t, y.getD j 0)
          + ∑ j ∈ Finset.Ico t n, y.getD j 0 :=
    (Finset.sum_range_add_sum_Ico _ ht1).symm
  have hT2R : (T2 t : ℝ) = 1 - 1 / (syl (t + 1)) := by rw [T2_simp]; push_cast; ring
  have htail : ∑ j ∈ Finset.Ico t n, y.getD j 0 ≤ 1 / (syl (t + 1)) := by
    have hySum := h.hySum
    linarith [hsum_ge]
  -- weights of the whole list as a range-sum, then split head/tail (case-independent)
  have hwsum : (y.map (wh M)).sum = ∑ j ∈ Finset.range n, wh M (y.getD j 0) := by
    rw [list_sum_eq_range (y.map (wh M))]
    have hlen : (y.map (wh M)).length = n := by rw [List.length_map, ← hn]
    rw [hlen]
    apply Finset.sum_congr rfl
    intro j hjmem
    have hjy : j < y.length := by have := Finset.mem_range.mp hjmem; omega
    rw [List.getD_eq_getElem (y.map (wh M)) 0 (by rw [List.length_map]; exact hjy),
        List.getElem_map, ← List.getD_eq_getElem y 0 hjy]
  have hwsplit : ∑ j ∈ Finset.range n, wh M (y.getD j 0)
      = (∑ j ∈ Finset.range t, wh M (y.getD j 0))
        + ∑ j ∈ Finset.Ico t n, wh M (y.getD j 0) :=
    (Finset.sum_range_add_sum_Ico _ ht1).symm
  -- Three exhaustive cases, using `t ≤ i-1` (ht2) and `t ≤ n` (ht1).
  rcases Nat.eq_or_lt_of_le (show t ≤ i - 1 by omega) with hci | hci
  · -- Case t = i - 1: every tail item is ≤ 1/M, so its weight is (M/(M-1))·size.
    have hti : t + 1 = i := by omega
    rw [hti] at htail          -- htail : tail-size-sum ≤ 1 / syl i
    have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h.hM
    have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
    have hsyli : (0 : ℝ) < (syl i : ℝ) := by
      have : 0 < syl i := by have := syl_pos (i - 1); omega
      exact_mod_cast this
    -- (b) each tail item lands in the `then` branch, weight = (M/(M-1))·size
    have htailw : ∑ j ∈ Finset.Ico t n, wh M (y.getD j 0)
        = ((M : ℝ) / (M - 1)) * ∑ j ∈ Finset.Ico t n, y.getD j 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hjmem
      obtain ⟨hjt, hjn⟩ := Finset.mem_Ico.mp hjmem
      have hjy : j < y.length := by omega
      have hle_tail : y.getD j 0 ≤ ∑ k ∈ Finset.Ico t n, y.getD k 0 := by
        apply Finset.single_le_sum (f := fun k => y.getD k 0) _ hjmem
        intro k hk
        obtain ⟨hkt, hkn⟩ := Finset.mem_Ico.mp hk
        change (0 : ℝ) ≤ y.getD k 0
        rw [List.getD_eq_getElem y 0 (by omega)]
        exact le_of_lt (h.hyb _ (List.getElem_mem _)).1
      have hsyliM : (1 : ℝ) / (syl i) ≤ 1 / M :=
        one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < M)) (by exact_mod_cast hi2.2)
      have hxleM : y.getD j 0 ≤ 1 / (M : ℝ) := by linarith [hle_tail, htail, hsyliM]
      rw [wh, if_pos hxleM]; ring
    have htailw_le : ∑ j ∈ Finset.Ico t n, wh M (y.getD j 0)
        ≤ ((M : ℝ) / (M - 1)) * (1 / (syl i)) := by
      rw [htailw]
      exact mul_le_mul_of_nonneg_left htail (by positivity)
    -- (c) the algebraic identity that makes the two sides meet exactly
    have halg : ((M : ℝ) / (M - 1)) * (1 / (syl i))
        = 1 / (syl i) + (1 / ((M : ℝ) - 1)) / (syl i) := by
      field_simp; ring
    -- (d) T i = T t + 1/syl i  (since i = t + 1)
    have hTrel_q : T i = T t + 1 / (syl i) := by
      rw [show i = t + 1 from hti.symm]; unfold T; rw [Finset.sum_range_succ]
    have hTrel : (T i : ℝ) = (T t : ℝ) + 1 / (syl i) := by
      rw [hTrel_q]; push_cast; ring
    rw [hwsum, hwsplit, hsum_eq]
    linarith [htailw_le, halg, hTrel]
  · rcases Nat.eq_or_lt_of_le ht1 with hcn | hcn
    · -- Case t = n: the tail `[t,n)` is empty, so total weight = head weight = T t ≤ T i.
      -- total weight collapses to the head sum
      rw [hwsum, ← hcn, hsum_eq]
      -- T t ≤ T i since range t ⊆ range i, and the extra term is nonnegative
      have hTle : (T t : ℝ) ≤ (T i : ℝ) := by
        have hti' : t ≤ i := by omega
        have hstep : T t ≤ T i := by
          unfold T
          rw [← Finset.sum_range_add_sum_Ico _ hti']
          have hnn : (0 : ℚ) ≤ ∑ j ∈ Finset.Ico t i, (1 : ℚ) / (syl (j + 1)) :=
            Finset.sum_nonneg (fun j _ => by positivity)
          linarith
        exact_mod_cast hstep
      have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
        have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h.hM
        linarith
      have hsyli : (0 : ℝ) < (syl i : ℝ) := by
        have : 0 < syl i := by have := syl_pos (i - 1); omega
        exact_mod_cast this
      have hpos : (0 : ℝ) ≤ (1 / ((M : ℝ) - 1)) / (syl i) :=
        div_nonneg (div_nonneg zero_le_one (le_of_lt hM1)) (le_of_lt hsyli)
      linarith [hTle, hpos]
    · -- Case t < i - 1 ∧ t < n
      -- Every tail item has raw category ≥ syl(t+1) + 1:
      -- item t via `ht4` (category ≠ syl(t+1)) + the size bound; later items via sortedness.
      have htn : t < y.length := by omega
      have hnonneg : ∀ k ∈ Finset.Ico t n, 0 ≤ y.getD k 0 := by
        intro k hk
        obtain ⟨_, hkn⟩ := Finset.mem_Ico.mp hk
        rw [List.getD_eq_getElem y 0 (by omega)]
        exact le_of_lt (h.hyb _ (List.getElem_mem _)).1
      have hmemt : t ∈ Finset.Ico t n := Finset.mem_Ico.mpr ⟨le_refl t, by omega⟩
      have hyt_le : y.getD t 0 ≤ 1 / (syl (t + 1) : ℝ) :=
        le_trans (Finset.single_le_sum hnonneg hmemt) htail
      have hyt0 : 0 < y.getD t 0 := by
        rw [List.getD_eq_getElem y 0 htn]; exact (h.hyb _ (List.getElem_mem _)).1
      have hge_t : syl (t + 1) ≤ rawcat (y.getD t 0) :=
        rawcat_ge _ _ hyt0 hyt_le (syl_pos t)
      have hne_t : rawcat (y.getD t 0) ≠ syl (t + 1) := by
        rw [List.getD_eq_getElem y 0 htn]
        exact ht4 ⟨by omega, by omega⟩
      have hrt_t : syl (t + 1) + 1 ≤ rawcat (y.getD t 0) := by omega
      have hcat_ge : ∀ j ∈ Finset.Ico t n, syl (t + 1) + 1 ≤ rawcat (y.getD j 0) := by
        intro j hjmem
        obtain ⟨hjt, hjn⟩ := Finset.mem_Ico.mp hjmem
        have hjy : j < y.length := by omega
        have hyj0 : 0 < y.getD j 0 := by
          rw [List.getD_eq_getElem y 0 hjy]; exact (h.hyb _ (List.getElem_mem _)).1
        have hyj_le : y.getD j 0 ≤ y.getD t 0 := by
          rw [List.getD_eq_getElem y 0 hjy, List.getD_eq_getElem y 0 htn]
          have := hySort.antitone_get (show (⟨t, htn⟩ : Fin y.length) ≤ ⟨j, hjy⟩ from hjt)
          simpa [List.get_eq_getElem] using this
        have := rawcat_anti (y.getD j 0) (y.getD t 0) hyj0 hyj_le
        omega
      -- syl(t+1) < M throughout the tail
      have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h.hM
        linarith
      have hsyli : (0 : ℝ) < (syl i : ℝ) := by
        have : 0 < syl i := by have := syl_pos (i - 1); omega
        exact_mod_cast this
      have hpos : (0 : ℝ) ≤ (1 / ((M : ℝ) - 1)) / (syl i) :=
        div_nonneg (div_nonneg zero_le_one hM1.le) hsyli.le
      rcases Nat.lt_or_ge (syl (t + 1)) (M - 1) with h3b | h3a
      · -- Case 3b: syl(t+1) ≤ M-2. Bound each item's weight by (1+1/(k+1))·size.
        have hkM : ((syl (t + 1)) : ℝ) + 1 ≤ (M : ℝ) - 1 := by
          have hn2 : syl (t + 1) + 2 ≤ M := by omega
          have : ((syl (t + 1)) : ℝ) + 2 ≤ (M : ℝ) := by exact_mod_cast hn2
          linarith
        have htail_w : ∑ j ∈ Finset.Ico t n, wh M (y.getD j 0)
            ≤ (1 + 1 / ((syl (t + 1) : ℝ) + 1)) * (1 / (syl (t + 1))) := by
          have hpi : ∀ j ∈ Finset.Ico t n,
              wh M (y.getD j 0) ≤ (1 + 1 / ((syl (t + 1) : ℝ) + 1)) * (y.getD j 0) := by
            intro j hjmem
            obtain ⟨hjt, hjn⟩ := Finset.mem_Ico.mp hjmem
            have hjy : j < y.length := by omega
            have hmem : y.getD j 0 ∈ y := by
              rw [List.getD_eq_getElem y 0 hjy]; exact List.getElem_mem _
            obtain ⟨hx0, hx1⟩ := h.hyb _ hmem
            exact wh_tail_le M (syl (t + 1)) _ hx0 hx1 hkM hM1 (hcat_ge j hjmem)
          calc ∑ j ∈ Finset.Ico t n, wh M (y.getD j 0)
              ≤ ∑ j ∈ Finset.Ico t n, (1 + 1 / ((syl (t + 1) : ℝ) + 1)) * (y.getD j 0) :=
                Finset.sum_le_sum hpi
            _ = (1 + 1 / ((syl (t + 1) : ℝ) + 1)) * ∑ j ∈ Finset.Ico t n, y.getD j 0 := by
                rw [Finset.mul_sum]
            _ ≤ (1 + 1 / ((syl (t + 1) : ℝ) + 1)) * (1 / (syl (t + 1))) :=
                mul_le_mul_of_nonneg_left htail (by positivity)
        rw [hwsum, hwsplit, hsum_eq]
        have hmono := T_mono (show t + 2 ≤ i by omega)
        linarith [htail_w, T_step2 t, hmono, hpos]
      · -- Case 3a: syl(t+1) = M-1, so every tail item is category M (then-branch).
        have hi21 := hi2.1
        have hklt : syl (t + 1) < M := lt_of_le_of_lt (syl_le (by omega : t + 1 ≤ i - 1)) hi2.1
        have h3a' : syl (t + 1) = M - 1 := by omega
        have hk0 : (0 : ℝ) < (syl (t + 1) : ℝ) := by exact_mod_cast syl_pos t
        have hMpos : (0 : ℝ) < (M : ℝ) := by linarith [hM1]
        -- each tail item has weight exactly (M/(M-1))·size
        have htailw : ∑ j ∈ Finset.Ico t n, wh M (y.getD j 0)
            = ((M : ℝ) / ((M : ℝ) - 1)) * ∑ j ∈ Finset.Ico t n, y.getD j 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hjmem
          obtain ⟨hjt, hjn⟩ := Finset.mem_Ico.mp hjmem
          have hjy : j < y.length := by omega
          have hmem : y.getD j 0 ∈ y := by
            rw [List.getD_eq_getElem y 0 hjy]; exact List.getElem_mem _
          obtain ⟨hx0, hx1⟩ := h.hyb _ hmem
          have hcatM : M ≤ rawcat (y.getD j 0) := by have := hcat_ge j hjmem; omega
          have hxM : y.getD j 0 ≤ 1 / (M : ℝ) := by
            obtain ⟨hb1, _⟩ := rawcat_bounds (y.getD j 0) (rawcat (y.getD j 0)) hx0 hx1 rfl
            have hMc : (M : ℝ) ≤ 1 / (y.getD j 0) := le_trans (by exact_mod_cast hcatM) hb1
            rw [le_div_iff₀ hMpos]
            rw [le_div_iff₀ hx0] at hMc
            nlinarith [hMc]
          rw [wh, if_pos hxM]; ring
        rw [hwsum, hwsplit, hsum_eq, htailw]
        have htailsize : ((M : ℝ) / ((M : ℝ) - 1)) * ∑ j ∈ Finset.Ico t n, y.getD j 0
            ≤ ((M : ℝ) / ((M : ℝ) - 1)) * (1 / (syl (t + 1))) :=
          mul_le_mul_of_nonneg_left htail (div_nonneg (by positivity) hM1.le)
        have hkey : (T (t + 1) : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl (t + 1)))
            ≤ (T i : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl i)) := by
          refine T_aux_mono M (t + 1) (by omega) hM1 i (by omega) ?_
          intro m hm1 hm2
          have hh : syl m ≤ syl (i - 1) := syl_le (by omega)
          omega
        have hTid : (T t : ℝ) + ((M : ℝ) / ((M : ℝ) - 1)) * (1 / (syl (t + 1)))
            = (T (t + 1) : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl (t + 1))) := by
          have hT1 : (T (t + 1) : ℝ) = (T t : ℝ) + 1 / (syl (t + 1)) := by
            have h0 : T (t + 1) = T t + 1 / (syl (t + 1)) := by
              unfold T; rw [Finset.sum_range_succ]
            rw [h0]; push_cast; ring
          rw [hT1]; field_simp; ring
        have hbi : (1 / ((M : ℝ) - 1)) / (syl i) = (1 / ((M : ℝ) - 1)) * (1 / (syl i)) :=
          div_eq_mul_one_div _ _
        linarith [htailsize, hkey, hTid, hbi]

theorem harmonic_bound (M : ℕ) (y : List ℝ) (h : HarmonicBoundPreconds M y)
  : (y.map (wh M)).sum ≤ Q M := by
  classical
  have hM2 := h.hM
  -- Sorting preserves the weight sum, so work with a sorted permutation `y'`.
  set y' := y.mergeSort (fun a b => decide (a ≥ b)) with hy'
  have hperm : List.Perm y' y := List.mergeSort_perm y _
  have hsort : y'.SortedGE := List.sortedGE_mergeSort
  have hsum_eq : (y.map (wh M)).sum = (y'.map (wh M)).sum :=
    (List.Perm.sum_eq (hperm.map (wh M))).symm
  have h' : HarmonicBoundPreconds M y' :=
    { hM := h.hM
      hyb := fun z hz => h.hyb z (hperm.mem_iff.mp hz)
      hySum := by rw [List.Perm.sum_eq hperm]; exact h.hySum }
  -- `i = syl_inv_fast M` sits in the Sylvester sandwich `syl (i-1) < M ≤ syl i`.
  obtain ⟨hMi, hlt_i⟩ := syl_inv_fast_spec M
  set i := syl_inv_fast M with hi
  have hi1 : 2 ≤ i := by
    by_contra hc
    push Not at hc
    have hle : syl i ≤ syl 1 := syl_le (by omega)
    have : syl 1 = 1 := rfl
    omega
  have hi2 : syl (i - 1) < M ∧ M ≤ syl i := ⟨hlt_i (i - 1) (by omega), hMi⟩
  -- `t` = the largest prefix (within `min |y'| (i-1)`) whose categories match `syl`.
  set P : ℕ → Prop := fun s => ∀ j, j < s → rawcat (y'.getD j 0) = syl (j + 1) with hP
  set b := min y'.length (i - 1) with hb
  set t := Nat.findGreatest P b with ht
  have hP0 : P 0 := fun j hj => absurd hj (Nat.not_lt_zero j)
  have hPt : P t := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have htb : t ≤ b := Nat.findGreatest_le _
  have ht1 : t ≤ y'.length := le_trans htb (min_le_left _ _)
  have ht2 : t + 1 ≤ i := by have := le_trans htb (min_le_right _ _); omega
  -- Convert `Q M` to the real-valued form the helper produces.
  have hQcast : ((Q M : ℚ) : ℝ) = (T i : ℝ) + (1 / ((M : ℝ) - 1)) / ((syl i) : ℝ) := by
    unfold Q; rw [← hi]; push_cast; ring
  rw [hsum_eq]
  refine le_trans (harmonic_bound_helper M i t y' h' hi1 hi2 hsort ht1 ht2 ?_ ?_)
    (le_of_eq hQcast.symm)
  · -- ht3 : the first `t` categories match `syl`
    intro j hj
    have hh := hPt j hj
    rw [List.getD_eq_getElem y' 0 (by omega)] at hh
    exact hh
  · -- ht4 : the prefix breaks at index `t`
    intro hcond heq
    have hnotP : ¬ P (t + 1) :=
      Nat.findGreatest_is_greatest
        (lt_of_le_of_lt (le_of_eq ht.symm) (Nat.lt_succ_self t))
        (by rw [hb]; exact le_min hcond.1 hcond.2)
    apply hnotP
    intro j hj
    rcases (Nat.lt_succ_iff.mp hj).lt_or_eq with hjt | hjeq
    · exact hPt j hjt
    · subst hjeq
      rw [List.getD_eq_getElem y' 0 (by omega)]
      exact heq
