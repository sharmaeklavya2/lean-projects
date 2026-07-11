module

public import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.List.GetD

public import BinPack.Harmonic.Core
import BinPack.Harmonic.Syl
import BinPack.Common

/-! Here we prove an upper-bound on the total harmonic weight
of a set of items that fit into a bin. -/

/- Definitions -/

def T2 (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, 1 / (syl (i + 1) + 1)

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

/-- `syl (n+1) = syl n * (syl n + 1)` for `n ≥ 1` (the recursion, usable for an
opaque `n`; `rfl` only fires once `n` is syntactically a successor). -/
theorem syl_succ {n : ℕ} (hn : 1 ≤ n) : syl (n + 1) = syl n * (syl n + 1) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rfl

/-- One more term of `T`. -/
theorem T_succ (n : ℕ) : T (n + 1) = T n + 1 / (syl (n + 1)) := by
  unfold T; rw [Finset.sum_range_succ]

/-- `T` is (weakly) monotone: every summand `1/syl(i+1)` is nonnegative. -/
theorem T_mono {a b : ℕ} (h : a ≤ b) : T a ≤ T b := by
  induction b, h using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih =>
    have : (0 : ℚ) ≤ 1 / (syl (n + 1)) := by positivity
    rw [T_succ]; linarith

/-- Prefix sum of a mapped list, pointwise-identified with a `Finset.range` sum. -/
theorem take_map_sum (F : ℝ → ℝ) :
    ∀ (L : List ℝ) (t : ℕ) (_ht : t ≤ L.length) (g : ℕ → ℝ)
      (_h : ∀ k (hk : k < t), F (L[k]'(by omega)) = g k),
    ((L.take t).map F).sum = ∑ k ∈ Finset.range t, g k := by
  intro L
  induction L with
  | nil => intro t ht g h; simp only [List.length_nil, Nat.le_zero] at ht; subst ht; simp
  | cons x L' ih =>
    intro t ht g h
    cases t with
    | zero => simp
    | succ s =>
      have hx : F x = g 0 := h 0 (by omega)
      have hrec : ((L'.take s).map F).sum = ∑ k ∈ Finset.range s, g (k + 1) := by
        apply ih s (by simpa using Nat.succ_le_succ_iff.mp ht) (fun k => g (k + 1))
        intro k hk
        have := h (k + 1) (by omega)
        simpa using this
      rw [List.take_succ_cons, List.map_cons, List.sum_cons, hrec, hx,
          Finset.sum_range_succ', add_comm]

-- `T c + (1/(M-1))·(1/syl c)` is monotone in `c` while `syl c ≤ M-1`.
theorem T_aux_mono (M a : ℕ) (ha1 : 1 ≤ a) (hM1 : (0 : ℝ) < (M : ℝ) - 1) :
    ∀ b, a ≤ b → (∀ m, a ≤ m → m < b → syl m ≤ M - 1) →
    (T a : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl a))
      ≤ (T b : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl b)) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ n hn ih =>
    intro hcond
    have hcondn : ∀ m, a ≤ m → m < n → syl m ≤ M - 1 :=
      fun m hm hmn => hcond m hm (by omega)
    have h1 := ih hcondn
    -- single step `f n ≤ f (n+1)`
    have hn1 : 1 ≤ n := le_trans ha1 hn
    have hsn_pos : (0 : ℝ) < (syl n : ℝ) := by
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact_mod_cast syl_pos p
    have hsn1 : (syl (n + 1) : ℝ) = (syl n : ℝ) * ((syl n : ℝ) + 1) := by
      rw [syl_succ hn1]; push_cast; ring
    have hsnpos1 : (0 : ℝ) < (syl n : ℝ) + 1 := by linarith
    have hM2 : 1 ≤ M := by
      have : (1 : ℝ) < (M : ℝ) := by linarith
      exact_mod_cast le_of_lt this
    have hsleM : (syl n : ℝ) ≤ (M : ℝ) - 1 := by
      have hh : syl n ≤ M - 1 := hcond n hn (by omega)
      have hc : (syl n : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hh
      rw [Nat.cast_sub hM2] at hc; push_cast at hc; linarith
    have hstep : (T n : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl n))
        ≤ (T (n + 1) : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl (n + 1))) := by
      rw [T_succ]; push_cast; rw [hsn1]
      set s := (syl n : ℝ) with hs
      have e1 : (1 / ((M : ℝ) - 1)) * (1 / s) = (s + 1) / (((M : ℝ) - 1) * (s * (s + 1))) := by
        field_simp
      have e2 : 1 / (s * (s + 1)) + (1 / ((M : ℝ) - 1)) * (1 / (s * (s + 1)))
          = (((M : ℝ) - 1) + 1) / (((M : ℝ) - 1) * (s * (s + 1))) := by
        field_simp
      have hscalar : (1 / ((M : ℝ) - 1)) * (1 / s)
          ≤ 1 / (s * (s + 1)) + (1 / ((M : ℝ) - 1)) * (1 / (s * (s + 1))) := by
        rw [e1, e2]; gcongr
      linarith
    linarith

/-- Multiply a mapped list-sum by a constant. -/
private theorem sum_map_smul (c : ℝ) (L : List ℝ) :
    (L.map (fun z => c * z)).sum = c * L.sum := by
  induction L with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

/-- If `x ≤ 1/c` (and `c ≥ 1`), then `⌊1/x⌋ ≥ c`, i.e. `rawcat x ≥ c`. -/
private theorem rawcat_ge_of_le (x : ℝ) (hx0 : 0 < x) (c : ℕ) (hc1 : 1 ≤ c)
    (hc : x ≤ 1 / (c : ℝ)) : c ≤ rawcat x := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc1
  have hcx : (c : ℝ) ≤ 1 / x := by
    rw [le_div_iff₀ hx0]; rw [le_div_iff₀ hcR] at hc; linarith
  have hfloor : (c : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.mpr (by exact_mod_cast hcx)
  have := Int.toNat_le_toNat hfloor
  simpa [rawcat, Int.toNat_natCast] using this

/-- From `rawcat x = r`, the size exceeds `1/(r+1)`. -/
private theorem size_gt (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (r : ℕ) (hr : rawcat x = r) :
    1 / ((r : ℝ) + 1) < x := by
  have h1x : (1 : ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx0, one_mul]; exact hx1
  have hfnn : (0 : ℤ) ≤ ⌊1 / x⌋ := Int.floor_nonneg.mpr (by linarith)
  have hfloor : ⌊1 / x⌋ = (r : ℤ) := by rw [← hr]; exact (Int.toNat_of_nonneg hfnn).symm
  have hlt : 1 / x < (r : ℝ) + 1 := by
    have := Int.lt_floor_add_one (1 / x); rw [hfloor] at this; push_cast at this; linarith
  have hxr : 1 < ((r : ℝ) + 1) * x := by
    calc (1 : ℝ) = (1 / x) * x := by field_simp
      _ < ((r : ℝ) + 1) * x := by apply mul_lt_mul_of_pos_right hlt hx0
  rw [div_lt_iff₀ (by positivity)]; linarith

/-- `rawcat` is antitone in the size. -/
private theorem rawcat_anti (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : rawcat b ≤ rawcat a := by
  have hle : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
  exact Int.toNat_le_toNat (Int.floor_le_floor hle)

/-! ## Per-item category facts (over `ℝ`) -/

/-- `⌊1/x⌋.toNat` cast to `ℝ` is `≤ 1/x`, for `0 < x ≤ 1`. -/
public theorem toNat_floor_le (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ((⌊1 / x⌋).toNat : ℝ) ≤ 1 / x := by
  have h1x : (1 : ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx0, one_mul]; exact hx1
  have hfnn : (0 : ℤ) ≤ ⌊1 / x⌋ := by
    have : (1 : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.mpr (by exact_mod_cast h1x); omega
  calc ((⌊1 / x⌋).toNat : ℝ) = (⌊1 / x⌋ : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hfnn
    _ ≤ 1 / x := Int.floor_le (1 / x)

/-- A "small" category-`k` item (`k < M`) has size `≤ 1/k` and weight exactly `1/k`. -/
public theorem cat_lt_M_facts (M : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (k : ℕ)
    (hk : cat M x = k) (hkM : k < M) :
    x ≤ 1 / (k : ℝ) ∧ wh M x = 1 / (k : ℝ) := by
  have h1x : (1 : ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx0, one_mul]; exact hx1
  have hfloor1 : (1 : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.mpr (by exact_mod_cast h1x)
  have hfnn : (0 : ℤ) ≤ ⌊1 / x⌋ := by omega
  have hrk : (⌊1 / x⌋).toNat = k := by simp only [cat] at hk; omega
  have hfloork : ⌊1 / x⌋ = (k : ℤ) := by rw [← hrk]; exact (Int.toNat_of_nonneg hfnn).symm
  have hk1 : 1 ≤ k := by omega
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  obtain ⟨hlo, hhi⟩ := Int.floor_eq_iff.mp hfloork
  have hloR : (k : ℝ) ≤ 1 / x := by exact_mod_cast hlo
  have hhiR : 1 / x < (k : ℝ) + 1 := by push_cast at hhi; linarith
  have hkM1 : (k : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ M)
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hkR]; rw [le_div_iff₀ hx0] at hloR; linarith
  · have h1xM : 1 / x < (M : ℝ) := by linarith
    have hxgtM : 1 / (M : ℝ) < x := by
      rw [div_lt_iff₀ hMpos, mul_comm]; rw [div_lt_iff₀ hx0] at h1xM; exact h1xM
    rw [wh, if_neg (not_le.mpr hxgtM), hrk]

/-- A "tiny" category-`M` item has size `≤ 1/M` and weight `M/(M-1)·size`. -/
public theorem cat_eq_M_facts (M : ℕ) (hM : 2 ≤ M) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hk : cat M x = M) :
    x ≤ 1 / (M : ℝ) ∧ wh M x = (M : ℝ) / ((M : ℝ) - 1) * x := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hrM : M ≤ (⌊1 / x⌋).toNat := by simp only [cat] at hk; omega
  have hMle : (M : ℝ) ≤ 1 / x :=
    le_trans (by exact_mod_cast hrM) (toNat_floor_le x hx0 hx1)
  have hxM : x ≤ 1 / (M : ℝ) := by
    rw [le_div_iff₀ hMpos]; rw [le_div_iff₀ hx0] at hMle; linarith
  exact ⟨hxM, by rw [wh, if_pos hxM]; ring⟩

/-- Per-item bound for suffix items: an item whose (unclamped) category is `≥ c+1`
has weight at most `max (M/(M-1)) (1 + 1/(c+1))` times its size. -/
private theorem suffix_item_bound (M : ℕ) (hM : 2 ≤ M) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (c : ℕ) (hc1 : 1 ≤ c) (hcx : c + 1 ≤ rawcat x) :
    wh M x ≤ max ((M : ℝ) / ((M : ℝ) - 1)) (1 + 1 / ((c : ℝ) + 1)) * x := by
  have h2R : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hcR : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  set r := rawcat x with hrdef
  have hcateq : cat M x = min M r := rfl
  rcases Nat.lt_or_ge r M with hrM | hrM
  · have hcat : cat M x = r := by rw [hcateq, Nat.min_eq_right (le_of_lt hrM)]
    obtain ⟨_, hwh⟩ := cat_lt_M_facts M x hx0 hx1 r hcat hrM
    rw [hwh]
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have hgt : 1 / ((r : ℝ) + 1) < x := size_gt x hx0 hx1 r rfl
    have hcr : (c : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hcx
    have hmid : 1 / (r : ℝ) ≤ (1 + 1 / ((c : ℝ) + 1)) * (1 / ((r : ℝ) + 1)) := by
      rw [show (1 + 1 / ((c : ℝ) + 1)) * (1 / ((r : ℝ) + 1))
            = (1 + 1 / ((c : ℝ) + 1)) / ((r : ℝ) + 1) from by ring,
          div_le_div_iff₀ hrpos (by positivity)]
      have hkey : (1 : ℝ) ≤ (r : ℝ) * (1 / ((c : ℝ) + 1)) := by
        rw [mul_one_div, le_div_iff₀ hcR]; linarith
      nlinarith [hkey]
    have hB : (0 : ℝ) ≤ 1 + 1 / ((c : ℝ) + 1) := by positivity
    have hmid2 : (1 + 1 / ((c : ℝ) + 1)) * (1 / ((r : ℝ) + 1))
        ≤ (1 + 1 / ((c : ℝ) + 1)) * x := mul_le_mul_of_nonneg_left (le_of_lt hgt) hB
    exact le_trans (le_trans hmid hmid2)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hx0))
  · have hcat : cat M x = M := by rw [hcateq, Nat.min_eq_left hrM]
    obtain ⟨_, hwh⟩ := cat_eq_M_facts M hM x hx0 hx1 hcat
    rw [hwh]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hx0)

theorem harmonic_bound_helper (M i t : ℕ) (y : List ℝ)
  (hM : M ≥ 2) (hyb : ∀ z ∈ y, 0 < z) (hySum : y.sum ≤ 1)
  (hi1 : i ≥ 2) (hi2 : syl (i - 1) < M ∧ M ≤ syl i)
  (hySort : y.SortedGE)
  (ht1 : t ≤ y.length) (ht2 : t + 1 ≤ i)
  (ht3 : ∀ j, (hj : j < t) → rawcat (y[j]'(by omega)) = syl (j + 1))
  (ht4 : (h : t + 1 ≤ y.length ∧ t + 1 ≤ i - 1)
    → rawcat (y[t]'(by omega)) ≠ syl (t + 1))
  : (y.map (wh M)).sum ≤ T i + (1 / (M - 1)) / (syl i) := by
  obtain ⟨hi2a, hi2b⟩ := hi2
  have h2R : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1R : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hMR : (0 : ℝ) < (M : ℝ) := by linarith
  have hyle : ∀ z ∈ y, z ≤ 1 := fun z hz =>
    le_trans (List.single_le_sum (fun a ha => le_of_lt (hyb a ha)) z hz) hySum
  have hsyli_pos : (0 : ℝ) < (syl i : ℝ) := by
    have h1 : 1 ≤ syl i := by
      have := syl_pos (i - 1); rwa [Nat.sub_add_cancel (by omega)] at this
    exact_mod_cast h1
  have hRHS2 : (0 : ℝ) ≤ (1 / ((M : ℝ) - 1)) / (syl i) :=
    div_nonneg (div_nonneg zero_le_one (le_of_lt hM1R)) (le_of_lt hsyli_pos)
  -- Prefix weight is `T t`.
  have hWP : ((y.take t).map (wh M)).sum = (T t : ℝ) := by
    have hpt : ∀ k (hk : k < t), wh M (y[k]'(by omega)) = (1 / (syl (k + 1) : ℝ)) := by
      intro k hk
      have hrawk : rawcat (y[k]'(by omega)) = syl (k + 1) := ht3 k hk
      have hsylk_lt : syl (k + 1) < M := lt_of_le_of_lt (syl_le (by omega)) hi2a
      have hx0 : 0 < y[k]'(by omega) := hyb _ (List.getElem_mem _)
      have hx1 : y[k]'(by omega) ≤ 1 := hyle _ (List.getElem_mem _)
      have hcat : cat M (y[k]'(by omega)) = syl (k + 1) := by
        rw [show cat M (y[k]'(by omega)) = min M (rawcat (y[k]'(by omega))) from rfl, hrawk,
          Nat.min_eq_right (le_of_lt hsylk_lt)]
      exact (cat_lt_M_facts M (y[k]'(by omega)) hx0 hx1 (syl (k + 1)) hcat hsylk_lt).2
    rw [take_map_sum (wh M) y t ht1 (fun k => 1 / (syl (k + 1) : ℝ)) hpt, T]
    push_cast; rfl
  have hWsplit : (y.map (wh M)).sum
      = ((y.take t).map (wh M)).sum + ((y.drop t).map (wh M)).sum := by
    conv_lhs => rw [← List.take_append_drop t y]
    rw [List.map_append, List.sum_append]
  have hsum_split : y.sum = (y.take t).sum + (y.drop t).sum := by
    conv_lhs => rw [← List.take_append_drop t y]
    rw [List.sum_append]
  rw [hWsplit, hWP]
  -- Case split on whether the prefix is the whole list.
  rcases eq_or_lt_of_le ht1 with htn | htn
  · -- Case 2: `t = n`, suffix empty.
    have hdrop0 : ((y.drop t).map (wh M)).sum = 0 := by
      rw [htn, List.drop_length]; simp
    have htT : (T t : ℝ) ≤ (T i : ℝ) := by exact_mod_cast T_mono (by omega : t ≤ i)
    rw [hdrop0]; linarith
  · -- Suffix nonempty.
    have hcs1 : 1 ≤ syl (t + 1) := syl_pos t
    have hcsR : (0 : ℝ) < (syl (t + 1) : ℝ) := by exact_mod_cast hcs1
    -- Prefix size `≥ T2 t`.
    have hT2eq : (T2 t : ℝ) = ∑ k ∈ Finset.range t, (1 / ((syl (k + 1) : ℝ) + 1)) := by
      rw [T2]; push_cast; rfl
    have hPsum : (T2 t : ℝ) ≤ (y.take t).sum := by
      set g : ℕ → ℝ := fun k => if hk : k < t then y[k]'(by omega) else 0 with hg
      have hPeq : (y.take t).sum = ∑ k ∈ Finset.range t, g k := by
        have := take_map_sum id y t ht1 g (fun k hk => by simp [hg, hk])
        simpa using this
      rw [hT2eq, hPeq]
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_range] at hk
      have hgk : g k = y[k]'(by omega) := by simp [hg, hk]
      rw [hgk]
      have hrawk : rawcat (y[k]'(by omega)) = syl (k + 1) := ht3 k hk
      have := size_gt (y[k]'(by omega)) (hyb _ (List.getElem_mem _))
        (hyle _ (List.getElem_mem _)) (syl (k + 1)) hrawk
      push_cast at this ⊢; linarith
    -- Suffix size `≤ 1/syl(t+1)`.
    have hT2simp : (T2 t : ℝ) = 1 - 1 / ((syl (t + 1)) : ℝ) := by
      have h := T2_simp t
      have hc : (T2 t : ℝ) = ((1 - 1 / (syl (t + 1)) : ℚ) : ℝ) := by rw [h]
      rw [hc]; push_cast; ring
    have hSsum : (y.drop t).sum ≤ 1 / ((syl (t + 1)) : ℝ) := by
      have hpge : (1 : ℝ) - 1 / ((syl (t + 1)) : ℝ) ≤ (y.take t).sum := by
        rw [← hT2simp]; exact hPsum
      linarith [hySum, hsum_split]
    -- Sub-case split: `t+1 = i` (Case 1) or `t+1 < i` (Case 3).
    rcases eq_or_lt_of_le ht2 with hti | hti
    · -- Case 1: `t = i-1`; all suffix items have category `M`.
      subst hti
      have hzM : ∀ z ∈ y.drop t, wh M z = (M : ℝ) / ((M : ℝ) - 1) * z := by
        intro z hz
        have hz0 : 0 < z := hyb z (List.mem_of_mem_drop hz)
        have hz1 : z ≤ 1 := hyle z (List.mem_of_mem_drop hz)
        have hzsum : z ≤ (y.drop t).sum :=
          List.single_le_sum (fun a ha => le_of_lt (hyb a (List.mem_of_mem_drop ha))) z hz
        have hsyliM : (M : ℝ) ≤ (syl (t + 1) : ℝ) := by exact_mod_cast hi2b
        have hzle : z ≤ 1 / (M : ℝ) := by
          have hle2 : (y.drop t).sum ≤ 1 / (M : ℝ) :=
            le_trans hSsum (one_div_le_one_div_of_le hMR hsyliM)
          linarith
        have hrawM : M ≤ rawcat z := rawcat_ge_of_le z hz0 M (by omega) hzle
        have hcat : cat M z = M := by
          rw [show cat M z = min M (rawcat z) from rfl, Nat.min_eq_left hrawM]
        exact (cat_eq_M_facts M hM z hz0 hz1 hcat).2
      have hWS : ((y.drop t).map (wh M)).sum = (M : ℝ) / ((M : ℝ) - 1) * (y.drop t).sum := by
        rw [show (y.drop t).map (wh M) = (y.drop t).map (fun z => (M : ℝ) / ((M : ℝ) - 1) * z)
              from List.map_congr_left hzM, sum_map_smul]
      rw [hWS, show (T (t + 1) : ℝ) = (T t : ℝ) + 1 / (syl (t + 1) : ℝ)
            from by rw [T_succ t]; push_cast; ring]
      have hfrac : (M : ℝ) / ((M : ℝ) - 1) * (y.drop t).sum
          ≤ (M : ℝ) / ((M : ℝ) - 1) * (1 / (syl (t + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left hSsum (le_of_lt (div_pos hMR hM1R))
      have hkeyB : (M : ℝ) / ((M : ℝ) - 1) * (1 / (syl (t + 1) : ℝ))
          = 1 / (syl (t + 1) : ℝ) + (1 / ((M : ℝ) - 1)) / (syl (t + 1) : ℝ) := by
        field_simp; ring
      linarith
    · -- Case 3: `t ≤ i-2`; suffix items have category `≥ syl(t+1)+1`.
      have htlen : t + 1 ≤ y.length := htn
      have hti1 : t + 1 ≤ i - 1 := by omega
      have hne : rawcat (y[t]'(by omega)) ≠ syl (t + 1) := ht4 ⟨htlen, hti1⟩
      have hdropcons : y.drop t = (y[t]'(by omega)) :: y.drop (t + 1) :=
        List.drop_eq_getElem_cons (by omega)
      have hyt0 : 0 < y[t]'(by omega) := hyb _ (List.getElem_mem _)
      have hyt_mem : (y[t]'(by omega)) ∈ y.drop t := by rw [hdropcons]; exact List.mem_cons_self ..
      have hyt_le : y[t]'(by omega) ≤ (y.drop t).sum :=
        List.single_le_sum (fun a ha => le_of_lt (hyb a (List.mem_of_mem_drop ha))) _ hyt_mem
      have hyt_le_cs : y[t]'(by omega) ≤ 1 / (syl (t + 1) : ℝ) := le_trans hyt_le hSsum
      have hraw_ge : syl (t + 1) ≤ rawcat (y[t]'(by omega)) :=
        rawcat_ge_of_le _ hyt0 (syl (t + 1)) hcs1 hyt_le_cs
      have hraw_head : syl (t + 1) + 1 ≤ rawcat (y[t]'(by omega)) := by
        rcases eq_or_lt_of_le hraw_ge with he | he
        · exact absurd he.symm hne
        · omega
      have hpair : (y.drop t).Pairwise (· ≥ ·) :=
        List.Pairwise.sublist (List.drop_sublist t y) hySort.pairwise
      have hSrc : ∀ z ∈ y.drop t, syl (t + 1) + 1 ≤ rawcat z := by
        intro z hz
        have hz0 : 0 < z := hyb z (List.mem_of_mem_drop hz)
        have hz_le_head : z ≤ y[t]'(by omega) := by
          rw [hdropcons] at hz hpair
          rcases List.mem_cons.mp hz with rfl | hztail
          · exact le_refl _
          · exact List.rel_of_pairwise_cons hpair hztail
        calc syl (t + 1) + 1 ≤ rawcat (y[t]'(by omega)) := hraw_head
          _ ≤ rawcat z := rawcat_anti z (y[t]'(by omega)) hz0 hz_le_head
      -- `A` and `B` are the two candidate weight/size ratios; the bound is their `max`.
      set A := (M : ℝ) / ((M : ℝ) - 1) with hA
      set B := 1 + 1 / ((syl (t + 1) : ℝ) + 1) with hB
      have hzbound : ∀ z ∈ y.drop t, wh M z ≤ max A B * z := fun z hz =>
        suffix_item_bound M hM z (hyb z (List.mem_of_mem_drop hz))
          (hyle z (List.mem_of_mem_drop hz)) (syl (t + 1)) hcs1 (hSrc z hz)
      have hmaxnn : (0 : ℝ) ≤ max A B :=
        le_trans (le_of_lt (div_pos hMR hM1R)) (le_max_left _ _)
      have hWSle : ((y.drop t).map (wh M)).sum ≤ max A B * (y.drop t).sum := by
        calc ((y.drop t).map (wh M)).sum
            ≤ ((y.drop t).map (fun z => max A B * z)).sum := List.sum_le_sum hzbound
          _ = _ := sum_map_smul _ _
      have hDmax : max A B * (y.drop t).sum ≤ max A B * (1 / (syl (t + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left hSsum hmaxnn
      have hstep : (T t : ℝ) + max A B * (y.drop t).sum
          ≤ (T i : ℝ) + (1 / ((M : ℝ) - 1)) / (syl i) := by
        rcases le_total A B with hAB | hAB
        · -- max = B; the `T (t+2)` bound
          rw [max_eq_right hAB] at hDmax ⊢
          have hsucc2 : syl (t + 2) = syl (t + 1) * (syl (t + 1) + 1) := syl_succ (by omega)
          have e2 : (T t : ℝ) + B * (1 / (syl (t + 1) : ℝ)) = (T (t + 2) : ℝ) := by
            rw [hB, show (T (t + 2) : ℝ) = (T (t + 1) : ℝ) + 1 / (syl (t + 2) : ℝ)
                  from by rw [T_succ (t + 1)]; push_cast; ring,
                show (T (t + 1) : ℝ) = (T t : ℝ) + 1 / (syl (t + 1) : ℝ)
                  from by rw [T_succ t]; push_cast; ring,
                show (syl (t + 2) : ℝ) = (syl (t + 1) : ℝ) * ((syl (t + 1) : ℝ) + 1)
                  from by rw [hsucc2]; push_cast; ring]
            field_simp; ring
          have hle : (T (t + 2) : ℝ) ≤ (T i : ℝ) := by exact_mod_cast T_mono (by omega : t + 2 ≤ i)
          linarith [hDmax, e2, hle, hRHS2]
        · -- max = A; the `T_aux_mono` bound
          rw [max_eq_left hAB] at hDmax ⊢
          have e1 : (T t : ℝ) + A * (1 / (syl (t + 1) : ℝ))
              = (T (t + 1) : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl (t + 1) : ℝ)) := by
            rw [hA, show (T (t + 1) : ℝ) = (T t : ℝ) + 1 / (syl (t + 1) : ℝ)
                  from by rw [T_succ t]; push_cast; ring]
            field_simp; ring
          have mono := T_aux_mono M (t + 1) (by omega) hM1R i (by omega)
            (fun m hm hmi => by
              have hsm : syl m ≤ syl (i - 1) := syl_le (by omega)
              omega)
          have hmono2 : (T (t + 1) : ℝ) + (1 / ((M : ℝ) - 1)) * (1 / (syl (t + 1) : ℝ))
              ≤ (T i : ℝ) + (1 / ((M : ℝ) - 1)) / (syl i) := by
            rw [← mul_one_div (1 / ((M : ℝ) - 1)) (syl i : ℝ)]; exact mono
          linarith [hDmax, e1, hmono2]
      linarith [hWSle]

public theorem harmonic_bound (M : ℕ) (y : List ℝ)
  (hM : M ≥ 2) (hyb : ∀ z ∈ y, 0 < z) (hySum : y.sum ≤ 1)
  : (y.map (wh M)).sum ≤ Q M := by
  classical
  obtain ⟨hMi, hlti⟩ := syl_inv_fast_spec M
  set i := syl_inv_fast M with hi
  -- `i ≥ 2`
  have hine0 : i ≠ 0 := by
    rintro h; rw [h] at hMi; have : syl 0 = 0 := rfl; omega
  have hine1 : i ≠ 1 := by
    rintro h; rw [h] at hMi; have : syl 1 = 1 := rfl; omega
  have hi1 : 2 ≤ i := by omega
  have hi2a : syl (i - 1) < M := hlti (i - 1) (by omega)
  have hi2b : M ≤ syl i := hMi
  -- sorted permutation `y'` of `y`
  set y' := y.mergeSort (· ≥ ·) with hy'
  have hperm : List.Perm y' y := List.mergeSort_perm y (· ≥ ·)
  have hsort : y'.SortedGE := List.sortedGE_mergeSort
  have hyb' : ∀ z ∈ y', 0 < z := fun z hz => hyb z (hperm.mem_iff.mp hz)
  have hsum' : y'.sum ≤ 1 := by rw [hperm.sum_eq]; exact hySum
  have hmapsum : (y.map (wh M)).sum = (y'.map (wh M)).sum :=
    ((hperm.map (wh M)).sum_eq).symm
  -- construct the maximal consecutive-Sylvester-category prefix length `t`
  set m := min y'.length (i - 1) with hm
  set A := (Finset.range (m + 1)).filter
    (fun s => ∀ j, j < s → rawcat (y'.getD j 0) = syl (j + 1)) with hA
  have h0A : 0 ∈ A := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hAne : A.Nonempty := ⟨0, h0A⟩
  set t := A.max' hAne with ht
  have htA : t ∈ A := A.max'_mem hAne
  obtain ⟨htrange, htprefix⟩ := Finset.mem_filter.mp htA
  have htm : t ≤ m := by have := Finset.mem_range.mp htrange; omega
  have ht1 : t ≤ y'.length := le_trans htm (min_le_left _ _)
  have ht2 : t + 1 ≤ i := by have := le_trans htm (min_le_right _ _); omega
  have ht3 : ∀ j, (hj : j < t) → rawcat (y'[j]'(by omega)) = syl (j + 1) := by
    intro j hj
    rw [← List.getD_eq_getElem y' 0 (by omega : j < y'.length)]
    exact htprefix j hj
  have ht4 : (h : t + 1 ≤ y'.length ∧ t + 1 ≤ i - 1)
      → rawcat (y'[t]'(by omega)) ≠ syl (t + 1) := by
    intro h
    have htnotA : t + 1 ∉ A := fun hin => by have := A.le_max' _ hin; omega
    have hfail : ¬ (∀ j, j < t + 1 → rawcat (y'.getD j 0) = syl (j + 1)) := fun hall =>
      htnotA (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hall⟩)
    push Not at hfail
    obtain ⟨j, hjlt, hjne⟩ := hfail
    have hjt : j = t := by
      by_contra hjne2
      exact hjne (htprefix j (by omega))
    subst hjt
    rw [← List.getD_eq_getElem y' 0 (by omega : t < y'.length)]
    exact hjne
  -- apply the helper and rewrite the bound as `Q M`
  rw [hmapsum]
  refine le_trans (harmonic_bound_helper M i t y' hM hyb' hsum' hi1 ⟨hi2a, hi2b⟩ hsort
    ht1 ht2 ht3 ht4) ?_
  rw [Q]
  push_cast
  rfl

public theorem harmonic_isWeighting (M : ℕ) (hM : 2 ≤ M) :
    IsWeighting (id : ℝ → ℝ) (wh M) ((Q M : ℝ)) := by
  intro b hb hbin
  have hsum : b.sum ≤ 1 := by simpa [binLoad] using hbin
  simpa [totalWeight] using harmonic_bound M b hM (by simpa using hb) hsum
