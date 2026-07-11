module

public import BinPack.Harmonic.Core
import BinPack.Harmonic.Correctness
import BinPack.Harmonic.WeightBound
import Mathlib.Tactic.Linarith

/-!
# Approximation ratio of `harmonicPack`

The algorithm fact (`harmonicPack_halg`) says next-fit-per-category uses fewer than
`totalWeight (wh M) + (M-1)` bins. Combined with the weight bound
(`harmonic_isWeighting`, giving `wbound = Q M`) via the weighting engine, this
yields `length < Q M · OPT + (M-1)` (`harmonicPack_ratio`), the asymptotic
`Q_M`-competitiveness of the harmonic algorithm.

The counting rests on one uniform per-category fact: within a single category, every
*completed* (non-open) next-fit bin has harmonic weight `≥ 1`.
-/

@[expose] public section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*}

/-! ## Generic next-fit infrastructure

A fresh fold invariant: the non-open (tail) bins of `nextFit` satisfy any predicate
`P` that holds of a bin at the moment an input item overflows it. -/

omit [IsStrictOrderedRing α] in
/-- Inserting one item just prepends it to the flattened contents (local copy of
`NextFit`'s internal lemma, which isn't exported). -/
private theorem insertNext_flatten' (size : β → α) (x : β) (p : List (List β)) :
    (insertNext size x p).flatten = x :: p.flatten := by
  rcases p with _ | ⟨b, rest⟩
  · rfl
  · simp only [insertNext]; split <;> simp

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- Total weight of a flattened packing is the sum of the bins' weights. -/
theorem totalWeight_flatten (wt : β → α) (bins : List (List β)) :
    totalWeight wt bins.flatten = (bins.map (totalWeight wt)).sum := by
  induction bins with
  | nil => simp [totalWeight]
  | cons b rest ih =>
    simp only [List.flatten_cons, List.map_cons, List.sum_cons, ← ih, totalWeight,
      List.map_append, List.sum_append]

omit [IsStrictOrderedRing α] in
/-- The fold that builds `nextFit`, with the "completed bins satisfy `P`" invariant
threaded alongside "every packed item comes from `s`". -/
theorem foldl_insertNext_tail (size : β → α) (s : List β) (P : List β → Prop)
    (hclose : ∀ (b : List β) (x : β), (∀ y ∈ b, y ∈ s) → x ∈ s →
        1 < binLoad size b + size x → P b) :
    ∀ (l : List β) (acc : List (List β)), (∀ x ∈ l, x ∈ s) →
      (∀ y ∈ acc.flatten, y ∈ s) → (∀ b ∈ acc.tail, P b) →
      (∀ b ∈ (l.foldl (fun p x => insertNext size x p) acc).tail, P b)
      ∧ (∀ y ∈ (l.foldl (fun p x => insertNext size x p) acc).flatten, y ∈ s) := by
  intro l
  induction l with
  | nil => intro acc _ hmem htail; exact ⟨htail, hmem⟩
  | cons a t ih =>
    intro acc hl hmem htail
    have has : a ∈ s := hl a (by simp)
    have ht : ∀ x ∈ t, x ∈ s := fun x hx => hl x (by simp [hx])
    -- new accumulator after inserting a
    have hmem' : ∀ y ∈ (insertNext size a acc).flatten, y ∈ s := by
      intro y hy
      rw [insertNext_flatten', List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact has
      · exact hmem y hy
    have htail' : ∀ b ∈ (insertNext size a acc).tail, P b := by
      rcases acc with _ | ⟨bh, rest⟩
      · intro b hb; simp [insertNext] at hb
      · simp only [insertNext]
        split
        · -- fits: tail is unchanged `rest`
          intro b hb
          simp only [List.tail_cons] at hb
          exact htail b (by simpa using hb)
        · -- no fit: new tail is `bh :: rest`; `bh` just got completed by `a`
          rename_i hnofit
          intro b hb
          simp only [List.tail_cons, List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hclose _ a (fun y hy => hmem y (List.mem_flatten.mpr ⟨_, by simp, hy⟩))
              has (not_le.mp hnofit)
          · exact htail b (by simpa using hb)
    simpa only [List.foldl_cons] using ih (insertNext size a acc) ht hmem' htail'

omit [IsStrictOrderedRing α] in
/-- Every completed (non-open) bin of `nextFit size s` satisfies `P`, when `P` holds
of any bin that an input item overflows. -/
theorem nextFit_tail_prop (size : β → α) (s : List β) (P : List β → Prop)
    (hclose : ∀ (b : List β) (x : β), (∀ y ∈ b, y ∈ s) → x ∈ s →
        1 < binLoad size b + size x → P b) :
    ∀ b ∈ (nextFit size s).tail, P b :=
  (foldl_insertNext_tail size s P hclose s [] (fun _ h => h) (by simp) (by simp)).1

omit [IsStrictOrderedRing α] in
/-- `nextFit` never produces an empty bin. -/
theorem nextFit_bins_ne_nil (size : β → α) (s : List β) :
    ∀ b ∈ nextFit size s, b ≠ [] := by
  have key : ∀ (l : List β) (acc : List (List β)), (∀ b ∈ acc, b ≠ []) →
      ∀ b ∈ l.foldl (fun p x => insertNext size x p) acc, b ≠ [] := by
    intro l
    induction l with
    | nil => intro acc hacc; exact hacc
    | cons a t ih =>
      intro acc hacc
      apply ih
      intro b hb
      rcases acc with _ | ⟨bh, rest⟩
      · simp only [insertNext, List.mem_singleton] at hb; subst hb; simp
      · simp only [insertNext] at hb
        split at hb
        · -- (a :: bh) :: rest
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · simp
          · exact hacc b (List.mem_cons_of_mem _ hb)
        · -- [a] :: bh :: rest
          simp only [List.mem_cons] at hb
          rcases hb with rfl | rfl | hb
          · simp
          · exact hacc _ (by simp)
          · exact hacc b (List.mem_cons_of_mem _ hb)
  exact key s [] (by simp)

/-! ## Counting bins from per-bin weights -/

/-- If every element weighs `≥ 1`, the length is at most the total weight. -/
theorem length_le_sum_all {γ : Type*} (L : List γ) (f : γ → α)
    (hall : ∀ x ∈ L, 1 ≤ f x) : (L.length : α) ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := hall a (by simp)
    have ht := ih (fun x hx => hall x (by simp [hx]))
    push_cast; linarith

/-- If every non-head element weighs `≥ 1` and all weigh `≥ 0`, the length is at
most the total weight plus one (the open bin may be underfull). -/
theorem length_le_sum_tail {γ : Type*} (L : List γ) (f : γ → α)
    (hpos : ∀ x ∈ L, 0 ≤ f x) (htail : ∀ x ∈ L.tail, 1 ≤ f x) :
    (L.length : α) ≤ (L.map f).sum + 1 := by
  cases L with
  | nil =>
    simp only [List.length_nil, List.map_nil, List.sum_nil, Nat.cast_zero, zero_add]
    exact zero_le_one
  | cons a t =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hh := hpos a (by simp)
    have ht := length_le_sum_all t f (fun x hx => htail x hx)
    push_cast; linarith

omit [IsStrictOrderedRing α] in
/-- Folding `insertNext` prepends the reversed input to the accumulator's contents. -/
private theorem foldl_flatten' (size : β → α) :
    ∀ (l : List β) (acc : List (List β)),
      (l.foldl (fun p x => insertNext size x p) acc).flatten = l.reverse ++ acc.flatten := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons a t ih =>
    intro acc
    simp only [List.foldl_cons, List.reverse_cons]
    rw [ih (insertNext size a acc), insertNext_flatten']; simp

omit [IsStrictOrderedRing α] in
/-- The flattened next-fit packing is the reversed input. -/
theorem nextFit_flatten (size : β → α) (s : List β) :
    (nextFit size s).flatten = s.reverse := by
  simp only [nextFit, foldl_flatten', List.flatten_nil, List.append_nil]

omit [IsStrictOrderedRing α] in
/-- The bins' weights sum to the total weight of the input. -/
theorem sum_bins_weight (size wt : β → α) (s : List β) :
    ((nextFit size s).map (totalWeight wt)).sum = totalWeight wt s := by
  rw [← totalWeight_flatten, nextFit_flatten]
  simp [totalWeight, List.map_reverse, List.sum_reverse]

/-! ## Per-item category facts (over `ℝ`) -/

/-- `⌊1/x⌋.toNat` cast to `ℝ` is `≤ 1/x`, for `0 < x ≤ 1`. -/
private theorem toNat_floor_le (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ((⌊1 / x⌋).toNat : ℝ) ≤ 1 / x := by
  have h1x : (1 : ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx0, one_mul]; exact hx1
  have hfnn : (0 : ℤ) ≤ ⌊1 / x⌋ := by
    have : (1 : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.mpr (by exact_mod_cast h1x); omega
  calc ((⌊1 / x⌋).toNat : ℝ) = (⌊1 / x⌋ : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hfnn
    _ ≤ 1 / x := Int.floor_le (1 / x)

/-- A "small" category-`k` item (`k < M`) has size `≤ 1/k` and weight exactly `1/k`. -/
theorem cat_lt_M_facts (M : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (k : ℕ)
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
theorem cat_eq_M_facts (M : ℕ) (hM : 2 ≤ M) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hk : cat M x = M) :
    x ≤ 1 / (M : ℝ) ∧ wh M x = (M : ℝ) / ((M : ℝ) - 1) * x := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hrM : M ≤ (⌊1 / x⌋).toNat := by simp only [cat] at hk; omega
  have hMle : (M : ℝ) ≤ 1 / x :=
    le_trans (by exact_mod_cast hrM) (toNat_floor_le x hx0 hx1)
  have hxM : x ≤ 1 / (M : ℝ) := by
    rw [le_div_iff₀ hMpos]; rw [le_div_iff₀ hx0] at hMle; linarith
  exact ⟨hxM, by rw [wh, if_pos hxM]; ring⟩

/-! ## The crux: a completed bin of one category weighs `≥ 1` -/

/-- A map with a constant value sums to `length · value`. -/
private theorem sum_map_const {γ : Type*} (l : List γ) (c : ℝ) (f : γ → ℝ)
    (h : ∀ y ∈ l, f y = c) : (l.map f).sum = (l.length : ℝ) * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h a (by simp), ih (fun y hy => h y (by simp [hy]))]; push_cast; ring

/-- The (real-cast) length of a `flatMap` is the sum of the branch lengths. -/
private theorem cast_length_flatMap {γ δ : Type*} (cs : List γ) (f : γ → List δ) :
    (((cs.flatMap f).length : ℝ)) = (cs.map (fun c => ((f c).length : ℝ))).sum := by
  induction cs with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ← ih]
    push_cast; ring

/-- Pull a constant factor out of a mapped sum. -/
private theorem sum_map_mul_left' {γ : Type*} (l : List γ) (c : ℝ) (g : γ → ℝ) :
    (l.map (fun y => c * g y)).sum = c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **Crux.** In a single category `k`, any bin `b` that an input item `x` overflows
(`binLoad b + size x > 1`) has harmonic weight `≥ 1`. For `k < M` this is because
`b` then holds `≥ k` items each weighing `1/k`; for `k = M` because
`weight = M/(M-1)·load > 1`. -/
theorem cat_bin_weight_ge (M : ℕ) (hM : 2 ≤ M) (size : β → ℝ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkM : k ≤ M) (b : List β) (x : β)
    (hb : ∀ y ∈ b, (0 < size y ∧ size y ≤ 1) ∧ cat M (size y) = k)
    (hx0 : 0 < size x) (hx1 : size x ≤ 1) (hxk : cat M (size x) = k)
    (hover : 1 < binLoad size b + size x) :
    1 ≤ totalWeight (fun y => wh M (size y)) b := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM1pos : (0 : ℝ) < (M : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  rcases eq_or_lt_of_le hkM with hkeq | hklt
  · -- k = M
    subst hkeq
    have hsx : size x ≤ 1 / (k : ℝ) := (cat_eq_M_facts k hM (size x) hx0 hx1 hxk).1
    have hwh : ∀ y ∈ b, wh k (size y) = (k : ℝ) / ((k : ℝ) - 1) * size y :=
      fun y hy => (cat_eq_M_facts k hM (size y) (hb y hy).1.1 (hb y hy).1.2 (hb y hy).2).2
    have htw : totalWeight (fun y => wh k (size y)) b
        = (k : ℝ) / ((k : ℝ) - 1) * binLoad size b := by
      unfold totalWeight binLoad
      rw [show (b.map fun y => wh k (size y))
            = b.map (fun y => (k : ℝ) / ((k : ℝ) - 1) * size y) from
          List.map_congr_left (fun y hy => hwh y hy), sum_map_mul_left']
    have hbig : binLoad size b > 1 - 1 / (k : ℝ) := by linarith [hover, hsx]
    rw [htw, div_mul_eq_mul_div, le_div_iff₀ hM1pos, one_mul]
    have hkey : (k : ℝ) * (1 - 1 / (k : ℝ)) = (k : ℝ) - 1 := by field_simp
    nlinarith [mul_lt_mul_of_pos_left hbig hMpos, hkey]
  · -- k < M
    have hsx : size x ≤ 1 / (k : ℝ) := (cat_lt_M_facts M (size x) hx0 hx1 k hxk hklt).1
    have hwh : ∀ y ∈ b, wh M (size y) = 1 / (k : ℝ) :=
      fun y hy => (cat_lt_M_facts M (size y) (hb y hy).1.1 (hb y hy).1.2 k (hb y hy).2 hklt).2
    have hsz : ∀ y ∈ b, size y ≤ 1 / (k : ℝ) :=
      fun y hy => (cat_lt_M_facts M (size y) (hb y hy).1.1 (hb y hy).1.2 k (hb y hy).2 hklt).1
    have htw : totalWeight (fun y => wh M (size y)) b = (b.length : ℝ) * (1 / (k : ℝ)) := by
      unfold totalWeight; exact sum_map_const b (1 / (k : ℝ)) _ hwh
    have hbl : binLoad size b ≤ (b.length : ℝ) * (1 / (k : ℝ)) := by
      have h := List.sum_le_card_nsmul (b.map size) (1 / (k : ℝ)) (by
        intro z hz; rw [List.mem_map] at hz; obtain ⟨y, hy, rfl⟩ := hz; exact hsz y hy)
      rw [List.length_map, nsmul_eq_mul] at h; exact h
    have hbig : binLoad size b > 1 - 1 / (k : ℝ) := by linarith [hover, hsx]
    have hu : (0 : ℝ) < 1 / (k : ℝ) := by positivity
    have hku : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
    have hstep : (k : ℝ) < (b.length : ℝ) + 1 := by nlinarith [hbl, hbig, hku, hu]
    have hlenk : k ≤ b.length := by
      have : k < b.length + 1 := by exact_mod_cast hstep
      omega
    rw [htw]
    calc (1 : ℝ) = (k : ℝ) * (1 / (k : ℝ)) := hku.symm
      _ ≤ (b.length : ℝ) * (1 / (k : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlenk) hu.le

/-! ## Per-category bin counts -/

/-- Strict variant of `length_le_sum_tail`: if all elements weigh `> 0` and non-head
elements weigh `≥ 1`, the length is strictly below total weight plus one. -/
theorem length_lt_sum_tail {γ : Type*} (L : List γ) (f : γ → ℝ)
    (hpos : ∀ x ∈ L, 0 < f x) (htail : ∀ x ∈ L.tail, 1 ≤ f x) :
    (L.length : ℝ) < (L.map f).sum + 1 := by
  cases L with
  | nil => simp
  | cons a t =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hh := hpos a (by simp)
    have ht := length_le_sum_all t f (fun x hx => htail x hx)
    push_cast; linarith

omit [IsStrictOrderedRing α] in
/-- Every item of a `nextFit` bin comes from the input list. -/
theorem nextFit_mem (size : β → α) (s : List β) :
    ∀ b ∈ nextFit size s, ∀ y ∈ b, y ∈ s := by
  intro b hb y hy
  have hyf : y ∈ (nextFit size s).flatten := List.mem_flatten.mpr ⟨b, hb, hy⟩
  rw [nextFit_flatten] at hyf
  simpa using hyf

/-- Harmonic weight is strictly positive on valid items. -/
theorem wh_pos (M : ℕ) (hM : 2 ≤ M) (z : ℝ) (hz0 : 0 < z) (hz1 : z ≤ 1) : 0 < wh M z := by
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  rw [wh]
  split
  · exact div_pos (mul_pos hMpos hz0) hM1
  · have h1z : (1 : ℝ) ≤ 1 / z := by rw [le_div_iff₀ hz0, one_mul]; exact hz1
    have hfl : (1 : ℤ) ≤ ⌊1 / z⌋ := Int.le_floor.mpr (by exact_mod_cast h1z)
    have hpos : 0 < (⌊1 / z⌋).toNat := by omega
    exact div_pos one_pos (by exact_mod_cast hpos)

/-- Category `k` uses fewer than `totalWeight + 1` bins. -/
theorem cat_length_le (M : ℕ) (hM : 2 ≤ M) (size : β → ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkM : k ≤ M)
    (sub : List β) (hsub : ∀ y ∈ sub, (0 < size y ∧ size y ≤ 1) ∧ cat M (size y) = k) :
    ((nextFit size sub).length : ℝ) < totalWeight (fun y => wh M (size y)) sub + 1 := by
  have hpos : ∀ b ∈ nextFit size sub, 0 < totalWeight (fun y => wh M (size y)) b := by
    intro b hb
    unfold totalWeight
    apply List.sum_pos
    · intro w hw
      rw [List.mem_map] at hw; obtain ⟨y, hy, rfl⟩ := hw
      have hy' := hsub y (nextFit_mem size sub b hb y hy)
      exact wh_pos M hM (size y) hy'.1.1 hy'.1.2
    · simpa using nextFit_bins_ne_nil size sub b hb
  have htail : ∀ b ∈ (nextFit size sub).tail, 1 ≤ totalWeight (fun y => wh M (size y)) b :=
    nextFit_tail_prop size sub _ (fun b x hbsub hxsub hover =>
      cat_bin_weight_ge M hM size k hk1 hkM b x
        (fun y hy => hsub y (hbsub y hy)) (hsub x hxsub).1.1 (hsub x hxsub).1.2
        (hsub x hxsub).2 hover)
  have h := length_lt_sum_tail (nextFit size sub)
    (fun b => totalWeight (fun y => wh M (size y)) b) hpos htail
  rwa [sum_bins_weight] at h

/-- Category `1` uses at most `totalWeight` bins (each item weighs `1`, and every
bin is nonempty) — this is the saving that yields the `M-1` (not `M`) constant. -/
theorem cat_length_le_one (M : ℕ) (hM : 2 ≤ M) (size : β → ℝ) (sub : List β)
    (hsub : ∀ y ∈ sub, (0 < size y ∧ size y ≤ 1) ∧ cat M (size y) = 1) :
    ((nextFit size sub).length : ℝ) ≤ totalWeight (fun y => wh M (size y)) sub := by
  have hbins : ∀ b ∈ nextFit size sub, 1 ≤ totalWeight (fun y => wh M (size y)) b := by
    intro b hb
    have hne := nextFit_bins_ne_nil size sub b hb
    have hwh1 : ∀ y ∈ b, 1 ≤ wh M (size y) := by
      intro y hy
      have hy' := hsub y (nextFit_mem size sub b hb y hy)
      have hval := (cat_lt_M_facts M (size y) hy'.1.1 hy'.1.2 1 hy'.2 (by omega)).2
      rw [hval]; norm_num
    have h1 := length_le_sum_all b (fun y => wh M (size y)) hwh1
    have hblen : (1 : ℝ) ≤ (b.length : ℝ) := by
      have : 1 ≤ b.length := List.length_pos_iff.mpr hne
      exact_mod_cast this
    calc (1 : ℝ) ≤ (b.length : ℝ) := hblen
      _ ≤ totalWeight (fun y => wh M (size y)) b := by unfold totalWeight; exact h1
  have h := length_le_sum_all (nextFit size sub)
    (fun b => totalWeight (fun y => wh M (size y)) b) hbins
  rwa [sum_bins_weight] at h

/-! ## Assembly -/

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- Total weight is additive across the branches of a `flatMap`. -/
theorem totalWeight_flatMap {γ : Type*} (wt : β → α) (g : γ → List β) (cs : List γ) :
    totalWeight wt (cs.flatMap g) = (cs.map (fun c => totalWeight wt (g c))).sum := by
  induction cs with
  | nil => simp [totalWeight]
  | cons a t ih =>
    rw [List.flatMap_cons, totalWeight, List.map_append, List.sum_append, ← totalWeight,
      ← totalWeight, ih, List.map_cons, List.sum_cons]

/-- Strict pointwise sum comparison over a nonempty range. -/
theorem sum_range_map_lt (a b : ℕ → ℝ) : ∀ m, 1 ≤ m → (∀ i < m, a i < b i) →
    ((List.range m).map a).sum < ((List.range m).map b).sum := by
  intro m
  induction m with
  | zero => intro h _; omega
  | succ n ih =>
    intro _ hlt
    rw [List.range_succ, List.map_append, List.sum_append, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [List.range_zero, List.map_nil, List.sum_nil, zero_add]
      exact hlt 0 (by omega)
    · have ih' := ih hn (fun i hi => hlt i (by omega))
      have hlast := hlt n (by omega)
      linarith

/-- Sum over `[1, m]` of `a i + 1` is the sum of `a i` plus `m`. -/
theorem sum_range_map_add_one (a : ℕ → ℝ) : ∀ m,
    ((List.range m).map (fun i => a i + 1)).sum = ((List.range m).map a).sum + (m : ℝ) := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    push_cast; ring

/-- Combining the per-category bounds: category `0` (value `1`) with no slack, and
each later category `< totalWeight + 1`, over the `M-1 ≥ 1` later categories. -/
theorem sum_lt_of_cat (g h : ℕ → ℝ) (M : ℕ) (hM : 2 ≤ M)
    (h0 : g 0 ≤ h 0) (hrest : ∀ c, 1 ≤ c → c < M → g c < h c + 1) :
    ((List.range M).map g).sum < ((List.range M).map h).sum + ((M : ℝ) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
    List.map_map, List.map_map]
  have hmid := sum_range_map_lt (fun i => g (i + 1)) (fun i => h (i + 1) + 1) m hm
    (fun i hi => by have := hrest (i + 1) (by omega) (by omega); linarith)
  rw [sum_range_map_add_one (fun i => h (i + 1)) m] at hmid
  have hcomp1 : (List.range m).map (g ∘ Nat.succ) = (List.range m).map (fun i => g (i + 1)) := rfl
  have hcomp2 : (List.range m).map (h ∘ Nat.succ) = (List.range m).map (fun i => h (i + 1)) := rfl
  rw [hcomp1, hcomp2]
  push_cast
  linarith

/-- **The algorithm fact**: `harmonicPack` uses fewer than `totalWeight (wh M) + (M-1)`
bins (at `α = β = ℝ`, `M ≥ 2`). -/
public theorem harmonicPack_halg (M : ℕ) (hM : 2 ≤ M) (size : β → ℝ) (l : List β)
    (hl : ValidInput size l) :
    ((harmonicPack size M l).length : ℝ)
      < totalWeight (fun y => wh M (size y)) l + ((M : ℝ) - 1) := by
  set wt : β → ℝ := fun y => wh M (size y) with hwt
  set sub : ℕ → List β := fun c => l.filter fun x => cat M (size x) == c + 1 with hsubdef
  have hsub : ∀ c, ∀ y ∈ sub c, (0 < size y ∧ size y ≤ 1) ∧ cat M (size y) = c + 1 := by
    intro c y hy
    rw [hsubdef, List.mem_filter] at hy
    exact ⟨hl y hy.1, by simpa using hy.2⟩
  -- length is the sum of per-category bin counts
  have hlen : ((harmonicPack size M l).length : ℝ)
      = ((List.range M).map (fun c => ((nextFit size (sub c)).length : ℝ))).sum :=
    cast_length_flatMap (List.range M) (fun c => nextFit size (sub c))
  -- total weight is the sum of per-category total weights
  have htw : totalWeight wt l
      = ((List.range M).map (fun c => totalWeight wt (sub c))).sum := by
    have hperm := categories_cover size M (by omega) l hl
    calc totalWeight wt l
        = totalWeight wt ((List.range M).flatMap sub) :=
          (List.Perm.sum_eq (hperm.map wt)).symm
      _ = _ := totalWeight_flatMap wt sub (List.range M)
  rw [hlen, htw]
  apply sum_lt_of_cat _ _ M hM
  · -- category 0 : value 1
    exact cat_length_le_one M hM size (sub 0) (fun y hy => by simpa using hsub 0 y hy)
  · -- category c ≥ 1 : value c+1 ∈ [2, M]
    intro c hc1 hcM
    exact cat_length_le M hM size (c + 1) (by omega) (by omega) (sub c) (hsub c)

/-- **Harmonic algorithm is `Q M`-competitive** (at `α = β = ℝ`, `size = id`).
Combining `harmonicPack_halg` (ratio `1`, constant `M-1`) with the weight bound
`harmonic_isWeighting` (`wbound = Q M`) via the weighting engine. -/
public theorem harmonicPack_ratio (M : ℕ) (hM : 2 ≤ M) (l : List ℝ)
    (hl : ValidInput (id : ℝ → ℝ) l) :
    ((harmonicPack (id : ℝ → ℝ) M l).length : ℝ)
      < (Q M : ℝ) * optimum (id : ℝ → ℝ) l + ((M : ℝ) - 1) := by
  have h := length_lt_opt (id : ℝ → ℝ) (wh M) 1 (Q M : ℝ) ((M : ℝ) - 1) l
    (harmonicPack (id : ℝ → ℝ) M l) zero_le_one
    (harmonicPack_isPacking (id : ℝ → ℝ) M (by omega) l hl)
    (fun x hx => (hl x hx).1) (harmonic_isWeighting M hM)
    (by simpa using harmonicPack_halg M hM (id : ℝ → ℝ) l hl)
  simpa using h
