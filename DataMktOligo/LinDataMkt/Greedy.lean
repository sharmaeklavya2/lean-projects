module

public import DataMktOligo.LinDataMkt.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

/-!
# Demand as fractional knapsack

A buyer facing linear prices solves a fractional knapsack problem:
maximize `∑ j, τ i j * x j` subject to `∑ j, p j * x j ≤ b i` and `x ∈ [0,1]^m`.
Its solutions are exactly the greedy ones, consuming datasets in
non-increasing order of *bang-per-buck* `τ i j / p j`.

## Main results

* `DataMktOligo.LinDataMkt.isDemand_iff`: an affordable bundle is a demand iff
  it admits no improving swap and leaves no idle budget.
  This is a local, permutation-free characterization.
* `DataMktOligo.LinDataMkt.isDemand_of_isGreedy`: consuming greedily in bang-per-buck order,
  in the sense of `DataMktOligo.LinDataMkt.IsGreedy`, produces a demand.
* `DataMktOligo.LinDataMkt.exists_demand_two`: the `demand` set is non-empty for two datasets.
  `isDemand_of_isGreedy` gives us a witness.
-/

namespace DataMktOligo.LinDataMkt

variable {n m : ℕ} (mkt : Instance n m) (p : Fin m → ℝ) (i : Fin n)

/-- Buyer `i` weakly prefers dataset `k`'s bang-per-buck to dataset `j`'s,
i.e., `τ i j / p j ≤ τ i k / p k`.
Stated multiplicatively so that it is meaningful at zero prices. -/
@[expose] public def bpbLE (j k : Fin m) : Prop := mkt.τ i j * p k ≤ mkt.τ i k * p j

/-- The bundle `x` admits no improving swap: buyer `i` never holds a positive amount of a
dataset `k` while some strictly better bang-per-buck dataset `j` still has room to spare. -/
@[expose] public def NoImprovingSwap (x : Fin m → ℝ) : Prop :=
  ∀ j k, 0 < x k → x j < 1 → bpbLE mkt p i j k

/-- The bundle `x` leaves no idle budget: either it exhausts buyer `i`'s budget,
or it already contains all of every dataset she values. -/
@[expose] public def Saturated (x : Fin m → ℝ) : Prop :=
  cost p x = mkt.b i ∨ ∀ j, 0 < mkt.τ i j → x j = 1

/-! ### Auxiliary lemmas -/

/-- Perturbing a bundle at two coordinates changes any linear functional of it by the
obvious amount. Used to build improving bundles; taking `k := j` and `b := 0` perturbs a
single coordinate. -/
private theorem sum_perturb (c x : Fin m → ℝ) (j k : Fin m) (a b : ℝ) :
    ∑ l, c l * (x l + (if l = j then a else 0) - (if l = k then b else 0))
      = (∑ l, c l * x l) + c j * a - c k * b := by
  simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
    Finset.sum_ite_eq']

/-- If a positive budget is exactly exhausted, some dataset is bought at a positive price. -/
private theorem exists_pos_spend (hp : IsNonnegVector p) (hb : 0 < mkt.b i)
    {x : Fin m → ℝ} (hcube : x ∈ unitCube m) (hcost : cost p x = mkt.b i) :
    ∃ k, 0 < p k ∧ 0 < x k := by
  by_contra hcon
  push Not at hcon
  have hzero : cost p x = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases (hp k).lt_or_eq with hpk | hpk
    · have hxk : x k = 0 :=
        le_antisymm (hcon k hpk) ((mem_unitCube_iff.1 hcube k).1)
      simp [hxk]
    · simp [← hpk]
  rw [hcost] at hzero
  exact absurd hzero hb.ne'

/-- With a positive budget exactly exhausted, any *valuable* dataset that is not fully
bought must carry a positive price: a free valuable dataset would be an improving swap
against whatever the buyer did spend her money on. -/
private theorem price_pos_of_lt_one (hp : IsNonnegVector p) (hb : 0 < mkt.b i)
    {x : Fin m → ℝ} (hcube : x ∈ unitCube m) (hcost : cost p x = mkt.b i)
    (hswap : NoImprovingSwap mkt p i x) {j : Fin m} (hτ : 0 < mkt.τ i j) (hlt : x j < 1) :
    0 < p j := by
  rcases (hp j).lt_or_eq with hpj | hpj
  · exact hpj
  · obtain ⟨k, hpk, hxk⟩ := exists_pos_spend mkt p i hp hb hcube hcost
    have hsw := hswap j k hxk hlt
    simp only [bpbLE, ← hpj, mul_zero] at hsw
    nlinarith

/-- **Characterization of demand.** An affordable bundle is utility-maximizing exactly when
it admits no improving swap and leaves no idle budget.

The proof needs a *positive budget*, otherwise a counterexample exists: one buyer,
one free dataset (`p = 0`) of value `1`, and `x = ![1/2]`. -/
public theorem isDemand_iff (hp : IsNonnegVector p) (hb : 0 < mkt.b i) (x : Fin m → ℝ) :
    IsDemand mkt p i x ↔
      x ∈ affordableSet mkt p i ∧ NoImprovingSwap mkt p i x ∧ Saturated mkt p i x := by
  classical
  constructor
  · -- `→`: a maximizer admits no improving swap and leaves no idle budget.
    rintro ⟨hxa, hmax⟩
    refine ⟨hxa, ?_, ?_⟩
    · -- No improving swap: otherwise shift spending from `k` to `j`.
      intro j k hxk hxj
      by_contra hcon
      simp only [bpbLE, not_le] at hcon
      -- Both `τ i j` and `p k` are positive, since their product exceeds `τ i k * p j ≥ 0`.
      have hprod : 0 < mkt.τ i j * p k :=
        lt_of_le_of_lt (mul_nonneg (mkt.τ_nonneg i k) (hp j)) hcon
      have hτj : 0 < mkt.τ i j := by
        by_contra h
        push Not at h
        rw [le_antisymm h (mkt.τ_nonneg i j)] at hprod; simp at hprod
      have hpk : 0 < p k := by
        by_contra h
        push Not at h
        rw [le_antisymm h (hp k)] at hprod; simp at hprod
      have hjk : j ≠ k := by rintro rfl; exact absurd hcon (lt_irrefl _)
      -- The perturbation: buy `δ` more of `j`, paying for it by selling some of `k`.
      set δ := min (1 - x j) (x k * p k / (p j + 1)) with hδ
      have hp1 : (0:ℝ) < p j + 1 := by linarith [hp j]
      have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
      have hδ1 : δ ≤ 1 - x j := min_le_left _ _
      have hδ2 : δ ≤ x k * p k / (p j + 1) := min_le_right _ _
      have hshift : δ * p j / p k ≤ x k := by
        rw [div_le_iff₀ hpk]
        have h2 : δ * p j ≤ x k * p k / (p j + 1) * p j :=
          mul_le_mul_of_nonneg_right hδ2 (hp j)
        have h3 : x k * p k / (p j + 1) * p j ≤ x k * p k := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hp1]
          nlinarith [mul_nonneg hxk.le hpk.le]
        linarith
      have hshift0 : 0 ≤ δ * p j / p k :=
        div_nonneg (mul_nonneg hδpos.le (hp j)) hpk.le
      set y : Fin m → ℝ :=
        fun l => x l + (if l = j then δ else 0) - (if l = k then δ * p j / p k else 0) with hy
      have hyj : y j = x j + δ := by simp [hy, hjk]
      have hyk : y k = x k - δ * p j / p k := by simp [hy, Ne.symm hjk]
      have hyl : ∀ l, l ≠ j → l ≠ k → y l = x l := by intro l h1 h2; simp [hy, h1, h2]
      -- `y` is affordable …
      have hycost : cost p y = cost p x := by
        simp only [cost, hy, sum_perturb]
        field_simp
        ring
      have hyaff : y ∈ affordableSet mkt p i := by
        refine ⟨mem_unitCube_iff.2 fun l => ?_, ?_, ?_⟩
        · rcases eq_or_ne l j with rfl | hlj
          · exact ⟨by linarith [(mem_unitCube_iff.1 hxa.1 l).1, hδpos], by
              rw [hyj]; linarith⟩
          · rcases eq_or_ne l k with rfl | hlk
            · exact ⟨by rw [hyk]; linarith, by
                rw [hyk]; linarith [(mem_unitCube_iff.1 hxa.1 l).2]⟩
            · rw [hyl l hlj hlk]; exact mem_unitCube_iff.1 hxa.1 l
        · rw [hycost]; exact hxa.2.1
        · intro l hl
          rcases eq_or_ne l j with rfl | hlj
          · exact hτj
          · rcases eq_or_ne l k with rfl | hlk
            · exact hxa.2.2 l hxk
            · rw [hyl l hlj hlk] at hl; exact hxa.2.2 l hl
      -- … and strictly better, contradicting maximality.
      have hyutil : util mkt i x < util mkt i y := by
        have he : util mkt i y
            = util mkt i x + mkt.τ i j * δ - mkt.τ i k * (δ * p j / p k) := by
          simp only [util, hy, sum_perturb]
        rw [he]
        have hstep : mkt.τ i k * (δ * p j / p k) < mkt.τ i j * δ := by
          have e : mkt.τ i k * (δ * p j / p k) = mkt.τ i k * (δ * p j) / p k := by ring
          rw [e, div_lt_iff₀ hpk]
          nlinarith [mul_lt_mul_of_pos_left hcon hδpos]
        linarith
      exact absurd (hmax y hyaff) (not_le.mpr hyutil)
    · -- No idle budget: otherwise buy more of some valuable dataset.
      by_contra hcon
      simp only [Saturated] at hcon
      push Not at hcon
      obtain ⟨hne, j, hτj, hxj1⟩ := hcon
      have hxj : x j < 1 := lt_of_le_of_ne (mem_unitCube_iff.1 hxa.1 j).2 hxj1
      have hslack : cost p x < mkt.b i := lt_of_le_of_ne hxa.2.1 hne
      set δ := min (1 - x j) ((mkt.b i - cost p x) / (p j + 1)) with hδ
      have hp1 : (0:ℝ) < p j + 1 := by linarith [hp j]
      have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
      have hδ1 : δ ≤ 1 - x j := min_le_left _ _
      have hδ2 : δ ≤ (mkt.b i - cost p x) / (p j + 1) := min_le_right _ _
      set y : Fin m → ℝ :=
        fun l => x l + (if l = j then δ else 0) - (if l = j then 0 else 0) with hy
      have hyj : y j = x j + δ := by simp [hy]
      have hyl : ∀ l, l ≠ j → y l = x l := by intro l h1; simp [hy, h1]
      have hycost : cost p y = cost p x + p j * δ := by
        simp only [cost, hy, sum_perturb]; ring
      have hyaff : y ∈ affordableSet mkt p i := by
        refine ⟨mem_unitCube_iff.2 fun l => ?_, ?_, ?_⟩
        · rcases eq_or_ne l j with rfl | hlj
          · exact ⟨by linarith [(mem_unitCube_iff.1 hxa.1 l).1, hδpos], by rw [hyj]; linarith⟩
          · rw [hyl l hlj]; exact mem_unitCube_iff.1 hxa.1 l
        · rw [hycost]
          have : p j * δ ≤ mkt.b i - cost p x := by
            have h2 : δ * p j ≤ (mkt.b i - cost p x) / (p j + 1) * p j :=
              mul_le_mul_of_nonneg_right hδ2 (hp j)
            have h3 : (mkt.b i - cost p x) / (p j + 1) * p j ≤ mkt.b i - cost p x := by
              rw [div_mul_eq_mul_div, div_le_iff₀ hp1]
              nlinarith
            nlinarith
          linarith
        · intro l hl
          rcases eq_or_ne l j with rfl | hlj
          · exact hτj
          · rw [hyl l hlj] at hl; exact hxa.2.2 l hl
      have hyutil : util mkt i x < util mkt i y := by
        have he : util mkt i y = util mkt i x + mkt.τ i j * δ - mkt.τ i j * 0 := by
          simp only [util, hy, sum_perturb]
        rw [he]
        have : 0 < mkt.τ i j * δ := mul_pos hτj hδpos
        linarith
      exact absurd (hmax y hyaff) (not_le.mpr hyutil)
  · -- `←`: the exchange argument.
    rintro ⟨hxa, hswap, hsat⟩
    refine ⟨hxa, fun y hy => ?_⟩
    rcases hsat with hcost | hall
    · -- Budget exactly exhausted: bound every coordinate by the marginal rate `ρ`.
      set S := Finset.univ.filter (fun j => x j < 1) with hS
      rcases S.eq_empty_or_nonempty with hSe | hSne
      · -- Nothing left to buy: `x` is `1` everywhere, hence pointwise maximal.
        have hx1 : ∀ j, x j = 1 := by
          intro j
          by_contra hj
          have hmem : j ∈ S := by
            simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
            exact lt_of_le_of_ne (mem_unitCube_iff.1 hxa.1 j).2 hj
          rw [hSe] at hmem; simp at hmem
        refine Finset.sum_le_sum fun j _ => ?_
        rw [hx1 j]
        exact mul_le_mul_of_nonneg_left (mem_unitCube_iff.1 hy.1 j).2 (mkt.τ_nonneg i j)
      · set ρ := S.sup' hSne (fun j => mkt.τ i j / p j) with hρ
        have hmemS : ∀ j, x j < 1 → j ∈ S := by
          intro j hj; simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hj
        have hρ0 : 0 ≤ ρ := by
          obtain ⟨j0, hj0⟩ := hSne
          exact le_trans (div_nonneg (mkt.τ_nonneg i j0) (hp j0))
            (Finset.le_sup' (fun j => mkt.τ i j / p j) hj0)
        -- Anything with room to spare is worth at most the marginal rate.
        have hle_rho : ∀ j, x j < 1 → mkt.τ i j ≤ ρ * p j := by
          intro j hj
          rcases (mkt.τ_nonneg i j).lt_or_eq with hτ | hτ
          · have hpj := price_pos_of_lt_one mkt p i hp hb hxa.1 hcost hswap hτ hj
            have := Finset.le_sup' (fun j => mkt.τ i j / p j) (hmemS j hj)
            rw [div_le_iff₀ hpj] at this
            linarith [this]
          · rw [← hτ]; exact mul_nonneg hρ0 (hp j)
        -- Anything held is worth at least the marginal rate.
        have hrho_le : ∀ k, 0 < x k → ρ * p k ≤ mkt.τ i k := by
          intro k hk
          obtain ⟨j0, hj0mem, hj0eq⟩ := Finset.exists_mem_eq_sup' hSne (fun j => mkt.τ i j / p j)
          have hj0 : x j0 < 1 := by
            simpa only [hS, Finset.mem_filter, Finset.mem_univ, true_and] using hj0mem
          have hsw := hswap j0 k hk hj0
          simp only [bpbLE] at hsw
          rcases (hp j0).lt_or_eq with hpj0 | hpj0
          · rw [hρ, hj0eq, div_mul_eq_mul_div, div_le_iff₀ hpj0]
            linarith [hsw]
          · have hτ0 : mkt.τ i j0 = 0 := by
              by_contra hne
              have := price_pos_of_lt_one mkt p i hp hb hxa.1 hcost hswap
                (lt_of_le_of_ne (mkt.τ_nonneg i j0) (Ne.symm hne)) hj0
              rw [← hpj0] at this; exact absurd this (lt_irrefl _)
            rw [hρ, hj0eq, hτ0, ← hpj0]
            simpa using mkt.τ_nonneg i k
        -- Pointwise: `τ · Δ ≤ ρ · p · Δ`, in every direction.
        have key : ∀ j, mkt.τ i j * (y j - x j) ≤ ρ * p j * (y j - x j) := by
          intro j
          rcases lt_trichotomy (y j) (x j) with hlt | heq | hgt
          · have hxj : 0 < x j := lt_of_le_of_lt (mem_unitCube_iff.1 hy.1 j).1 hlt
            nlinarith [hrho_le j hxj]
          · rw [heq]; simp
          · have hxj : x j < 1 := lt_of_lt_of_le hgt (mem_unitCube_iff.1 hy.1 j).2
            nlinarith [hle_rho j hxj]
        have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => key j)
        have e1 : ∑ j, mkt.τ i j * (y j - x j) = util mkt i y - util mkt i x := by
          simp [util, mul_sub, Finset.sum_sub_distrib]
        have e2 : ∑ j, ρ * p j * (y j - x j) = ρ * (cost p y - cost p x) := by
          simp [cost, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
        rw [e1, e2] at hsum
        have hcy : cost p y ≤ mkt.b i := hy.2.1
        nlinarith
    · -- Everything valuable already fully bought: `x` dominates pointwise.
      refine Finset.sum_le_sum fun j _ => ?_
      rcases (mkt.τ_nonneg i j).lt_or_eq with hτ | hτ
      · rw [hall j hτ]
        exact mul_le_mul_of_nonneg_left (mem_unitCube_iff.1 hy.1 j).2 hτ.le
      · rw [← hτ]; simp

/-- The bundle `x` is the greedy bundle for the consumption order `σ`:
buyer `i` buys as much of `σ 0` as she can, then as much of `σ 1` as she can, and so on,
skipping datasets of no value to her.

The `min 1 (max 0 ·)` clamps the purchase to `[0,1]`, and the subtracted sum is
what she has already spent on datasets earlier in the order.
A dataset of no value is skipped. A *free* dataset of positive value is taken in full. -/
@[expose] public def IsGreedy (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ) : Prop :=
  ∀ j, x (σ j) =
    if 0 < mkt.τ i (σ j) then
      if p (σ j) = 0 then 1
      else
        min 1 (max 0
          ((mkt.b i - ∑ k ∈ Finset.univ.filter (· < j), p (σ k) * x (σ k)) / p (σ j)))
    else 0

/-- **Greedy is optimal.** If `σ` orders the datasets by non-increasing bang-per-buck,
then the greedy bundle for `σ` is a demand. -/
public theorem isDemand_of_isGreedy (hp : IsNonnegVector p) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ j k, j ≤ k → bpbLE mkt p i (σ k) (σ j))
    (x : Fin m → ℝ) (hx : IsGreedy mkt p i σ x) :
    IsDemand mkt p i x := by
  classical
  -- Restate the greedy recursion at an arbitrary dataset `l` rather than a position.
  have hxσ : ∀ l : Fin m, x l =
      if 0 < mkt.τ i l then
        (if p l = 0 then 1
         else min 1 (max 0 ((mkt.b i -
           ∑ k ∈ Finset.univ.filter (· < σ.symm l), p (σ k) * x (σ k)) / p l)))
      else 0 := by
    intro l; simpa using hx (σ.symm l)
  -- Basic shape of the greedy bundle.
  have hcube : x ∈ unitCube m := by
    refine mem_unitCube_iff.2 fun l => ?_
    rw [hxσ l]
    split_ifs
    · exact ⟨zero_le_one, le_refl 1⟩
    · exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    · exact ⟨le_refl 0, zero_le_one⟩
  have hx0 : ∀ l, 0 ≤ x l := fun l => (mem_unitCube_iff.1 hcube l).1
  have hsupp : ∀ l, 0 < x l → 0 < mkt.τ i l := by
    intro l hl
    by_contra h
    push Not at h
    rw [hxσ l, if_neg (not_lt.mpr h)] at hl
    exact absurd hl (lt_irrefl 0)
  -- A free valuable dataset is taken in full.
  have hfree : ∀ l, 0 < mkt.τ i l → p l = 0 → x l = 1 := by
    intro l hτ hp0; rw [hxσ l, if_pos hτ, if_pos hp0]
  -- Prefix spending, indexed by how many positions of `σ` have been processed.
  set S : ℕ → ℝ := fun t => ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k:ℕ) < t),
    p (σ k) * x (σ k) with hS
  have hterm : ∀ k : Fin m, 0 ≤ p (σ k) * x (σ k) := fun k =>
    mul_nonneg (hp _) (hx0 _)
  have hSmono : ∀ {t t' : ℕ}, t ≤ t' → S t ≤ S t' := by
    intro t t' htt
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hterm k)
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    omega
  -- The prefix sum before position `k₀` is `S k₀.val`.
  have hSfilter : ∀ k₀ : Fin m,
      Finset.univ.filter (· < k₀) = Finset.univ.filter (fun k : Fin m => (k:ℕ) < (k₀:ℕ)) := by
    intro k₀; ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  -- Greedy never overspends: every prefix stays within budget.
  have hSle : ∀ t : ℕ, S t ≤ mkt.b i := by
    intro t
    induction t with
    | zero => simpa [hS] using mkt.b_nonneg i
    | succ t ih =>
      by_cases ht : t < m
      · set k₀ : Fin m := ⟨t, ht⟩ with hk₀
        have hins : Finset.univ.filter (fun k : Fin m => (k:ℕ) < t + 1)
            = insert k₀ (Finset.univ.filter (fun k : Fin m => (k:ℕ) < t)) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            hk₀, Fin.ext_iff]
          omega
        have hnot : k₀ ∉ Finset.univ.filter (fun k : Fin m => (k:ℕ) < t) := by
          simp [hk₀]
        have hsplit : S (t + 1) = p (σ k₀) * x (σ k₀) + S t := by
          simp only [hS, hins, Finset.sum_insert hnot]
        -- The greedy purchase at `k₀` costs at most the remaining budget.
        have hbound : p (σ k₀) * x (σ k₀) ≤ mkt.b i - S t := by
          have hpre : (Finset.univ.filter (· < k₀)) =
              Finset.univ.filter (fun k : Fin m => (k:ℕ) < t) := by
            rw [hSfilter k₀]
          have hval := hx k₀
          rw [hpre] at hval
          by_cases hτ : 0 < mkt.τ i (σ k₀)
          · by_cases hp0 : p (σ k₀) = 0
            · rw [hp0]; simp; linarith [ih]
            · have hppos : 0 < p (σ k₀) := lt_of_le_of_ne (hp _) (Ne.symm hp0)
              have hrem : 0 ≤ mkt.b i - S t := by linarith [ih]
              have hmaxeq : max 0 ((mkt.b i - S t) / p (σ k₀))
                  = (mkt.b i - S t) / p (σ k₀) :=
                max_eq_right (div_nonneg hrem hppos.le)
              rw [hval, if_pos hτ, if_neg hp0, hmaxeq]
              have hle : min 1 ((mkt.b i - S t) / p (σ k₀))
                  ≤ (mkt.b i - S t) / p (σ k₀) := min_le_right _ _
              calc p (σ k₀) * min 1 ((mkt.b i - S t) / p (σ k₀))
                  ≤ p (σ k₀) * ((mkt.b i - S t) / p (σ k₀)) :=
                    mul_le_mul_of_nonneg_left hle hppos.le
                _ = mkt.b i - S t := by field_simp
          · rw [hval, if_neg hτ, mul_zero]; linarith [ih]
        linarith [hsplit, hbound]
      · have : Finset.univ.filter (fun k : Fin m => (k:ℕ) < t + 1)
            = Finset.univ.filter (fun k : Fin m => (k:ℕ) < t) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have := k.isLt
          omega
        simpa [hS, this] using ih
  -- Total cost is the last prefix.
  have hcostS : cost p x = S m := by
    have h1 : Finset.univ.filter (fun k : Fin m => (k:ℕ) < m) = Finset.univ := by
      ext k; simp
    simp only [hS, h1, cost]
    exact (Equiv.sum_comp σ (fun l => p l * x l)).symm
  have hcostle : cost p x ≤ mkt.b i := by rw [hcostS]; exact hSle m
  have haff : x ∈ affordableSet mkt p i := ⟨hcube, hcostle, hsupp⟩
  -- When a valuable dataset is not fully bought, the budget is exactly used up.
  have hexhaust : ∀ l : Fin m, 0 < mkt.τ i l → x l < 1 → S ((σ.symm l : Fin m) : ℕ) + p l * x l
      = mkt.b i := by
    intro l hτ hlt
    have hp0 : p l ≠ 0 := by
      intro h0; rw [hfree l hτ h0] at hlt; exact absurd hlt (lt_irrefl 1)
    have hppos : 0 < p l := lt_of_le_of_ne (hp l) (Ne.symm hp0)
    have hval := hxσ l
    rw [if_pos hτ, if_neg hp0, hSfilter (σ.symm l)] at hval
    have hrem : 0 ≤ mkt.b i - S ((σ.symm l : Fin m) : ℕ) := by
      linarith [hSle ((σ.symm l : Fin m) : ℕ)]
    have hmaxeq : max 0 ((mkt.b i - S ((σ.symm l : Fin m) : ℕ)) / p l)
        = (mkt.b i - S ((σ.symm l : Fin m) : ℕ)) / p l := max_eq_right (div_nonneg hrem hppos.le)
    rw [hmaxeq] at hval
    -- `x l < 1` forces the `min` to pick the budget-limited branch.
    have hmin : min 1 ((mkt.b i - S ((σ.symm l : Fin m) : ℕ)) / p l)
        = (mkt.b i - S ((σ.symm l : Fin m) : ℕ)) / p l := by
      rcases min_cases 1 ((mkt.b i - S ((σ.symm l : Fin m) : ℕ)) / p l) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at hval; exact absurd (hval ▸ hlt) (lt_irrefl 1)
      · exact he
    rw [hmin] at hval
    rw [hval]
    field_simp
    ring
  rcases (mkt.b_nonneg i).lt_or_eq with hb | hb
  · -- Positive budget: verify the two local conditions and invoke `isDemand_iff`.
    rw [isDemand_iff mkt p i hp hb]
    refine ⟨haff, ?_, ?_⟩
    · -- No improving swap.
      intro j k hxk hxj
      simp only [bpbLE]
      rcases (mkt.τ_nonneg i j).lt_or_eq with hτj | hτj
      · -- `j` is valuable but not fully bought, so the budget ran out at `j`.
        have hpj : p j ≠ 0 := by
          intro h0; rw [hfree j hτj h0] at hxj; exact absurd hxj (lt_irrefl 1)
        have hppos : 0 < p j := lt_of_le_of_ne (hp j) (Ne.symm hpj)
        have hex := hexhaust j hτj hxj
        by_cases hpk : p k = 0
        · rw [hpk, mul_zero]; exact mul_nonneg (mkt.τ_nonneg i k) (hp j)
        · -- `k` is bought at a positive price, so its prefix was strictly under budget.
          have hkpos : 0 < p k := lt_of_le_of_ne (hp k) (Ne.symm hpk)
          have hτk := hsupp k hxk
          have hvalk := hxσ k
          rw [if_pos hτk, if_neg hpk, hSfilter (σ.symm k)] at hvalk
          have hSk : S ((σ.symm k : Fin m) : ℕ) < mkt.b i := by
            by_contra hcon
            push Not at hcon
            have : max 0 ((mkt.b i - S ((σ.symm k : Fin m) : ℕ)) / p k) = 0 :=
              max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hkpos.le)
            rw [this, min_eq_right zero_le_one] at hvalk
            rw [hvalk] at hxk; exact absurd hxk (lt_irrefl 0)
          -- Hence `k` comes no later than `j` in the greedy order.
          have hpos : (σ.symm k : Fin m) ≤ (σ.symm j : Fin m) := by
            by_contra hcon
            push Not at hcon
            have hge : ((σ.symm j : Fin m) : ℕ) + 1 ≤ ((σ.symm k : Fin m) : ℕ) := by
              have := hcon; rw [Fin.lt_def] at this; omega
            have h1 : S (((σ.symm j : Fin m) : ℕ) + 1) ≤ S ((σ.symm k : Fin m) : ℕ) :=
              hSmono hge
            have h2 : S (((σ.symm j : Fin m) : ℕ) + 1) = mkt.b i := by
              set t := ((σ.symm j : Fin m) : ℕ) with htdef
              have ht : t < m := (σ.symm j).isLt
              set k₀ : Fin m := ⟨t, ht⟩ with hk₀
              have hk₀eq : k₀ = σ.symm j := by simp [hk₀, htdef]
              have hins : Finset.univ.filter (fun k : Fin m => (k:ℕ) < t + 1)
                  = insert k₀ (Finset.univ.filter (fun k : Fin m => (k:ℕ) < t)) := by
                ext k
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                  hk₀, Fin.ext_iff]
                omega
              have hnot : k₀ ∉ Finset.univ.filter (fun k : Fin m => (k:ℕ) < t) := by
                simp [hk₀]
              have : S (t + 1) = p (σ k₀) * x (σ k₀) + S t := by
                simp only [hS, hins, Finset.sum_insert hnot]
              rw [this, hk₀eq]
              simp only [Equiv.apply_symm_apply]
              linarith [hex]
            linarith [hSle ((σ.symm k : Fin m) : ℕ)]
          have := hσ (σ.symm k) (σ.symm j) hpos
          simpa only [bpbLE, Equiv.apply_symm_apply] using this
      · rw [← hτj]; simpa using mul_nonneg (mkt.τ_nonneg i k) (hp j)
    · -- No idle budget.
      by_cases hall : ∀ j, 0 < mkt.τ i j → x j = 1
      · exact Or.inr hall
      · left
        push Not at hall
        obtain ⟨j, hτj, hxj1⟩ := hall
        have hxj : x j < 1 := lt_of_le_of_ne (mem_unitCube_iff.1 hcube j).2 hxj1
        have hex := hexhaust j hτj hxj
        -- The budget is used up by position `σ.symm j`, and nothing more is spent after.
        refine le_antisymm hcostle ?_
        rw [hcostS]
        have ht : ((σ.symm j : Fin m) : ℕ) < m := (σ.symm j).isLt
        set t := ((σ.symm j : Fin m) : ℕ) with htdef
        set k₀ : Fin m := ⟨t, ht⟩ with hk₀
        have hk₀eq : k₀ = σ.symm j := by simp [hk₀, htdef]
        have hins : Finset.univ.filter (fun k : Fin m => (k:ℕ) < t + 1)
            = insert k₀ (Finset.univ.filter (fun k : Fin m => (k:ℕ) < t)) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            hk₀, Fin.ext_iff]
          omega
        have hnot : k₀ ∉ Finset.univ.filter (fun k : Fin m => (k:ℕ) < t) := by simp [hk₀]
        have hsplit : S (t + 1) = p (σ k₀) * x (σ k₀) + S t := by
          simp only [hS, hins, Finset.sum_insert hnot]
        have hb1 : S (t + 1) = mkt.b i := by
          rw [hsplit, hk₀eq]; simp only [Equiv.apply_symm_apply]; linarith [hex]
        exact le_trans (le_of_eq hb1.symm) (hSmono ht)
  · -- Zero budget: only free datasets can be bought, and greedy takes all of them.
    refine ⟨haff, fun y hy => ?_⟩
    have hzero : ∀ l, p l * y l = 0 := by
      intro l
      have hnn : ∀ l', 0 ≤ p l' * y l' := fun l' =>
        mul_nonneg (hp l') (mem_unitCube_iff.1 hy.1 l').1
      have hsum : cost p y ≤ 0 := by rw [hb]; exact hy.2.1
      by_contra hne
      have hpos : 0 < p l * y l := lt_of_le_of_ne (hnn l) (Ne.symm hne)
      have : 0 < cost p y :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ l))
      linarith
    refine Finset.sum_le_sum fun l _ => ?_
    rcases (mkt.τ_nonneg i l).lt_or_eq with hτ | hτ
    · by_cases hp0 : p l = 0
      · rw [hfree l hτ hp0]
        exact mul_le_mul_of_nonneg_left (mem_unitCube_iff.1 hy.1 l).2 hτ.le
      · have hppos : 0 < p l := lt_of_le_of_ne (hp l) (Ne.symm hp0)
        have hyl : y l = 0 := by
          have := hzero l
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hp0
          · exact h
        rw [hyl, mul_zero]
        exact mul_nonneg hτ.le (hx0 l)
    · rw [← hτ]; simp

/-! ### Existence of demands, for two datasets -/

/-- Some consumption order sorts two datasets by non-increasing bang-per-buck. -/
private theorem exists_sorted_two {n : ℕ} (M : Instance n 2) (P : Fin 2 → ℝ) (I : Fin n) :
    ∃ σ : Equiv.Perm (Fin 2), ∀ j k, j ≤ k → bpbLE M P I (σ k) (σ j) := by
  have key : ∀ σ : Equiv.Perm (Fin 2), bpbLE M P I (σ 1) (σ 0) →
      ∀ j k : Fin 2, j ≤ k → bpbLE M P I (σ k) (σ j) := by
    intro σ hσ j k hjk
    fin_cases j <;> fin_cases k <;> simp_all [bpbLE]
  rcases le_total (M.τ I 1 * P 0) (M.τ I 0 * P 1) with hle | hle
  · exact ⟨Equiv.refl _, key _ (by simpa [bpbLE] using hle)⟩
  · refine ⟨Equiv.swap 0 1, key _ ?_⟩
    simpa [bpbLE, Equiv.swap_apply_left, Equiv.swap_apply_right] using hle

/-- With two datasets, a greedy bundle exists for every consumption order. -/
private theorem exists_isGreedy_two {n : ℕ} (M : Instance n 2) (P : Fin 2 → ℝ) (I : Fin n)
    (σ : Equiv.Perm (Fin 2)) : ∃ x, IsGreedy M P I σ x := by
  classical
  set A : ℝ := if 0 < M.τ I (σ 0) then
      (if P (σ 0) = 0 then 1 else min 1 (max 0 (M.b I / P (σ 0)))) else 0 with hA
  set B : ℝ := if 0 < M.τ I (σ 1) then
      (if P (σ 1) = 0 then 1
       else min 1 (max 0 ((M.b I - P (σ 0) * A) / P (σ 1)))) else 0 with hB
  have hne : σ 1 ≠ σ 0 := fun h => absurd (σ.injective h) (by decide)
  refine ⟨fun l => if l = σ 0 then A else B, ?_⟩
  intro j
  have h0 : (Finset.univ.filter (· < (0 : Fin 2))) = ∅ := by decide
  have h1 : (Finset.univ.filter (· < (1 : Fin 2))) = {0} := by decide
  fin_cases j
  · simp only [Fin.zero_eta, h0, Finset.sum_empty, sub_zero]
    exact hA
  · simp only [Fin.mk_one, if_neg hne, h1, Finset.sum_singleton]
    exact hB

/-- **Demands exist**, for two datasets and nonnegative prices. -/
public theorem exists_demand_two {n : ℕ} (M : Instance n 2) (P : Fin 2 → ℝ) (I : Fin n)
    (hP : IsNonnegVector P) : ∃ x, IsDemand M P I x := by
  obtain ⟨σ, hσ⟩ := exists_sorted_two M P I
  obtain ⟨x, hx⟩ := exists_isGreedy_two M P I σ
  exact ⟨x, isDemand_of_isGreedy M P I hP σ hσ x hx⟩

end DataMktOligo.LinDataMkt
