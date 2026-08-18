module

public import DataMktOligo.LinDataMkt.Revenue
public import DataMktOligo.LinDataMkt.Greedy
public import DataMktOligo.MuOpt.Revenue
public import DataMktOligo.NashInapprox.Instance
import DataMktOligo.NashInapprox.Demand
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The bridge: market revenue vs. the closed forms of `MuOpt`

`DataMktOligo.MuOpt` *stipulates* closed forms for the sellers' revenues, their best responses,
and the instability ratio `μ`. This file states that those stipulations are correct:
they agree with what the market of `DataMktOligo.LinDataMkt` actually produces for
the instance of `DataMktOligo.NashInapprox.Instance`.

## Main results

* `V_nonempty`: some revenue vector is attainable.
* `mem_V_iff_mem_muOptV`: the market's valid-revenue set is `MuOpt.V`.
* `bestResponseRevenue_seller0`, `bestResponseRevenue_seller1`:
  the sellers' best-response revenues are `MuOpt.r1star` and `MuOpt.r2star`.
* `not_isApproxNE_of_lt_μ`: if `μ(p,q)` exceeds `c`, then `(p,q)` is not a `c`-approximate
  Nash equilibrium. This is the direction the main result needs.

**The `cap` convention**: `MuOpt.μ` uses a finite `cap` in place of `∞` for the `x/0` convention,
whereas `LinDataMkt.IsApproxNE` is stated multiplicatively and never divides.
The two agree only for `c < cap`, which is why `not_isApproxNE_of_lt_μ` carries that hypothesis.
-/

@[expose] public section

namespace DataMktOligo.NashInapprox

open DataMktOligo.MuOpt (Constraints cap μ ratio r1star r2star)

variable {α β ν : ℝ}

/-! ### Demands exist -/

/-- Every buyer has at least one demand at nonnegative prices,
so the set of valid revenue vectors is nonempty.
A witness comes from `LinDataMkt.isDemand_of_isGreedy`. -/
public theorem V_nonempty (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (LinDataMkt.V (inst h) ![p, q]).Nonempty := by
  classical
  have hP : LinDataMkt.IsNonnegVector ![p, q] := isNonnegVector_prices hp hq
  choose x hx using fun i : Fin 2 =>
    LinDataMkt.exists_demand_two (inst h) ![p, q] i hP
  exact ⟨LinDataMkt.revenue (inst h) ![p, q] x, x, hx, rfl⟩

/-! ### The valid-revenue set -/

/-- Seller revenues from a purchase profile, with the poor buyer counted `ν` times. -/
private theorem revenue_two (h : Constraints α β ν) (p q : ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    LinDataMkt.revenue (inst h) ![p, q] x 0 = ν * (p * x 0 0) + p * x 1 0 ∧
    LinDataMkt.revenue (inst h) ![p, q] x 1 = ν * (q * x 0 1) + q * x 1 1 := by
  constructor <;> simp [LinDataMkt.revenue, Fin.sum_univ_succ, inst]

/-- **The closed form for `V` is correct**:
A pair of seller revenues is attainable in the market exactly when it lies in `MuOpt.V`.
Stated componentwise rather than as an equality of sets because
the market's revenue vectors live in `Fin 2 → ℝ` and `MuOpt.V`'s live in `ℝ × ℝ`. -/
public theorem mem_V_iff_mem_muOptV (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {r : Fin 2 → ℝ} :
    r ∈ LinDataMkt.V (inst h) ![p, q] ↔ (r 0, r 1) ∈ DataMktOligo.MuOpt.V α β ν p q := by
  have hν : 0 < ν := by linarith [h.c1_mid, h.c1_hi]
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hr0, hr1⟩ := rich_spend h hp hq (hx 1)
    obtain ⟨e0, e1⟩ := revenue_two h p q x
    rw [hr0] at e0
    rw [hr1, mul_zero, add_zero] at e1
    simp only [DataMktOligo.MuOpt.V]
    split_ifs with c1 c2 c3
    · obtain ⟨s0, s1⟩ := poor_spend_of_add_le h hp hq (hx 0) c1
      have m0 : min p (max 0 (1 - q)) = p := by
        rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - q)]; exact min_eq_left (by linarith)
      have m1 : min q (max 0 (1 - p)) = q := by
        rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - p)]; exact min_eq_left (by linarith)
      simp only [Set.mem_singleton_iff, Prod.mk.injEq,
        DataMktOligo.MuOpt.r1lo, DataMktOligo.MuOpt.r2lo, m0, m1]
      rw [e0, e1, s0, s1]
      exact ⟨by ring, by ring⟩
    · obtain ⟨s0, s1⟩ := poor_spend_of_lt h hp hq (hx 0) c2
      simp only [Set.mem_singleton_iff, Prod.mk.injEq,
        DataMktOligo.MuOpt.r1hi, DataMktOligo.MuOpt.r2lo]
      rw [e0, e1, s0, s1]
      exact ⟨by ring, by ring⟩
    · obtain ⟨s1, s0⟩ := poor_spend_of_gt h hp hq (hx 0) c3
      simp only [Set.mem_singleton_iff, Prod.mk.injEq,
        DataMktOligo.MuOpt.r1lo, DataMktOligo.MuOpt.r2hi]
      rw [e0, e1, s0, s1]
      exact ⟨by ring, by ring⟩
    · have hsum := poor_spend_sum h hp hq (hx 0) (by linarith [not_le.mp c1])
      simp only [Set.mem_ofPred_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [DataMktOligo.MuOpt.r1lo, e0]
        linarith [mul_le_mul_of_nonneg_left (poor_spend0_ge h hp hq (hx 0)) hν.le]
      · simp only [DataMktOligo.MuOpt.r1hi, e0]
        linarith [mul_le_mul_of_nonneg_left (poor_spend0_le h hp hq (hx 0)) hν.le]
      · simp only [DataMktOligo.MuOpt.r2lo, e1]
        linarith [mul_le_mul_of_nonneg_left (poor_spend1_ge h hp hq (hx 0)) hν.le]
      · simp only [DataMktOligo.MuOpt.r2hi, e1]
        linarith [mul_le_mul_of_nonneg_left (poor_spend1_le h hp hq (hx 0)) hν.le]
      · simp only [e0, e1]
        have hd : ν * (p * x 0 0) + ν * (q * x 0 1) = ν := by rw [← mul_add, hsum, mul_one]
        linarith
  · intro hmem
    obtain ⟨zr, hzr⟩ := LinDataMkt.exists_demand_two (inst h) ![p, q] 1
      (isNonnegVector_prices hp hq)
    obtain ⟨hzr0, hzr1⟩ := rich_spend h hp hq hzr
    simp only [DataMktOligo.MuOpt.V] at hmem
    split_ifs at hmem with c1 c2 c3
    · obtain ⟨zp, hzp⟩ := LinDataMkt.exists_demand_two (inst h) ![p, q] 0
        (isNonnegVector_prices hp hq)
      obtain ⟨s0, s1⟩ := poor_spend_of_add_le h hp hq hzp c1
      have m0 : min p (max 0 (1 - q)) = p := by
        rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - q)]; exact min_eq_left (by linarith)
      have m1 : min q (max 0 (1 - p)) = q := by
        rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - p)]; exact min_eq_left (by linarith)
      simp only [Set.mem_singleton_iff, Prod.mk.injEq,
        DataMktOligo.MuOpt.r1lo, DataMktOligo.MuOpt.r2lo, m0, m1] at hmem
      obtain ⟨e0, e1⟩ := revenue_two h p q ![zp, zr]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
      refine ⟨![zp, zr], ?_, ?_⟩
      · intro i; fin_cases i
        · simpa using hzp
        · simpa using hzr
      · funext j; fin_cases j
        · simp only [Fin.zero_eta, e0, s0, hzr0]; linarith [hmem.1]
        · simp only [Fin.mk_one, e1, s1, hzr1, mul_zero]; linarith [hmem.2]
    · obtain ⟨zp, hzp⟩ := LinDataMkt.exists_demand_two (inst h) ![p, q] 0
        (isNonnegVector_prices hp hq)
      obtain ⟨s0, s1⟩ := poor_spend_of_lt h hp hq hzp c2
      simp only [Set.mem_singleton_iff, Prod.mk.injEq,
        DataMktOligo.MuOpt.r1hi, DataMktOligo.MuOpt.r2lo] at hmem
      obtain ⟨e0, e1⟩ := revenue_two h p q ![zp, zr]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
      refine ⟨![zp, zr], ?_, ?_⟩
      · intro i; fin_cases i
        · simpa using hzp
        · simpa using hzr
      · funext j; fin_cases j
        · simp only [Fin.zero_eta, e0, s0, hzr0]; linarith [hmem.1]
        · simp only [Fin.mk_one, e1, s1, hzr1, mul_zero]; linarith [hmem.2]
    · obtain ⟨zp, hzp⟩ := LinDataMkt.exists_demand_two (inst h) ![p, q] 0
        (isNonnegVector_prices hp hq)
      obtain ⟨s1, s0⟩ := poor_spend_of_gt h hp hq hzp c3
      simp only [Set.mem_singleton_iff, Prod.mk.injEq,
        DataMktOligo.MuOpt.r1lo, DataMktOligo.MuOpt.r2hi] at hmem
      obtain ⟨e0, e1⟩ := revenue_two h p q ![zp, zr]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
      refine ⟨![zp, zr], ?_, ?_⟩
      · intro i; fin_cases i
        · simpa using hzp
        · simpa using hzr
      · funext j; fin_cases j
        · simp only [Fin.zero_eta, e0, s0, hzr0]; linarith [hmem.1]
        · simp only [Fin.mk_one, e1, s1, hzr1, mul_zero]; linarith [hmem.2]
    · -- Knife edge: build the poor buyer's split from the target revenue.
      have htie : p = α * q := le_antisymm (not_lt.mp c3) (not_lt.mp c2)
      have hα : 0 < α := by linarith [h.c1_lo]
      have hpq1 : 1 < p + q := not_le.mp c1
      have hqpos : 0 < q := by
        rcases eq_or_lt_of_le hq with hq0 | hq0
        · rw [htie, ← hq0] at hpq1; simp at hpq1; linarith
        · exact hq0
      have hppos : 0 < p := by rw [htie]; positivity
      simp only [Set.mem_ofPred_eq, DataMktOligo.MuOpt.r1lo, DataMktOligo.MuOpt.r1hi,
        DataMktOligo.MuOpt.r2lo, DataMktOligo.MuOpt.r2hi] at hmem
      obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hmem
      set t : ℝ := r 1 / ν with ht
      have hνne : ν ≠ 0 := hν.ne'
      have hνt : ν * t = r 1 := by rw [ht]; field_simp
      -- `t` is the poor buyer's spending with seller `1`.
      have ht0 : 0 ≤ t := by
        have hm : (0:ℝ) ≤ min q (max 0 (1 - p)) := le_min hq (le_max_left _ _)
        have h2 : 0 ≤ r 1 := le_trans (mul_nonneg hν.le hm) hb3
        rw [ht]; positivity
      have htq : t ≤ q := by
        have hm : min q 1 ≤ q := min_le_left _ _
        have h1 : r 1 ≤ ν * q := le_trans hb4 (mul_le_mul_of_nonneg_left hm hν.le)
        rw [ht, div_le_iff₀ hν]; linarith
      have ht1 : t ≤ 1 := by
        have hm : min q 1 ≤ 1 := min_le_right _ _
        have h1 : r 1 ≤ ν * 1 := le_trans hb4 (mul_le_mul_of_nonneg_left hm hν.le)
        rw [ht, div_le_iff₀ hν]; linarith
      have htp : 1 - p ≤ t := by
        have hmp : min p 1 ≤ p := min_le_left _ _
        have hstep : ν * min p 1 ≤ ν * p := mul_le_mul_of_nonneg_left hmp hν.le
        have h1 : ν * (1 - p) ≤ r 1 := by nlinarith
        rw [ht, le_div_iff₀ hν]; linarith
      have hpne : p ≠ 0 := hppos.ne'
      have hqne : q ≠ 0 := hqpos.ne'
      set zp : Fin 2 → ℝ := ![(1 - t) / p, t / q] with hzpdef
      have hzpe0 : zp 0 = (1 - t) / p := rfl
      have hzpe1 : zp 1 = t / q := rfl
      have hzp0 : p * zp 0 = 1 - t := by rw [hzpe0]; field_simp
      have hzp1 : q * zp 1 = t := by rw [hzpe1]; field_simp
      have hzp : LinDataMkt.IsDemand (inst h) ![p, q] 0 zp := by
        refine poor_isDemand_of_tie h hp hq htie ?_ ?_ ?_ ?_ ?_
        · rw [hzpe0]; positivity
        · rw [hzpe0, div_le_one hppos]; linarith
        · rw [hzpe1]; positivity
        · rw [hzpe1, div_le_one hqpos]; linarith
        · rw [hzp0, hzp1]; ring
      obtain ⟨e0, e1⟩ := revenue_two h p q ![zp, zr]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
      refine ⟨![zp, zr], ?_, ?_⟩
      · intro i; fin_cases i
        · simpa using hzp
        · simpa using hzr
      · funext j; fin_cases j
        · simp only [Fin.zero_eta, e0, hzp0, hzr0]; linarith
        · simp only [Fin.mk_one, e1, hzp1, hzr1, mul_zero]; linarith

/-! ### Best-response revenues -/

/-! Deviating changes exactly one coordinate of the price vector. -/

private theorem update_prices_one (p q q' : ℝ) : Function.update ![p, q] 1 q' = ![p, q'] := by
  funext j; fin_cases j <;> simp [Function.update]

private theorem update_prices_zero (p q p' : ℝ) : Function.update ![p, q] 0 p' = ![p', q] := by
  funext j; fin_cases j <;> simp [Function.update]

private theorem mem_deviation_one (h : Constraints α β ν) {p q y : ℝ} :
    y ∈ LinDataMkt.deviationRevenues (inst h) ![p, q] 1 ↔
      ∃ q' : ℝ, 0 ≤ q' ∧ ∃ r ∈ LinDataMkt.V (inst h) ![p, q'], y = r 1 := by
  constructor
  · rintro ⟨q', hq', r, hr, rfl⟩
    exact ⟨q', hq', r, by rwa [update_prices_one] at hr, rfl⟩
  · rintro ⟨q', hq', r, hr, rfl⟩
    exact ⟨q', hq', r, by rwa [update_prices_one], rfl⟩

private theorem mem_deviation_zero (h : Constraints α β ν) {p q y : ℝ} :
    y ∈ LinDataMkt.deviationRevenues (inst h) ![p, q] 0 ↔
      ∃ p' : ℝ, 0 ≤ p' ∧ ∃ r ∈ LinDataMkt.V (inst h) ![p', q], y = r 0 := by
  constructor
  · rintro ⟨p', hp', r, hr, rfl⟩
    exact ⟨p', hp', r, by rwa [update_prices_zero] at hr, rfl⟩
  · rintro ⟨p', hp', r, hr, rfl⟩
    exact ⟨p', hp', r, by rwa [update_prices_zero], rfl⟩

/-! Seller `1`'s revenue at an arbitrary price, read off `MuOpt.V`. -/

/-- Seller `1` never earns more than `ν·min(q', 1)`, and when she is *not* the
best-bang-per-buck seller she earns at most `ν·max(0, 1-p)`. -/
private theorem seller1_rev_le (h : Constraints α β ν) {p q' r1 r2 : ℝ} (hp : 0 ≤ p) (_hq' : 0 ≤ q')
    (hr : (r1, r2) ∈ DataMktOligo.MuOpt.V α β ν p q') :
    r2 ≤ ν * min q' 1 ∧ (p < α * q' → r2 ≤ ν * max 0 (1 - p)) := by
  have hν : 0 < ν := by linarith [h.c1_mid, h.c1_hi]
  have hm1 : max 0 (1 - p) ≤ 1 := max_le (by norm_num) (by linarith)
  simp only [DataMktOligo.MuOpt.V] at hr
  split_ifs at hr with c1 c2 c3
  · simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r2lo] at hr
    refine ⟨?_, fun _ => ?_⟩
    · rw [hr.2]
      exact mul_le_mul_of_nonneg_left (min_le_min_left _ hm1) hν.le
    · rw [hr.2]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) hν.le
  · simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r2lo] at hr
    refine ⟨?_, fun _ => ?_⟩
    · rw [hr.2]
      exact mul_le_mul_of_nonneg_left (min_le_min_left _ hm1) hν.le
    · rw [hr.2]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) hν.le
  · simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r2hi] at hr
    exact ⟨le_of_eq hr.2, fun hlt => absurd hlt (not_lt.mpr (le_of_lt c3))⟩
  · simp only [Set.mem_ofPred_eq, DataMktOligo.MuOpt.r2hi] at hr
    exact ⟨hr.2.2.2.1, fun hlt => absurd hlt c2⟩

/-- On the low side, when seller `1` prices strictly below `p/α` she earns exactly
`ν·min(q', 1)`: both the `p + q' ≤ 1` and the `p > α·q'` branches give that value. -/
private theorem seller1_rev_of_gt (_h : Constraints α β ν) {p q' r1 r2 : ℝ} (hp : 0 ≤ p)
    (_hq' : 0 ≤ q') (hgt : α * q' < p) (hr : (r1, r2) ∈ DataMktOligo.MuOpt.V α β ν p q') :
    r2 = ν * min q' 1 := by
  simp only [DataMktOligo.MuOpt.V] at hr
  by_cases c1 : p + q' ≤ 1
  · rw [if_pos c1] at hr
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r2lo] at hr
    rw [hr.2, max_eq_right (by linarith : (0:ℝ) ≤ 1 - p),
      min_eq_left (by linarith : q' ≤ 1 - p), min_eq_left (by linarith : q' ≤ 1)]
  · rw [if_neg c1, if_neg (not_lt.mpr hgt.le), if_pos hgt] at hr
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r2hi] at hr
    exact hr.2

/-- On the high side, when seller `1` prices strictly above `p/α` she earns exactly
`ν·max(0, 1-p)`, provided her price is large enough to absorb the poor buyer's leftovers. -/
private theorem seller1_rev_of_lt (_h : Constraints α β ν) {p q' r1 r2 : ℝ} (_hp : 0 ≤ p)
    (_hq' : 0 ≤ q') (hlt : p < α * q') (hbig : max 0 (1 - p) ≤ q')
    (hr : (r1, r2) ∈ DataMktOligo.MuOpt.V α β ν p q') :
    r2 = ν * max 0 (1 - p) := by
  simp only [DataMktOligo.MuOpt.V] at hr
  by_cases c1 : p + q' ≤ 1
  · rw [if_pos c1] at hr
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r2lo] at hr
    rw [hr.2, min_eq_right hbig]
  · rw [if_neg c1, if_pos hlt] at hr
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r2lo] at hr
    rw [hr.2, min_eq_right hbig]


/-- `min` moves by at most as much as its argument does. -/
private theorem min_le_min_add {a c b : ℝ} (hac : a ≤ c) : min c b ≤ min a b + (c - a) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]
    exact le_trans (min_le_left _ _) (by linarith)
  · rw [min_eq_right hab]
    exact le_trans (min_le_right _ _) (by linarith)

/-! Seller `0`'s revenue at an arbitrary price, read off `MuOpt.V`. -/

private theorem seller0_rev_le (h : Constraints α β ν) {p' q r1 r2 : ℝ} (_hp' : 0 ≤ p')
    (hq : 0 ≤ q) (hr : (r1, r2) ∈ DataMktOligo.MuOpt.V α β ν p' q) :
    r1 ≤ min p' β + ν * min p' 1 := by
  have hν : 0 < ν := by linarith [h.c1_mid, h.c1_hi]
  have hm : max 0 (1 - q) ≤ 1 := max_le (by norm_num) (by linarith)
  have hkey : min p' (max 0 (1 - q)) ≤ min p' 1 := min_le_min (le_refl _) hm
  simp only [DataMktOligo.MuOpt.V] at hr
  split_ifs at hr with c1 c2 c3
  · simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r1lo] at hr
    rw [hr.1]
    linarith [mul_le_mul_of_nonneg_left hkey hν.le]
  · simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r1hi] at hr
    exact le_of_eq hr.1
  · simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r1lo] at hr
    rw [hr.1]
    linarith [mul_le_mul_of_nonneg_left hkey hν.le]
  · simp only [Set.mem_ofPred_eq, DataMktOligo.MuOpt.r1hi] at hr
    exact hr.2.1

/-- Pricing strictly above `α·q` makes seller `0` second choice for the poor buyer. -/
private theorem seller0_rev_of_gt (_h : Constraints α β ν) {p' q r1 r2 : ℝ} (_hp' : 0 ≤ p')
    (_hq : 0 ≤ q) (hgt : α * q < p') (hr : (r1, r2) ∈ DataMktOligo.MuOpt.V α β ν p' q) :
    r1 = min p' β + ν * min p' (max 0 (1 - q)) := by
  simp only [DataMktOligo.MuOpt.V] at hr
  by_cases c1 : p' + q ≤ 1
  · rw [if_pos c1] at hr
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r1lo] at hr
    exact hr.1
  · rw [if_neg c1, if_neg (not_lt.mpr hgt.le), if_pos hgt] at hr
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r1lo] at hr
    exact hr.1

/-- Pricing strictly below `α·q` makes seller `0` first choice, so she fills the poor
buyer's budget first. -/
private theorem seller0_rev_of_lt (_h : Constraints α β ν) {p' q r1 r2 : ℝ} (_hp' : 0 ≤ p')
    (hq : 0 ≤ q) (hlt : p' < α * q) (hr : (r1, r2) ∈ DataMktOligo.MuOpt.V α β ν p' q) :
    r1 = min p' β + ν * min p' 1 := by
  simp only [DataMktOligo.MuOpt.V] at hr
  by_cases c1 : p' + q ≤ 1
  · rw [if_pos c1] at hr
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r1lo] at hr
    rw [hr.1, max_eq_right (by linarith : (0:ℝ) ≤ 1 - q),
      min_eq_left (by linarith : p' ≤ 1 - q), min_eq_left (by linarith : p' ≤ 1)]
  · rw [if_neg c1, if_pos hlt] at hr
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, DataMktOligo.MuOpt.r1hi] at hr
    exact hr.1

/-- **The closed form for `r₁*` is correct**: seller `0`'s best-response revenue,
given that seller `1` charges `q`, is `MuOpt.r1star`.
Note it does not depend on seller `0`'s own current price `p`. -/
public theorem bestResponseRevenue_seller0 (h : Constraints α β ν) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    LinDataMkt.bestResponseRevenue (inst h) ![p, q] 0 = r1star α β ν q := by
  have hν : 0 < ν := by linarith [h.c1_mid, h.c1_hi]
  have hα : 0 < α := by linarith [h.c1_lo]
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have haq : 0 ≤ α * q := by positivity
  have hm1 : max 0 (1 - q) ≤ 1 := max_le (by norm_num) (by linarith)
  simp only [LinDataMkt.bestResponseRevenue]
  set S := LinDataMkt.deviationRevenues (inst h) ![p, q] 0 with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨r, hr⟩ := V_nonempty h hp hq
    exact ⟨r 0, (mem_deviation_zero h).2 ⟨p, hp, r, hr, rfl⟩⟩
  -- Every deviation earns at most `r₁*(q)`.
  have hub : ∀ y ∈ S, y ≤ r1star α β ν q := by
    rintro y hy
    obtain ⟨p', hp', r, hr, rfl⟩ := (mem_deviation_zero h).1 hy
    have hrM := (mem_V_iff_mem_muOptV h hp' hq).1 hr
    simp only [DataMktOligo.MuOpt.r1star]
    rcases lt_or_ge (α * q) p' with hc | hc
    · -- Second choice: bounded by the `p' → ∞` limit.
      rw [seller0_rev_of_gt h hp' hq hc hrM]
      refine le_trans ?_ (le_max_left _ _)
      have h1 : min p' β ≤ β := min_le_right _ _
      have h2 : min p' (max 0 (1 - q)) ≤ max 0 (1 - q) := min_le_right _ _
      linarith [mul_le_mul_of_nonneg_left h2 hν.le]
    · -- First choice: bounded by the value at `p' = α·q`.
      refine le_trans (seller0_rev_le h hp' hq hrM) (le_trans ?_ (le_max_right _ _))
      have h1 : min p' β ≤ min β (α * q) := by
        rw [min_comm β (α * q)]; exact min_le_min hc (le_refl β)
      have h2 : min p' 1 ≤ min 1 (α * q) := by
        rw [min_comm 1 (α * q)]; exact min_le_min hc (le_refl 1)
      linarith [mul_le_mul_of_nonneg_left h2 hν.le]
  have hbdd : BddAbove S := ⟨r1star α β ν q, hub⟩
  refine le_antisymm (csSup_le hSne hub) ?_
  -- Pricing far above `α·q` earns `β + ν·max(0, 1-q)`, and that is attained.
  have hA : β + ν * max 0 (1 - q) ≤ sSup S := by
    have hP : (0:ℝ) ≤ α * q + β + 1 := by linarith
    obtain ⟨r, hr⟩ := V_nonempty h hP hq
    have hgt : α * q < α * q + β + 1 := by linarith
    have hval := seller0_rev_of_gt h hP hq hgt ((mem_V_iff_mem_muOptV h hP hq).1 hr)
    rw [min_eq_right (by linarith), min_eq_right (by linarith)] at hval
    refine le_csSup hbdd ?_
    rw [← hval]
    exact (mem_deviation_zero h).2 ⟨α * q + β + 1, hP, r, hr, rfl⟩
  rcases eq_or_lt_of_le haq with hq0 | hqpos
  · -- `α·q = 0`: undercutting yields nothing, so the high-price branch is everything.
    have he : r1star α β ν q = β + ν * max 0 (1 - q) := by
      simp only [DataMktOligo.MuOpt.r1star, ← hq0]
      rw [min_eq_right hβ.le, min_eq_right zero_le_one]
      have : (0:ℝ) ≤ ν * max 0 (1 - q) := by positivity
      rw [max_eq_left (by linarith)]
    rw [he]; exact hA
  · rw [DataMktOligo.MuOpt.r1star]
    refine max_le hA ?_
    -- Undercutting `α·q` approaches the first-choice value without attaining it.
    rw [Real.le_sSup_iff hbdd hSne]
    intro ε hε
    have hden : (0:ℝ) < 1 + ν := by linarith
    have hstep : ε / (2 * (1 + ν)) < 0 :=
      div_neg_of_neg_of_pos hε (by linarith)
    set p' : ℝ := max 0 (α * q + ε / (2 * (1 + ν))) with hp'def
    have hp'0 : 0 ≤ p' := le_max_left _ _
    have hp'lt : p' < α * q := by
      refine max_lt hqpos ?_
      linarith
    have hval : ∃ y ∈ S, y = min p' β + ν * min p' 1 := by
      obtain ⟨r, hr⟩ := V_nonempty h hp'0 hq
      refine ⟨r 0, (mem_deviation_zero h).2 ⟨p', hp'0, r, hr, rfl⟩, ?_⟩
      exact seller0_rev_of_lt h hp'0 hq hp'lt ((mem_V_iff_mem_muOptV h hp'0 hq).1 hr)
    obtain ⟨y, hyS, hyeq⟩ := hval
    refine ⟨y, hyS, ?_⟩
    -- `min` is 1-Lipschitz, so the shortfall is at most `(1+ν)·(α·q - p')`.
    have hgap : α * q - p' ≤ -(ε / (2 * (1 + ν))) := by
      have : α * q + ε / (2 * (1 + ν)) ≤ p' := le_max_right _ _
      linarith
    have hb1 : min (α * q) β ≤ min p' β + (α * q - p') := min_le_min_add hp'lt.le
    have hb2 : min (α * q) 1 ≤ min p' 1 + (α * q - p') := min_le_min_add hp'lt.le
    have hb3 : ν * min (α * q) 1 ≤ ν * min p' 1 + ν * (α * q - p') := by
      have := mul_le_mul_of_nonneg_left hb2 hν.le
      linarith
    have hcalc : (1 + ν) * (α * q - p') ≤ -(ε / 2) := by
      have hmul := mul_le_mul_of_nonneg_left hgap hden.le
      have heq : (1 + ν) * -(ε / (2 * (1 + ν))) = -(ε / 2) := by field_simp
      rw [heq] at hmul
      exact hmul
    rw [hyeq, min_comm β (α * q), min_comm 1 (α * q)]
    linarith

/-- **The closed form for `r₂*` is correct**: seller `1`'s best-response revenue,
given that seller `0` charges `p`, is `MuOpt.r2star`. -/
public theorem bestResponseRevenue_seller1 (h : Constraints α β ν) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    LinDataMkt.bestResponseRevenue (inst h) ![p, q] 1 = r2star α ν p := by
  have hν : 0 < ν := by linarith [h.c1_mid, h.c1_hi]
  have hα : 0 < α := by linarith [h.c1_lo]
  simp only [LinDataMkt.bestResponseRevenue]
  set S := LinDataMkt.deviationRevenues (inst h) ![p, q] 1 with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨r, hr⟩ := V_nonempty h hp hq
    exact ⟨r 1, (mem_deviation_one h).2 ⟨q, hq, r, hr, rfl⟩⟩
  -- Every deviation earns at most `r₂*(p)`.
  have hub : ∀ y ∈ S, y ≤ r2star α ν p := by
    rintro y hy
    obtain ⟨q', hq', r, hr, rfl⟩ := (mem_deviation_one h).1 hy
    obtain ⟨hle1, hle2⟩ := seller1_rev_le h hp hq' ((mem_V_iff_mem_muOptV h hp hq').1 hr)
    simp only [DataMktOligo.MuOpt.r2star]
    rcases lt_or_ge p (α * q') with hc | hc
    · refine le_trans (hle2 hc) (mul_le_mul_of_nonneg_left ?_ hν.le)
      refine max_le (le_trans ?_ (le_max_right _ _)) (le_max_left _ _)
      exact le_min zero_le_one (by positivity)
    · refine le_trans hle1 (mul_le_mul_of_nonneg_left ?_ hν.le)
      refine le_trans ?_ (le_max_right _ _)
      rw [min_comm]
      exact min_le_min (le_refl 1) (by rw [le_div_iff₀ hα]; linarith)
  have hbdd : BddAbove S := ⟨r2star α ν p, hub⟩
  refine le_antisymm (csSup_le hSne hub) ?_
  -- Pricing above `p/α` earns `ν·max(0, 1-p)`, and that value is attained.
  have hA : ν * max 0 (1 - p) ≤ sSup S := by
    have hq'0 : (0:ℝ) ≤ p / α + 1 := by positivity
    obtain ⟨r, hr⟩ := V_nonempty h hp hq'0
    have hlt : p < α * (p / α + 1) := by
      rw [mul_add, mul_div_cancel₀ _ hα.ne', mul_one]; linarith
    have hpa : (0:ℝ) ≤ p / α := by positivity
    have hbig : max 0 (1 - p) ≤ p / α + 1 := max_le (by linarith) (by linarith)
    have hval := seller1_rev_of_lt h hp hq'0 hlt hbig ((mem_V_iff_mem_muOptV h hp hq'0).1 hr)
    refine le_csSup hbdd ?_
    rw [← hval]
    exact (mem_deviation_one h).2 ⟨p / α + 1, hq'0, r, hr, rfl⟩
  rcases eq_or_lt_of_le hp with hp0 | hppos
  · -- `p = 0`: the high-price branch already realizes `r₂*`.
    have he : r2star α ν p = ν * max 0 (1 - p) := by
      simp only [DataMktOligo.MuOpt.r2star, ← hp0]
      norm_num
    rw [he]; exact hA
  · rw [DataMktOligo.MuOpt.r2star, mul_max_of_nonneg _ _ hν.le]
    refine max_le (le_trans (mul_le_mul_of_nonneg_left (le_max_right 0 (1 - p)) hν.le) hA) ?_
    -- Undercutting `p/α` approaches `ν·min(1, p/α)` without attaining it.
    rw [Real.le_sSup_iff hbdd hSne]
    intro ε hε
    have h2ν : (0:ℝ) < 2 * ν := by linarith
    have hhalf : ε / (2 * ν) < 0 := div_neg_of_neg_of_pos hε h2ν
    set d : ℝ := min 1 (p / α) + ε / (2 * ν) with hd
    have hdlt : d < min 1 (p / α) := by rw [hd]; linarith
    have hexp : ν * d = ν * min 1 (p / α) + ε / 2 := by
      rw [hd]; field_simp
    rcases le_or_gt d 0 with hdle | hdpos
    · -- Even a price of `0` already beats the target, which is negative here.
      refine ⟨0, ?_, ?_⟩
      · obtain ⟨r, hr⟩ := V_nonempty h hp (le_refl (0:ℝ))
        have hval := seller1_rev_of_gt h hp (le_refl (0:ℝ)) (by simpa using hppos)
          ((mem_V_iff_mem_muOptV h hp (le_refl (0:ℝ))).1 hr)
        have h0 : r 1 = 0 := by rw [hval, min_eq_left zero_le_one, mul_zero]
        rw [← h0]
        exact (mem_deviation_one h).2 ⟨0, le_refl 0, r, hr, rfl⟩
      · have hnp : ν * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hν.le hdle
        rw [hexp] at hnp
        linarith
    · refine ⟨ν * d, ?_, ?_⟩
      · obtain ⟨r, hr⟩ := V_nonempty h hp hdpos.le
        have hgt : α * d < p := by
          have hdp : d < p / α := lt_of_lt_of_le hdlt (min_le_right _ _)
          rw [mul_comm]; exact (lt_div_iff₀ hα).mp hdp
        have hval := seller1_rev_of_gt h hp hdpos.le hgt
          ((mem_V_iff_mem_muOptV h hp hdpos.le).1 hr)
        have hd1 : min d 1 = d :=
          min_eq_left (le_of_lt (lt_of_lt_of_le hdlt (min_le_left _ _)))
        rw [hd1] at hval
        rw [← hval]
        exact (mem_deviation_one h).2 ⟨d, hdpos.le, r, hr, rfl⟩
      · rw [hexp]; linarith

/-! ### `μ` bounds approximate equilibria -/

/- Both best-response revenues are strictly positive, so a seller earning `0`
can always do better. -/

private theorem r1star_pos (h : Constraints α β ν) (q : ℝ) : 0 < r1star α β ν q := by
  have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
  have hν : 0 ≤ ν := nu_nonneg h
  have h1 : 0 ≤ ν * max 0 (1 - q) := mul_nonneg hν (le_max_left _ _)
  have h2 : β + ν * max 0 (1 - q) ≤ r1star α β ν q := by
    simp only [DataMktOligo.MuOpt.r1star]; exact le_max_left _ _
  linarith

private theorem r2star_pos (h : Constraints α β ν) {p : ℝ} (_hp : 0 ≤ p) : 0 < r2star α ν p := by
  have hα : 0 < α := by linarith [h.c1_lo]
  have hν : 0 < ν := by linarith [h.c1_mid, h.c1_hi]
  simp only [DataMktOligo.MuOpt.r2star]
  refine mul_pos hν ?_
  rcases lt_or_ge p 1 with h1 | h1
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · refine lt_of_lt_of_le ?_ (le_max_right _ _)
    exact lt_min zero_lt_one (by positivity)

private theorem cap_pos (h : Constraints α β ν) : 0 < cap α β ν := by
  have hν : 0 < ν := by linarith [h.c1_mid, h.c1_hi]
  simp only [DataMktOligo.MuOpt.cap]
  nlinarith [h.c1_lo, h.c1_mid]

/-- Every element of `MuOpt.V` is a nonnegative revenue pair, transported from
`LinDataMkt.nonneg_of_mem_V` through the bridge. -/
private theorem nonneg_of_mem_muOptV (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {r1 r2 : ℝ} (hr : (r1, r2) ∈ DataMktOligo.MuOpt.V α β ν p q) : 0 ≤ r1 ∧ 0 ≤ r2 := by
  have hmem : ![r1, r2] ∈ LinDataMkt.V (inst h) ![p, q] := by
    refine (mem_V_iff_mem_muOptV h hp hq).2 ?_
    simpa using hr
  exact ⟨LinDataMkt.nonneg_of_mem_V (inst h) ![p, q] (isNonnegVector_prices hp hq) hmem 0,
    LinDataMkt.nonneg_of_mem_V (inst h) ![p, q] (isNonnegVector_prices hp hq) hmem 1⟩

/-- **The bridge to the optimization problem.** If the instability ratio at `(p,q)` exceeds `c`,
then `(p,q)` is not a `c`-approximate Nash equilibrium.

Only this direction is needed, and only this direction is sound under the `cap` convention. -/
public theorem not_isApproxNE_of_lt_μ (h : Constraints α β ν) {p q c : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (_hcap : c < cap α β ν) (hc : c < μ α β ν p q) :
    ¬ LinDataMkt.IsApproxNE (inst h) ![p, q] c := by
  intro hNE
  obtain ⟨r, hr⟩ := V_nonempty h hp hq
  have hrM : (r 0, r 1) ∈ DataMktOligo.MuOpt.V α β ν p q := (mem_V_iff_mem_muOptV h hp hq).1 hr
  -- `μ` is an infimum over a set that contains the ratio pair at `r`.
  have hbdd : BddBelow {m : ℝ | ∃ r1 r2, (r1, r2) ∈ DataMktOligo.MuOpt.V α β ν p q ∧
      m = max (ratio (cap α β ν) (r1star α β ν q) r1)
              (ratio (cap α β ν) (r2star α ν p) r2)} := by
    refine ⟨0, ?_⟩
    rintro m ⟨r1, r2, hmem, rfl⟩
    obtain ⟨h1, h2⟩ := nonneg_of_mem_muOptV h hp hq hmem
    refine le_max_of_le_left ?_
    simp only [DataMktOligo.MuOpt.ratio]
    split_ifs with hz
    · exact (cap_pos h).le
    · exact div_nonneg (r1star_pos h q).le h1
  have hμle : μ α β ν p q ≤
      max (ratio (cap α β ν) (r1star α β ν q) (r 0))
          (ratio (cap α β ν) (r2star α ν p) (r 1)) := by
    unfold μ
    exact csInf_le hbdd ⟨r 0, r 1, hrM, rfl⟩
  have hcm : c < max (ratio (cap α β ν) (r1star α β ν q) (r 0))
      (ratio (cap α β ν) (r2star α ν p) (r 1)) := lt_of_lt_of_le hc hμle
  -- The equilibrium condition caps each seller's best response by `c` times her revenue.
  have hb0 := hNE.2 r hr 0
  have hb1 := hNE.2 r hr 1
  rw [bestResponseRevenue_seller0 h hp hq] at hb0
  rw [bestResponseRevenue_seller1 h hp hq] at hb1
  have hr0 := LinDataMkt.nonneg_of_mem_V (inst h) ![p, q] (isNonnegVector_prices hp hq) hr 0
  have hr1 := LinDataMkt.nonneg_of_mem_V (inst h) ![p, q] (isNonnegVector_prices hp hq) hr 1
  rcases lt_max_iff.1 hcm with hcase | hcase
  · -- Seller `0` could do better than `c` times what she earns.
    simp only [DataMktOligo.MuOpt.ratio] at hcase
    split_ifs at hcase with hz
    · rw [hz, mul_zero] at hb0
      exact absurd hb0 (not_le.mpr (r1star_pos h q))
    · have hpos : 0 < r 0 := lt_of_le_of_ne hr0 (Ne.symm hz)
      rw [lt_div_iff₀ hpos] at hcase
      nlinarith
  · -- Seller `1` could do better.
    simp only [DataMktOligo.MuOpt.ratio] at hcase
    split_ifs at hcase with hz
    · rw [hz, mul_zero] at hb1
      exact absurd hb1 (not_le.mpr (r2star_pos h hp))
    · have hpos : 0 < r 1 := lt_of_le_of_ne hr1 (Ne.symm hz)
      rw [lt_div_iff₀ hpos] at hcase
      nlinarith

end DataMktOligo.NashInapprox
