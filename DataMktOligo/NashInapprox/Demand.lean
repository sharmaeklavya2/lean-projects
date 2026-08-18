module

public import DataMktOligo.NashInapprox.Instance
public import DataMktOligo.LinDataMkt.Greedy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# What each buyer spends

For revenue we never need a buyer's demand itself, only how much she *spends* with each
seller. This file pins down that spending, which is what `thm:lne-cex:r` asserts.

The rich buyer is immediate: dataset `1` is worthless to her, so she spends `min p β` with
seller `0` and nothing with seller `1`.

The poor buyer always satisfies the two-sided bounds of `thm:lne-cex:r`, and her spending is
pinned exactly except on the knife-edge `p = α·q` with `p + q > 1`, where it depends on how
she breaks the tie.

## Main results

* `rich_spend`: the rich buyer's spending.
* `poor_spend0_le`, `poor_spend1_le`, `poor_spend0_ge`, `poor_spend1_ge`: the general
  two-sided bounds.
* `poor_spend_of_lt`, `poor_spend_of_gt`: exact spending off the knife-edge.
* `poor_spend_sum`: when `p + q ≥ 1` the poor buyer exhausts her budget.
-/

@[expose] public section

namespace DataMktOligo.NashInapprox

open DataMktOligo.LinDataMkt
open DataMktOligo.MuOpt (Constraints)

variable {α β ν : ℝ}

/-- Cost at a two-seller price vector, written out. -/
theorem cost_two (p q : ℝ) (z : Fin 2 → ℝ) : cost ![p, q] z = p * z 0 + q * z 1 := by
  simp [cost, Fin.sum_univ_succ]

/-! ### The rich buyer -/

/-- The rich buyer values only dataset `0`, so she spends `min p β` with seller `0` and
nothing with seller `1`. -/
theorem rich_spend (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {z : Fin 2 → ℝ} (hz : IsDemand (inst h) ![p, q] 1 z) :
    p * z 0 = min p β ∧ z 1 = 0 := by
  obtain ⟨haff, _, hsat⟩ :=
    (isDemand_iff (inst h) ![p, q] 1 (isNonnegVector_prices hp hq) (inst_b_pos h 1) z).1 hz
  have hz1 : z 1 = 0 := by
    by_contra hne
    have hpos : 0 < z 1 := lt_of_le_of_ne (mem_unitCube_iff.1 haff.1 1).1 (Ne.symm hne)
    have := haff.2.2 1 hpos
    simp at this
  have hz0le : z 0 ≤ 1 := (mem_unitCube_iff.1 haff.1 0).2
  have hz0ge : 0 ≤ z 0 := (mem_unitCube_iff.1 haff.1 0).1
  have hcost : p * z 0 = cost ![p, q] z := by rw [cost_two, hz1]; ring
  have hb : cost ![p, q] z ≤ β := by simpa using haff.2.1
  refine ⟨le_antisymm ?_ ?_, hz1⟩
  · refine le_min ?_ (by linarith [hcost, hb])
    nlinarith
  · rcases hsat with hc | hall
    · have : p * z 0 = β := by rw [hcost, hc]; simp
      rw [this]; exact min_le_right _ _
    · have h1 : z 0 = 1 := by
        have hβ : 0 < β := by linarith [h.c1_lo, h.c1_mid]
        simpa using hall 0 (by simpa using hβ)
      rw [h1, mul_one]; exact min_le_left _ _

/-! ### The poor buyer -/

/-- The three conditions of `isDemand_iff`, written out for the poor buyer. Both of her
values are positive, so the support condition is vacuous and `Saturated`'s second disjunct
says she owns both datasets outright. -/
private theorem poor_facts (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {z : Fin 2 → ℝ} (hz : IsDemand (inst h) ![p, q] 0 z) :
    (0 ≤ z 0 ∧ z 0 ≤ 1) ∧ (0 ≤ z 1 ∧ z 1 ≤ 1) ∧ p * z 0 + q * z 1 ≤ 1
      ∧ (0 < z 1 → z 0 < 1 → α * q ≤ p)
      ∧ (0 < z 0 → z 1 < 1 → p ≤ α * q)
      ∧ (p * z 0 + q * z 1 = 1 ∨ (z 0 = 1 ∧ z 1 = 1)) := by
  obtain ⟨haff, hswap, hsat⟩ :=
    (isDemand_iff (inst h) ![p, q] 0 (isNonnegVector_prices hp hq) (inst_b_pos h 0) z).1 hz
  have hα : 0 < α := by linarith [h.c1_lo]
  refine ⟨⟨(mem_unitCube_iff.1 haff.1 0).1, (mem_unitCube_iff.1 haff.1 0).2⟩,
    ⟨(mem_unitCube_iff.1 haff.1 1).1, (mem_unitCube_iff.1 haff.1 1).2⟩, ?_, ?_, ?_, ?_⟩
  · have := haff.2.1; rw [cost_two] at this; simpa using this
  · intro h1 h0
    have := hswap 0 1 h1 h0
    simpa [bpbLE] using this
  · intro h0 h1
    have := hswap 1 0 h0 h1
    simpa [bpbLE] using this
  · rcases hsat with hc | hall
    · left; rw [cost_two] at hc; simpa using hc
    · right
      exact ⟨by simpa using hall 0 (by simpa using hα),
        by simpa using hall 1 (by norm_num)⟩

theorem poor_spend0_le (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {z : Fin 2 → ℝ} (hz : IsDemand (inst h) ![p, q] 0 z) : p * z 0 ≤ min p 1 := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, _⟩, hcost, _, _, _⟩ := poor_facts h hp hq hz
  exact le_min (by nlinarith) (by nlinarith)

theorem poor_spend1_le (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {z : Fin 2 → ℝ} (hz : IsDemand (inst h) ![p, q] 0 z) : q * z 1 ≤ min q 1 := by
  obtain ⟨⟨h00, _⟩, ⟨h10, h11⟩, hcost, _, _, _⟩ := poor_facts h hp hq hz
  exact le_min (by nlinarith) (by nlinarith)

theorem poor_spend0_ge (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {z : Fin 2 → ℝ} (hz : IsDemand (inst h) ![p, q] 0 z) :
    min p (max 0 (1 - q)) ≤ p * z 0 := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, hcost, _, _, hsat⟩ := poor_facts h hp hq hz
  rcases eq_or_lt_of_le h01 with h1 | h1
  · rw [h1, mul_one]; exact min_le_left _ _
  · -- Not fully bought, so the budget is exhausted and `p·z₀ ≥ 1 - q`.
    have hc : p * z 0 + q * z 1 = 1 := by
      rcases hsat with hc | ⟨he, _⟩
      · exact hc
      · exact absurd he (ne_of_lt h1)
    refine le_trans (min_le_right _ _) ?_
    refine max_le (by nlinarith) (by nlinarith)

theorem poor_spend1_ge (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {z : Fin 2 → ℝ} (hz : IsDemand (inst h) ![p, q] 0 z) :
    min q (max 0 (1 - p)) ≤ q * z 1 := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, hcost, _, _, hsat⟩ := poor_facts h hp hq hz
  rcases eq_or_lt_of_le h11 with h1 | h1
  · rw [h1, mul_one]; exact min_le_left _ _
  · have hc : p * z 0 + q * z 1 = 1 := by
      rcases hsat with hc | ⟨_, he⟩
      · exact hc
      · exact absurd he (ne_of_lt h1)
    refine le_trans (min_le_right _ _) ?_
    refine max_le (by nlinarith) (by nlinarith)

/-- When `p + q ≥ 1`, the poor buyer exhausts her budget. -/
theorem poor_spend_sum (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {z : Fin 2 → ℝ} (hz : IsDemand (inst h) ![p, q] 0 z) (hpq : 1 ≤ p + q) :
    p * z 0 + q * z 1 = 1 := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, hcost, _, _, hsat⟩ := poor_facts h hp hq hz
  rcases hsat with hc | ⟨e0, e1⟩
  · exact hc
  · rw [e0, e1] at hcost ⊢; linarith

/-- When `p + q ≤ 1` the poor buyer can afford both datasets outright, so she buys both
whichever way she ranks them. -/
theorem poor_spend_of_add_le (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {z : Fin 2 → ℝ} (hz : IsDemand (inst h) ![p, q] 0 z) (hpq : p + q ≤ 1) :
    p * z 0 = p ∧ q * z 1 = q := by
  have h0 := poor_spend0_ge h hp hq hz
  have h1 := poor_spend0_le h hp hq hz
  have h2 := poor_spend1_ge h hp hq hz
  have h3 := poor_spend1_le h hp hq hz
  rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - q), min_eq_left (by linarith : p ≤ 1 - q)] at h0
  rw [min_eq_left (by linarith : p ≤ 1)] at h1
  rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - p), min_eq_left (by linarith : q ≤ 1 - p)] at h2
  rw [min_eq_left (by linarith : q ≤ 1)] at h3
  exact ⟨le_antisymm h1 h0, le_antisymm h3 h2⟩

/-- Off the knife-edge, with dataset `0` strictly better: the poor buyer fills up on
dataset `0` first. -/
theorem poor_spend_of_lt (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {z : Fin 2 → ℝ} (hz : IsDemand (inst h) ![p, q] 0 z) (hlt : p < α * q) :
    p * z 0 = min p 1 ∧ q * z 1 = min q (max 0 (1 - p)) := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, hcost, hsw01, _, hsat⟩ := poor_facts h hp hq hz
  -- Holding any of dataset `1` forces dataset `0` to be full.
  have hfull : 0 < z 1 → z 0 = 1 := by
    intro hz1
    by_contra hne
    exact absurd (hsw01 hz1 (lt_of_le_of_ne h01 hne)) (not_le.mpr hlt)
  constructor
  · refine le_antisymm (poor_spend0_le h hp hq hz) ?_
    rcases eq_or_lt_of_le h01 with h1 | h1
    · rw [h1, mul_one]; exact min_le_left _ _
    · have hz1 : z 1 = 0 := by
        by_contra hne
        exact absurd (hfull (lt_of_le_of_ne h10 (Ne.symm hne))) (ne_of_lt h1)
      have hc : p * z 0 = 1 := by
        rcases hsat with hc | ⟨he, _⟩
        · rw [hz1, mul_zero, add_zero] at hc; exact hc
        · exact absurd he (ne_of_lt h1)
      rw [hc]; exact min_le_right _ _
  · refine le_antisymm ?_ (poor_spend1_ge h hp hq hz)
    refine le_min (by nlinarith) ?_
    rcases eq_or_lt_of_le h10 with h1 | h1
    · rw [← h1, mul_zero]; exact le_max_left _ _
    · have := hfull h1
      refine le_trans ?_ (le_max_right _ _)
      rw [this, mul_one] at hcost; linarith

/-- Off the knife-edge, with dataset `1` strictly better: the poor buyer fills up on
dataset `1` first. -/
theorem poor_spend_of_gt (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    {z : Fin 2 → ℝ} (hz : IsDemand (inst h) ![p, q] 0 z) (hgt : α * q < p) :
    q * z 1 = min q 1 ∧ p * z 0 = min p (max 0 (1 - q)) := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, hcost, _, hsw10, hsat⟩ := poor_facts h hp hq hz
  have hfull : 0 < z 0 → z 1 = 1 := by
    intro hz0
    by_contra hne
    exact absurd (hsw10 hz0 (lt_of_le_of_ne h11 hne)) (not_le.mpr hgt)
  constructor
  · refine le_antisymm (poor_spend1_le h hp hq hz) ?_
    rcases eq_or_lt_of_le h11 with h1 | h1
    · rw [h1, mul_one]; exact min_le_left _ _
    · have hz0 : z 0 = 0 := by
        by_contra hne
        exact absurd (hfull (lt_of_le_of_ne h00 (Ne.symm hne))) (ne_of_lt h1)
      have hc : q * z 1 = 1 := by
        rcases hsat with hc | ⟨_, he⟩
        · rw [hz0, mul_zero, zero_add] at hc; exact hc
        · exact absurd he (ne_of_lt h1)
      rw [hc]; exact min_le_right _ _
  · refine le_antisymm ?_ (poor_spend0_ge h hp hq hz)
    refine le_min (by nlinarith) ?_
    rcases eq_or_lt_of_le h00 with h1 | h1
    · rw [← h1, mul_zero]; exact le_max_left _ _
    · have := hfull h1
      refine le_trans ?_ (le_max_right _ _)
      rw [this, mul_one] at hcost; linarith

/-- On the knife-edge `p = α·q`, both datasets give the poor buyer the same bang-per-buck,
so *every* budget-exhausting bundle is a demand. This is what makes the sellers' revenues
genuinely ambiguous there (`remark:lne-cex:pq-ambig`). -/
theorem poor_isDemand_of_tie (h : Constraints α β ν) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (htie : p = α * q) {z : Fin 2 → ℝ}
    (h0 : 0 ≤ z 0) (h0' : z 0 ≤ 1) (h1 : 0 ≤ z 1) (h1' : z 1 ≤ 1)
    (hc : p * z 0 + q * z 1 = 1) : IsDemand (inst h) ![p, q] 0 z := by
  have hα : 0 < α := by linarith [h.c1_lo]
  refine (isDemand_iff (inst h) ![p, q] 0 (isNonnegVector_prices hp hq)
    (inst_b_pos h 0) z).2 ⟨⟨mem_unitCube_iff.2 ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j; fin_cases j
    · exact ⟨h0, h0'⟩
    · exact ⟨h1, h1'⟩
  · rw [cost_two]; simpa using le_of_eq hc
  · intro j hj; fin_cases j
    · simpa using hα
    · norm_num
  · intro j k _ _
    fin_cases j <;> fin_cases k <;> simp [bpbLE, htie]
  · left; rw [cost_two]; simpa using hc

end DataMktOligo.NashInapprox
