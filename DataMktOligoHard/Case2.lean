module

public import DataMktOligoHard.Defs
import DataMktOligoHard.SpecialPoints

/-!
# Case 2 of the main reduction (case2.tex)

This file corresponds to the "Case 2: `p < α·q` and `p + q ≥ 1`" subsection.
In this region `V(p,q)` is the singleton `{(r₁⁺, r₂⁻)}`, so
`μ(p,q) = max(r₁*(q)/r₁⁺, r₂*(p)/r₂⁻)`.

The paper's proof (thm:2) is a dichotomy at `p₁`:
* `p ≥ p₁`: seller 2's ratio `p/(α(1-p))` is increasing, so it is `≥ μ₁` (its value at `p₁`).
* `p ≤ p₁`: seller 1's ratio `r₁*(q)/(n·p)` is `≥ μ₁`, using the global bound
  `r₁*(q) ≥ r₁*(q₁) = (n+1)·ĉ₁` (thm:q1) and `p ≤ p₁`.

The `p = 0` and `p ≥ 1` corners (where a seller earns `0`) give `μ = cap` under Lean's
`x/0` convention, but `μ₁ ≤ cap` (`μ1_le_cap`) so the sharp bound `μ₁ ≤ μ` holds there too.
-/

namespace DataMktOligoHard

variable {α β n : ℝ}

/-! ## `μ` as a max in the case-2 region -/

/-- In the case-2 region (`p < α·q` and `p + q ≥ 1`, with `0 ≤ p`), `V` is the
singleton `{(r₁⁺, r₂⁻)}`, so `μ(p,q) = max(r₁*(q)/r₁⁺, r₂*(p)/r₂⁻)`.
At the boundary `p + q = 1`, `V` takes its `{(r₁⁻, r₂⁻)}` branch instead, but there
`r₁⁻ = r₁⁺` (since `1 - q = p ≤ 1`), so the singleton is the same. -/
theorem μ_eq_max_case2 (h : Constraints α β n) {p q : ℝ}
    (hp : 0 ≤ p) (hpq1 : 1 ≤ p + q) (hpaq : p < α * q) :
    μ α β n p q = max (ratio (cap α β n) (r1star α β n q) (r1hi β n p q))
                      (ratio (cap α β n) (r2star α n p) (r2lo n p q)) := by
  have hV : V α β n p q = {(r1hi β n p q, r2lo n p q)} := by
    rcases lt_or_eq_of_le hpq1 with hlt | heq
    · unfold V
      rw [if_neg (not_le.mpr hlt), if_pos hpaq]
    · -- boundary `p + q = 1`: the `{(r₁⁻, r₂⁻)}` branch, but `r₁⁻ = r₁⁺` here.
      have hp1 : 1 - q = p := by linarith
      have hplt1 : p < 1 := by
        rcases lt_or_ge p 1 with h1 | h1
        · exact h1
        · exfalso
          have hq' : q = 1 - p := by linarith
          rw [hq'] at hpaq
          nlinarith [alpha_pos h, hp, h1]
      have hr1 : r1lo β n p q = r1hi β n p q := by
        simp only [r1lo, r1hi, hp1]
        rw [max_eq_right hp, min_self, min_eq_left hplt1.le]
      unfold V
      rw [if_pos (le_of_eq heq.symm), hr1]
  have hset : {m : ℝ | ∃ r1 r2, (r1, r2) ∈ V α β n p q ∧
                m = max (ratio (cap α β n) (r1star α β n q) r1)
                        (ratio (cap α β n) (r2star α n p) r2)}
            = {max (ratio (cap α β n) (r1star α β n q) (r1hi β n p q))
                   (ratio (cap α β n) (r2star α n p) (r2lo n p q))} := by
    rw [hV]; ext m
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨r1, r2, ⟨rfl, rfl⟩, rfl⟩; rfl
    · rintro rfl; exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩
  unfold μ; rw [hset, csInf_singleton]

/-! ### thm:2 -/

/-- **thm:2**: if `p < α·q` and `p + q ≥ 1` (with `0 ≤ p`, `0 ≤ q`), then
`μ(p,q) ≥ μ₁`. At the `0`-revenue corners `p = 0` and `p ≥ 1` Lean's `x/0` convention
gives `μ = cap`, and `μ₁ ≤ cap` (`μ1_le_cap`) closes those.

For `p ≥ p₁` seller 2's ratio `p/(α(1-p))` (increasing on `(0,1)`) already clears `μ₁`;
for `p ≤ p₁` seller 1's ratio `r₁*(q)/(p(n+1)) ≥ (n+1)ĉ₁/(p(n+1)) = ĉ₁/p ≥ ĉ₁/p₁ = μ₁`. -/
public theorem thm_2 (h : Constraints α β n) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpaq : p < α * q) (hpq1 : 1 ≤ p + q) :
    μ1 α β n ≤ μ α β n p q := by
  have hn := n_pos h
  have hα := alpha_pos h
  rw [μ_eq_max_case2 h hp hpq1 hpaq]
  rcases le_or_gt 1 p with hp1le | hplt1
  · -- `p ≥ 1`: seller 2 earns `0`, so `ratio₂ = cap ≥ min cap μ₁`.
    have hr2lo0 : r2lo n p q = 0 := by
      simp only [r2lo]
      rw [max_eq_left (by linarith : (1:ℝ) - p ≤ 0), min_eq_right hq, mul_zero]
    have hratio2cap : ratio (cap α β n) (r2star α n p) (r2lo n p q) = cap α β n := by
      rw [ratio, if_pos hr2lo0]
    rw [hratio2cap]
    exact le_trans (μ1_le_cap h) (le_max_right _ _)
  · -- `p < 1`.
    rcases eq_or_lt_of_le hp with hp0 | hppos
    · -- `p = 0`: seller 1 earns `0`, so `ratio₁ = cap ≥ min cap μ₁`.
      have hr1hi0 : r1hi β n p q = 0 := by
        simp only [r1hi, ← hp0]
        rw [min_eq_left (by linarith [h.c1_lo, h.c1_mid] : (0:ℝ) ≤ β),
            min_eq_left (by norm_num : (0:ℝ) ≤ 1)]
        ring
      have hratio1cap : ratio (cap α β n) (r1star α β n q) (r1hi β n p q) = cap α β n := by
        rw [ratio, if_pos hr1hi0]
      rw [hratio1cap]
      exact le_trans (μ1_le_cap h) (le_max_left _ _)
    · -- `0 < p < 1`: the two genuine sub-cases.
      have hr1hi : r1hi β n p q = p * (n + 1) := by
        simp only [r1hi]
        rw [min_eq_left (by linarith [h.c1_lo, h.c1_mid] : p ≤ β),
            min_eq_left hplt1.le]
        ring
      have hr2lo : r2lo n p q = n * (1 - p) := by
        simp only [r2lo]
        rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - p),
            min_eq_right (by linarith : 1 - p ≤ q)]
      rcases le_total p (p1 α β n) with hpp1 | hp1p
      · -- `p ≤ p₁`: seller 1's ratio clears `μ₁`.
        refine le_trans ?_ (le_max_left _ _)
        have hden_pos : 0 < r1hi β n p q := by
          rw [hr1hi]; exact mul_pos hppos (by linarith)
        -- `(n+1)·ĉ₁ = n + α·q₁ ≤ r₁*(q)`.
        have hnc : (n + 1) * chat1 α β n = n + α * q1 α β n := by
          rw [← r1star_q1' h, r1star_q1 h]
        have hr1lb : (n + 1) * chat1 α β n ≤ r1star α β n q := by
          rw [hnc]; exact r1star_ge h q
        rw [ratio, if_neg (ne_of_gt hden_pos)]
        simp only [μ1]
        rw [div_le_div_iff₀ (p1_pos h) hden_pos, hr1hi]
        -- goal: `ĉ₁ * (p * (n+1)) ≤ r₁*(q) * p₁`
        nlinarith [hr1lb, hpp1, p1_pos h, chat1_gt_one h, hn,
          mul_nonneg (sub_nonneg.mpr hpp1)
            (mul_pos (by linarith [chat1_gt_one h] : (0:ℝ) < chat1 α β n)
              (by linarith : (0:ℝ) < n + 1)).le]
      · -- `p ≥ p₁`: seller 2's ratio clears `μ₁`.
        refine le_trans ?_ (le_max_right _ _)
        have hpgt : α / (α + 1) < p := lt_of_lt_of_le (p1_gt_ratio h) hp1p
        have hgt' : α < p * (α + 1) := by
          rwa [div_lt_iff₀ (by linarith : (0:ℝ) < α + 1)] at hpgt
        have hpα1 : p / α ≤ 1 := by rw [div_le_one hα]; linarith [h.c1_lo]
        have h1p : 1 - p ≤ p / α := by rw [le_div_iff₀ hα]; nlinarith [hgt']
        have hr2star : r2star α n p = n * (p / α) := by
          simp only [r2star]; rw [min_eq_right hpα1, max_eq_right h1p]
        have h1p_pos : 0 < 1 - p := by linarith
        have hden2 : r2lo n p q ≠ 0 := by
          rw [hr2lo]; exact ne_of_gt (mul_pos hn h1p_pos)
        rw [ratio, if_neg hden2, hr2star, hr2lo,
            mul_div_mul_left _ _ (ne_of_gt hn), div_div]
        simp only [μ1]
        rw [div_le_div_iff₀ (p1_pos h) (mul_pos hα h1p_pos)]
        -- goal: `ĉ₁ * (α * (1 - p)) ≤ p * p₁`; uses `p₁² = α·ĉ₁·(1-p₁)` and `p ≥ p₁`.
        nlinarith [p1_quadratic h, hp1p, p1_pos h, hα, chat1_gt_one h,
          mul_nonneg (sub_nonneg.mpr hp1p)
            (by nlinarith [p1_pos h, mul_pos hα (by linarith [chat1_gt_one h] :
              (0:ℝ) < chat1 α β n)] : (0:ℝ) ≤ p1 α β n + chat1 α β n * α)]

end DataMktOligoHard
