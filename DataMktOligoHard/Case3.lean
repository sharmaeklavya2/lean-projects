import DataMktOligoHard.SpecialPoints
import DataMktOligoHard.Case1
import DataMktOligoHard.Case2

/-!
# Case 3 of the main reduction (case3.tex)

This file corresponds to the "Case 3: `p + q ≤ 1`" subsection.
In this region `V(p,q)` is the singleton `{(r₁⁻, r₂⁻)}`, so
`μ(p,q) = max(r₁*(q)/r₁⁻, r₂*(p)/r₂⁻)`.

Writing `p' := α/(α+1)`, the paper first proves two monotonicity lemmas:
`μ(·,q)` is decreasing in `p` for `p ≤ min(p', 1-q)` (thm:mu-dec-p), and `μ(p,·)`
is decreasing in `q` for `q ≤ min(q₁, 1-p)` (thm:mu-dec-q). This file starts with
the first one.

## The `min cap` workaround

The paper's `μ(x₁,q) ≥ μ(x₂,q)` is *false* under Lean's `x/0 = cap` convention: at
the corners `x₁ = 0` or `q = 0` a seller earns `0`, so `μ(x₁,q) = cap`, while
`μ(x₂,q)` for small `x₂ > 0` can exceed `cap`. As in `thm_2`, we state the bound
side capped — `min cap (μ x₂ q) ≤ μ x₁ q` — which is honestly true (the corners
give `μ(x₁,q) ≥ cap ≥ min cap (μ x₂ q)`) and chains the same way downstream.
-/

namespace DataMktOligoHard

variable {α β n : ℝ}

/-! ## `μ` as a max in the case-3 region (`p + q ≤ 1`) -/

/-- In the case-3 region (`p + q ≤ 1`), `V` is the singleton `{(r₁⁻, r₂⁻)}`, so
`μ(p,q) = max(r₁*(q)/r₁⁻, r₂*(p)/r₂⁻)`. Constraint-free. -/
theorem μ_eq_max_case3_raw {p q : ℝ} (hpq : p + q ≤ 1) :
    μ α β n p q = max (ratio (cap α β n) (r1star α β n q) (r1lo β n p q))
                      (ratio (cap α β n) (r2star α n p) (r2lo n p q)) := by
  have hV : V α β n p q = {(r1lo β n p q, r2lo n p q)} := by
    unfold V; rw [if_pos hpq]
  have hset : {m : ℝ | ∃ r1 r2, (r1, r2) ∈ V α β n p q ∧
                m = max (ratio (cap α β n) (r1star α β n q) r1)
                        (ratio (cap α β n) (r2star α n p) r2)}
            = {max (ratio (cap α β n) (r1star α β n q) (r1lo β n p q))
                   (ratio (cap α β n) (r2star α n p) (r2lo n p q))} := by
    rw [hV]; ext m
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨r1, r2, ⟨rfl, rfl⟩, rfl⟩; rfl
    · rintro rfl; exact ⟨_, _, ⟨rfl, rfl⟩, rfl⟩
  unfold μ; rw [hset, csInf_singleton]

/-- Closed form of `μ` in the case-3 sub-region `0 < p`, `0 < q`, `p + q ≤ 1`,
`p ≤ p' = α/(α+1)`. Here `1 - p ≥ p/α`, so `r₁⁻ = p(n+1)`, `r₂⁻ = nq`, and
`r₂*(p) = n(1-p)`, giving `μ(p,q) = max(r₁*(q)/(p(n+1)), (1-p)/q)`. -/
theorem μ_eq_max_case3 (h : Constraints α β n) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 1) (hpp : p ≤ α / (α + 1)) :
    μ α β n p q = max (r1star α β n q / (p * (n + 1))) ((1 - p) / q) := by
  have hα := alpha_pos h
  have hn := n_pos h
  -- `p' = α/(α+1) < 1`, so `p < 1`.
  have hp1 : p < 1 :=
    lt_of_le_of_lt hpp (by rw [div_lt_one (by linarith : (0:ℝ) < α + 1)]; linarith)
  -- `p ≤ p'` unfolds to `p(α+1) ≤ α`, hence `p/α ≤ 1 - p`.
  have hpp' : p * (α + 1) ≤ α := (le_div_iff₀ (by linarith : (0:ℝ) < α + 1)).mp hpp
  have hpdiv : p / α ≤ 1 - p := by rw [div_le_iff₀ hα]; nlinarith [hpp']
  -- Components of `V` and `r₂*`.
  have hr1lo : r1lo β n p q = p * (n + 1) := by
    simp only [r1lo]
    rw [min_eq_left (by linarith [h.c1_lo, h.c1_mid] : p ≤ β),
        max_eq_right (by linarith : (0:ℝ) ≤ 1 - q),
        min_eq_left (by linarith : p ≤ 1 - q)]
    ring
  have hr2lo : r2lo n p q = n * q := by
    simp only [r2lo]
    rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - p),
        min_eq_left (by linarith : q ≤ 1 - p)]
  have hr2star : r2star α n p = n * (1 - p) := by
    simp only [r2star]
    rw [min_eq_right (by rw [div_le_one hα]; linarith [h.c1_lo] : p / α ≤ 1),
        max_eq_left hpdiv]
  -- Assemble.
  have hd1 : p * (n + 1) ≠ 0 := ne_of_gt (mul_pos hp (by linarith))
  have hd2 : n * q ≠ 0 := ne_of_gt (mul_pos hn hq)
  rw [μ_eq_max_case3_raw hpq, hr1lo, hr2lo, hr2star]
  simp only [ratio]
  rw [if_neg hd1, if_neg hd2, mul_div_mul_left _ _ (ne_of_gt hn)]

/-! ### thm:mu-dec-p -/

/-- **thm:mu-dec-p**: with `p' = α/(α+1)`, for `0 ≤ x₁ ≤ x₂ ≤ min(p', 1-q)` (which
forces `q ≤ 1`), `μ(·,q)` is decreasing: `min cap (μ x₂ q) ≤ μ x₁ q`.

The `min cap` is the `thm_2` workaround: the paper's `μ(x₁,q) ≥ μ(x₂,q)` fails at
the `0`-revenue corners `x₁ = 0` / `q = 0` (where `μ(x₁,q) = cap`), but there
`μ(x₁,q) ≥ cap ≥ min cap (μ x₂ q)`. Away from the corners
`μ(p,q) = max(r₁*(q)/(p(n+1)), (1-p)/q)`, a `max` of two functions decreasing in `p`. -/
theorem mu_dec_p (h : Constraints α β n) {q x1 x2 : ℝ}
    (hq0 : 0 ≤ q) (hx1 : 0 ≤ x1) (hx12 : x1 ≤ x2)
    (hx2 : x2 ≤ min (α / (α + 1)) (1 - q)) :
    min (cap α β n) (μ α β n x2 q) ≤ μ α β n x1 q := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hx2p' : x2 ≤ α / (α + 1) := le_trans hx2 (min_le_left _ _)
  have hx2q : x2 ≤ 1 - q := le_trans hx2 (min_le_right _ _)
  have hx1p' : x1 ≤ α / (α + 1) := le_trans hx12 hx2p'
  have hx1q : x1 ≤ 1 - q := le_trans hx12 hx2q
  rcases eq_or_lt_of_le hx1 with hx10 | hx1pos
  · -- `x₁ = 0`: seller 1 earns `0`, so `μ(0,q) ≥ cap ≥ min cap (μ x₂ q)`.
    subst hx10
    have hr1lo0 : r1lo β n 0 q = 0 := by
      simp only [r1lo]
      rw [min_eq_left (by linarith [h.c1_lo, h.c1_mid] : (0:ℝ) ≤ β),
          min_eq_left (le_max_left 0 (1 - q))]
      ring
    rw [μ_eq_max_case3_raw (show (0:ℝ) + q ≤ 1 by linarith), hr1lo0]
    rw [show ratio (cap α β n) (r1star α β n q) 0 = cap α β n from by rw [ratio, if_pos rfl]]
    exact le_trans (min_le_left _ _) (le_max_left _ _)
  · rcases eq_or_lt_of_le hq0 with hq00 | hqpos
    · -- `q = 0`: seller 2 earns `0`, so `μ(x₁,0) ≥ cap ≥ min cap (μ x₂ 0)`.
      subst hq00
      have hr2lo0 : r2lo n x1 0 = 0 := by
        simp only [r2lo]
        rw [min_eq_left (le_max_left 0 (1 - x1))]; ring
      rw [μ_eq_max_case3_raw (show x1 + (0:ℝ) ≤ 1 by linarith [hx1p',
            (by rw [div_lt_one (by linarith : (0:ℝ) < α + 1)]; linarith :
              α / (α + 1) < 1)]),
          hr2lo0]
      rw [show ratio (cap α β n) (r2star α n x1) 0 = cap α β n from by rw [ratio, if_pos rfl]]
      exact le_trans (min_le_left _ _) (le_max_right _ _)
    · -- `0 < x₁ ≤ x₂` and `0 < q`: genuine monotonicity, both ratios finite.
      have hx2pos : 0 < x2 := lt_of_lt_of_le hx1pos hx12
      have hr1s_pos : 0 < r1star α β n q := by
        have hlb : 0 < n + α * q1 α β n := by
          linarith [n_pos h, one_lt_alpha_mul_q1 h]
        linarith [r1star_ge h q]
      rw [μ_eq_max_case3 h hx1pos hqpos (by linarith : x1 + q ≤ 1) hx1p',
          μ_eq_max_case3 h hx2pos hqpos (by linarith : x2 + q ≤ 1) hx2p']
      -- seller-1 ratio: larger `x` ⇒ larger denominator ⇒ smaller ratio.
      have hA : r1star α β n q / (x2 * (n + 1)) ≤ r1star α β n q / (x1 * (n + 1)) := by
        rw [div_le_div_iff₀ (mul_pos hx2pos (by linarith)) (mul_pos hx1pos (by linarith))]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hx12 (by linarith)) hr1s_pos.le
      -- seller-2 ratio: larger `x` ⇒ smaller numerator `1 - x`.
      have hB : (1 - x2) / q ≤ (1 - x1) / q := by
        rw [div_le_div_iff₀ hqpos hqpos]
        exact mul_le_mul_of_nonneg_right (by linarith) hqpos.le
      exact le_trans (min_le_right _ _) (max_le_max hA hB)

/-! ## `μ` as a max in the case-3 region, decomposed for `q`-monotonicity -/

/-- Branch selection for `r₁*` (paper: `β + n(1-q) ≥ g₂(q) ⟺ q ≤ q₁`; we need only
`⟸`): for `q ≤ 1` and `q ≤ q₁`, the non-increasing first branch dominates, so
`r₁*(q) = β + n(1-q)`. Uses the crossing value `g₁(q₁) = g₂(q₁) = n + α·q₁`. -/
theorem r1star_eq_of_le_q1 (h : Constraints α β n) {q : ℝ}
    (hq1 : q ≤ 1) (hqq1 : q ≤ q1 α β n) :
    r1star α β n q = β + n * (1 - q) := by
  have hn := n_pos h
  have hα := alpha_pos h
  have hmax0 : max 0 (1 - q) = 1 - q := max_eq_right (by linarith)
  -- `g₂(q) ≤ g₂(q₁) = n + α·q₁` (g₂ non-decreasing).
  have hg2mono : min β (α * q) + n * min 1 (α * q) ≤ n + α * q1 α β n := by
    have hαle : α * q ≤ α * q1 α β n := mul_le_mul_of_nonneg_left hqq1 hα.le
    have hm1 : min β (α * q) ≤ min β (α * q1 α β n) := min_le_min le_rfl hαle
    have hm2 : min 1 (α * q) ≤ min 1 (α * q1 α β n) := min_le_min le_rfl hαle
    linarith [hm1, mul_le_mul_of_nonneg_left hm2 hn.le, g2_q1 h]
  -- `n + α·q₁ = g₁(q₁) = β + n(1-q₁) ≤ β + n(1-q)` (g₁ non-increasing).
  have hg1 : n + α * q1 α β n ≤ β + n * (1 - q) := by
    have hgq1 := g1_q1 h
    rw [max_eq_right (by linarith [q1_lt_one h] : (0:ℝ) ≤ 1 - q1 α β n)] at hgq1
    linarith [hgq1, mul_le_mul_of_nonneg_left (by linarith : 1 - q1 α β n ≤ 1 - q) hn.le]
  unfold r1star
  rw [hmax0, max_eq_left (by linarith [hg2mono, hg1])]

/-- Closed form of `μ` in the case-3 sub-region `0 < p`, `0 < q`, `q ≤ 1-p`,
`q ≤ q₁`. Here `r₁⁻ = p(n+1)`, `r₂⁻ = nq`, and `r₁*(q) = β + n(1-q)` (branch
selection), giving `μ(p,q) = max((β+n(1-q))/(p(n+1)), r₂*(p)/(nq))`. The
`r₂*(p)` numerator is left abstract — it is independent of `q`. -/
theorem μ_eq_max_case3_q (h : Constraints α β n) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hqp : q ≤ 1 - p) (hqq1 : q ≤ q1 α β n) :
    μ α β n p q = max ((β + n * (1 - q)) / (p * (n + 1))) (r2star α n p / (n * q)) := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hq1 : q ≤ 1 := le_trans hqq1 (le_of_lt (q1_lt_one h))
  have hp1 : p < 1 := by linarith
  have hpq : p + q ≤ 1 := by linarith
  have hr1lo : r1lo β n p q = p * (n + 1) := by
    simp only [r1lo]
    rw [min_eq_left (by linarith [h.c1_lo, h.c1_mid] : p ≤ β),
        max_eq_right (by linarith : (0:ℝ) ≤ 1 - q),
        min_eq_left (by linarith : p ≤ 1 - q)]
    ring
  have hr2lo : r2lo n p q = n * q := by
    simp only [r2lo]
    rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - p),
        min_eq_left (by linarith : q ≤ 1 - p)]
  have hd1 : p * (n + 1) ≠ 0 := ne_of_gt (mul_pos hp (by linarith))
  have hd2 : n * q ≠ 0 := ne_of_gt (mul_pos hn hq)
  rw [μ_eq_max_case3_raw hpq, hr1lo, hr2lo, r1star_eq_of_le_q1 h hq1 hqq1]
  simp only [ratio]
  rw [if_neg hd1, if_neg hd2]

/-! ### thm:mu-dec-q -/

/-- **thm:mu-dec-q**: for `0 ≤ p` and `0 ≤ y₁ ≤ y₂ ≤ min(q₁, 1-p)`, `μ(p,·)` is
decreasing: `min cap (μ p y₂) ≤ μ p y₁`.

Same `min cap` workaround as `mu_dec_p`: at the `0`-revenue corners `p = 0` /
`y₁ = 0` the paper's `μ(p,y₁) ≥ μ(p,y₂)` fails, but there `μ(p,y₁) ≥ cap`. Away
from them `μ(p,q) = max((β+n(1-q))/(p(n+1)), r₂*(p)/(nq))`, a `max` of two functions
decreasing in `q` (first numerator shrinks, second denominator grows). -/
theorem mu_dec_q (h : Constraints α β n) {p y1 y2 : ℝ}
    (hp : 0 ≤ p) (hy1 : 0 ≤ y1) (hy12 : y1 ≤ y2)
    (hy2 : y2 ≤ min (q1 α β n) (1 - p)) :
    min (cap α β n) (μ α β n p y2) ≤ μ α β n p y1 := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hy2q1 : y2 ≤ q1 α β n := le_trans hy2 (min_le_left _ _)
  have hy2p : y2 ≤ 1 - p := le_trans hy2 (min_le_right _ _)
  have hy1q1 : y1 ≤ q1 α β n := le_trans hy12 hy2q1
  have hy1p : y1 ≤ 1 - p := le_trans hy12 hy2p
  have hp1 : p ≤ 1 := by linarith
  rcases eq_or_lt_of_le hp with hp0 | hppos
  · -- `p = 0`: seller 1 earns `0`, so `μ(0,y₁) ≥ cap ≥ min cap (μ 0 y₂)`.
    subst hp0
    have hr1lo0 : r1lo β n 0 y1 = 0 := by
      simp only [r1lo]
      rw [min_eq_left (by linarith [h.c1_lo, h.c1_mid] : (0:ℝ) ≤ β),
          min_eq_left (le_max_left 0 (1 - y1))]
      ring
    rw [μ_eq_max_case3_raw (show (0:ℝ) + y1 ≤ 1 by linarith), hr1lo0]
    rw [show ratio (cap α β n) (r1star α β n y1) 0 = cap α β n from by rw [ratio, if_pos rfl]]
    exact le_trans (min_le_left _ _) (le_max_left _ _)
  · rcases eq_or_lt_of_le hy1 with hy10 | hy1pos
    · -- `y₁ = 0`: seller 2 earns `0`, so `μ(p,0) ≥ cap ≥ min cap (μ p y₂)`.
      subst hy10
      have hr2lo0 : r2lo n p 0 = 0 := by
        simp only [r2lo]
        rw [min_eq_left (le_max_left 0 (1 - p))]; ring
      rw [μ_eq_max_case3_raw (show p + (0:ℝ) ≤ 1 by linarith), hr2lo0]
      rw [show ratio (cap α β n) (r2star α n p) 0 = cap α β n from by rw [ratio, if_pos rfl]]
      exact le_trans (min_le_left _ _) (le_max_right _ _)
    · -- `0 < p` and `0 < y₁ ≤ y₂`: genuine monotonicity, both ratios finite.
      have hy2pos : 0 < y2 := lt_of_lt_of_le hy1pos hy12
      have hr2s_nonneg : 0 ≤ r2star α n p := by
        simp only [r2star]
        exact mul_nonneg hn.le
          (le_trans (le_min (by norm_num) (by positivity)) (le_max_right _ _))
      rw [μ_eq_max_case3_q h hppos hy1pos (by linarith : y1 ≤ 1 - p) hy1q1,
          μ_eq_max_case3_q h hppos hy2pos (by linarith : y2 ≤ 1 - p) hy2q1]
      -- seller-1 ratio: larger `q` ⇒ smaller numerator `β + n(1-q)`.
      have hA : (β + n * (1 - y2)) / (p * (n + 1)) ≤ (β + n * (1 - y1)) / (p * (n + 1)) := by
        rw [div_le_div_iff₀ (mul_pos hppos (by linarith)) (mul_pos hppos (by linarith))]
        have hnum : β + n * (1 - y2) ≤ β + n * (1 - y1) :=
          by linarith [mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) - y2 ≤ 1 - y1) hn.le]
        exact mul_le_mul_of_nonneg_right hnum (mul_pos hppos (by linarith)).le
      -- seller-2 ratio: larger `q` ⇒ larger denominator `nq`.
      have hB : r2star α n p / (n * y2) ≤ r2star α n p / (n * y1) := by
        rw [div_le_div_iff₀ (mul_pos hn hy2pos) (mul_pos hn hy1pos)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hy12 hn.le) hr2s_nonneg
      exact le_trans (min_le_right _ _) (max_le_max hA hB)

/-! ### thm:pq-dom -/

/-- **thm:pq-dom**: for `(p,q)` with `p + q ≤ 1`, there is a point `(p̂,q̂)` on the
line `p̂ + q̂ = 1` with `p̂ ≥ p`, `q̂ ≥ q`, and `min cap (μ p̂ q̂) ≤ μ(p,q)`
(the paper's `μ(p̂,q̂) ≤ μ(p,q)`, with the `min cap` workaround inherited from the
two monotonicity lemmas).

With `p' = α/(α+1)`, take `p̂ = max(p, min(p', 1-q))`, `q̂ = max(q, min(q₁, 1-p̂))`.
Three cases (on where `p` sits relative to `p'` and `1-q`) each collapse `(p̂,q̂)`
to the line and apply `mu_dec_p` and/or `mu_dec_q`. The geometric key is
`p' + q₁ > 1` (from `q₁ > 1/α`), which forces `1 - p̂ < q₁`. -/
theorem thm_pq_dom (h : Constraints α β n) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) :
    ∃ ph qh : ℝ, ph + qh = 1 ∧ p ≤ ph ∧ q ≤ qh ∧
      min (cap α β n) (μ α β n ph qh) ≤ μ α β n p q := by
  have hα := alpha_pos h
  have hpppos : 0 < α / (α + 1) := div_pos hα (by linarith)
  have hpplt1 : α / (α + 1) < 1 := by rw [div_lt_one (by linarith : (0:ℝ) < α + 1)]; linarith
  -- `p' + q₁ > 1`, i.e. `1 - p' < q₁`, from `q₁ > 1/α > 1/(α+1)`.
  have hfrac : 1 - α / (α + 1) = 1 / (α + 1) := by field_simp; ring
  have h1mpp : 1 - α / (α + 1) < q1 α β n := by
    rw [hfrac]
    exact lt_trans (one_div_lt_one_div_of_lt hα (by linarith)) (one_div_alpha_lt_q1 h)
  rcases le_total (α / (α + 1)) p with hpge | hple
  · -- Case 3: `p' ≤ p`. Take `(p̂,q̂) = (p, 1-p)`; slide only in `q`.
    refine ⟨p, 1 - p, by ring, le_rfl, by linarith, ?_⟩
    exact mu_dec_q h hp hq (by linarith)
      (le_min (by linarith [h1mpp]) le_rfl)
  · rcases le_total (1 - q) (α / (α + 1)) with h1q | h1q
    · -- Case 1: `p ≤ 1-q ≤ p'`. Take `(p̂,q̂) = (1-q, q)`; slide only in `p`.
      refine ⟨1 - q, q, by ring, by linarith, le_rfl, ?_⟩
      exact mu_dec_p h hq hp (by linarith) (le_min h1q le_rfl)
    · -- Case 2: `p ≤ p' ≤ 1-q`. Take `(p̂,q̂) = (p', 1-p')`; slide in both.
      refine ⟨α / (α + 1), 1 - α / (α + 1), by ring, hple, by linarith, ?_⟩
      have hA : min (cap α β n) (μ α β n (α / (α + 1)) q) ≤ μ α β n p q :=
        mu_dec_p h hq hp hple (le_min le_rfl h1q)
      have hB : min (cap α β n) (μ α β n (α / (α + 1)) (1 - α / (α + 1)))
              ≤ μ α β n (α / (α + 1)) q :=
        mu_dec_q h hpppos.le hq (by linarith) (le_min h1mpp.le le_rfl)
      exact le_trans (le_min (min_le_left _ _) hB) hA

/-! ### thm:3 -/

/-- **thm:3**: if `p + q ≤ 1`, then `μ(p,q) ≥ min(μ₁, μ₂, μ₃)`.

By `thm_pq_dom` reduce to a point `(p̂,q̂)` on the line `p̂+q̂=1`. That reduction is
still capped (`min cap (μ p̂ q̂) ≤ μ(p,q)`, genuinely necessary at the `0`-revenue
corners), but `min(μ₁,μ₂,μ₃) ≤ μ₁ ≤ cap` (`μ1_le_cap`) absorbs the cap here. A
trichotomy on `p̂` vs `α·q̂` dispatches to `thm_2` (`p̂ < α·q̂`, giving `μ₁`),
`thm_1_1`/`thm_1_2` (`p̂ > α·q̂`, giving `μ₂`/`μ₃` by `p̂ ≥ α` or `p̂ ≤ α`), or the
knife-edge `p̂ = α·q̂ = α/(α+1)`: there `V` is a singleton (on the line), and the
seller-1 ratio gives `μ ≥ ĉ₁/p̂ ≥ ĉ₁/p₁ = μ₁`. -/
theorem thm_3 (h : Constraints α β n) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) :
    min (μ1 α β n) (min (μ2 α β n) (μ3 α β n)) ≤ μ α β n p q := by
  obtain ⟨ph, qh, hsum, hph, hqh, hdom⟩ := thm_pq_dom h hp hq hpq
  have hα := alpha_pos h
  have hph0 : 0 ≤ ph := le_trans hp hph
  have hqh0 : 0 ≤ qh := le_trans hq hqh
  have hsum1 : (1:ℝ) ≤ ph + qh := le_of_eq hsum.symm
  -- `min(μ₁,μ₂,μ₃) ≤ μᵢ` for each `i`, and `≤ cap` (via `μ₁ ≤ cap`).
  have hBμ1 : min (μ1 α β n) (min (μ2 α β n) (μ3 α β n)) ≤ μ1 α β n := min_le_left _ _
  have hBμ2 : min (μ1 α β n) (min (μ2 α β n) (μ3 α β n)) ≤ μ2 α β n :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hBμ3 : min (μ1 α β n) (min (μ2 α β n) (μ3 α β n)) ≤ μ3 α β n :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hBcap : min (μ1 α β n) (min (μ2 α β n) (μ3 α β n)) ≤ cap α β n :=
    le_trans hBμ1 (μ1_le_cap h)
  -- `min(μ₁,μ₂,μ₃) ≤ μ(p̂,q̂)`.
  have hstar : min (μ1 α β n) (min (μ2 α β n) (μ3 α β n)) ≤ μ α β n ph qh := by
    rcases lt_trichotomy ph (α * qh) with hlt | heq | hgt
    · -- `p̂ < α·q̂`: `thm_2` gives `μ₁`.
      exact le_trans hBμ1 (thm_2 h hph0 hqh0 hlt hsum1)
    · -- `p̂ = α·q̂`: the knife-edge point `(α/(α+1), 1/(α+1))`.
      have hph_eq : ph = α / (α + 1) := by
        rw [eq_div_iff (by linarith : (α + 1:ℝ) ≠ 0)]
        linear_combination heq + α * hsum
      have hqh_eq : qh = 1 / (α + 1) := by
        rw [eq_div_iff (by linarith : (α + 1:ℝ) ≠ 0)]
        linear_combination hsum - heq
      have hn := n_pos h
      have hph_pos : 0 < ph := by rw [hph_eq]; exact div_pos hα (by linarith)
      have hqh_pos : 0 < qh := by rw [hqh_eq]; exact div_pos one_pos (by linarith)
      have hph_le_p1 : ph ≤ p1 α β n := by rw [hph_eq]; exact (p1_gt_ratio h).le
      -- `r₁*(q̂) ≥ (n+1)·ĉ₁` (global bound, `= r₁*(q₁)`).
      have hr1 : (n + 1) * chat1 α β n ≤ r1star α β n qh := by
        have h1 : (n + 1) * chat1 α β n = n + α * q1 α β n := by
          rw [← r1star_q1' h, r1star_q1 h]
        rw [h1]; exact r1star_ge h qh
      have hr1s_nonneg : 0 ≤ r1star α β n qh :=
        le_trans (mul_pos (by linarith : (0:ℝ) < n + 1)
          (by linarith [chat1_gt_one h] : (0:ℝ) < chat1 α β n)).le hr1
      have hden : (0:ℝ) < ph * (n + 1) := mul_pos hph_pos (by linarith)
      -- Seller 1's ratio clears `μ₁`: `ĉ₁/p₁ ≤ r₁*(q̂)/(p̂(n+1))`.
      have hμ1_ineq : μ1 α β n ≤ r1star α β n qh / (ph * (n + 1)) := by
        simp only [μ1]
        rw [div_le_div_iff₀ (p1_pos h) hden]
        nlinarith [mul_le_mul_of_nonneg_right hr1 hph_pos.le,
          mul_le_mul_of_nonneg_left hph_le_p1 hr1s_nonneg]
      have hμ1 : μ1 α β n ≤ μ α β n ph qh := by
        rw [μ_eq_max_case3 h hph_pos hqh_pos (le_of_eq hsum) (le_of_eq hph_eq)]
        exact le_trans hμ1_ineq (le_max_left _ _)
      exact le_trans hBμ1 hμ1
    · -- `α·q̂ < p̂`: `thm_1_1`/`thm_1_2` give `μ₂`/`μ₃`.
      rcases le_total α ph with hαle | hαge
      · exact le_trans hBμ2 (thm_1_1 h hqh0 hgt hαle)
      · exact le_trans hBμ3 (thm_1_2 h hqh0 hsum1 hgt hαge)
  -- combine with the capped domination `min cap (μ p̂ q̂) ≤ μ(p,q)`.
  exact le_trans (le_min hBcap hstar) hdom

end DataMktOligoHard
