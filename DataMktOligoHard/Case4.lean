module

public import DataMktOligoHard.Defs
import DataMktOligoHard.SpecialPoints
import Mathlib.Tactic.LinearCombination

/-!
# Case 4: the knife-edge `p = α·q` and `p + q > 1` (case4.tex)

On this region `V(p,q)` is a *segment*, not a singleton, so `μ` is a genuine
infimum. We reuse `Basic`'s revenue bounds `r1lo/r1hi/r2lo/r2hi` (the paper's
`r₁⁻,r₁⁺,r₂⁻,r₂⁺`) with the *same* `(p,q)` parameters, and only add:

* `sSum`, `d`: the sellers' total revenue and the common gap `r₁⁺-r₁⁻ = r₂⁺-r₂⁻`,
  generalized to all of `p+q ≥ 1` (revenue.tex observation);
* `r1c/r2c`: the segment's revenues parametrized by `z ∈ [0,1]`;
* `μz`: the paper's `μ(q,z)`, a reparametrization of `Basic.μ α β n (α·q) q`;
* `zhat/zstar`: the minimizing `z`.

## Status: fully proved (`thm_4` and all supporting lemmas are `sorry`-free).
-/

public section

namespace DataMktOligoHard

/-! ## Total revenue and gap on `p + q ≥ 1` (revenue.tex observation) -/

/-- Paper `s(q)`, generalized: the sellers' total revenue `min(p,β) + n` on
`p+q ≥ 1`. By the revenue.tex observation, `r₁⁻+r₂⁺ = r₁⁺+r₂⁻ = s`. -/
noncomputable def sSum (β n p : ℝ) : ℝ := min p β + n

/-- Paper `d(q)`, generalized: the common gap `r₁⁺-r₁⁻ = r₂⁺-r₂⁻`. -/
noncomputable def d (β n p q : ℝ) : ℝ := r1hi β n p q - r1lo β n p q

/-! ## The segment, parametrized by `z ∈ [0,1]` -/

/-- Seller 1's revenue `r₁(q,z) = r₁⁻ + z·d = (1-z)r₁⁻ + z·r₁⁺`. -/
noncomputable def r1c (β n p q z : ℝ) : ℝ := r1lo β n p q + z * d β n p q

/-- Seller 2's revenue `r₂(q,z) = r₂⁺ - z·d = z·r₂⁻ + (1-z)r₂⁺`. -/
noncomputable def r2c (β n p q z : ℝ) : ℝ := r2hi n p q - z * d β n p q

/-- Paper's `μ(q,z) = max(r₁*(q)/r₁(q,z), r₂*(p)/r₂(q,z))`, using the `cap`
convention for `·/0`. On the knife-edge this is `Basic.μ α β n p q` restricted
to the point of the segment indexed by `z`. -/
noncomputable def μz (α β n p q z : ℝ) : ℝ :=
  max (ratio (cap α β n) (r1star α β n q) (r1c β n p q z))
      (ratio (cap α β n) (r2star α n p) (r2c β n p q z))

/-- Paper `ẑ(q)`, the `z` where the two ratio curves cross. On the knife-edge
`p = α·q`, so we take `q` alone as the argument. -/
noncomputable def zhat (α β n q : ℝ) : ℝ :=
  r2star α n (α * q) * (r1star α β n q - r1lo β n (α * q) q)
    / ((r1star α β n q + r2star α n (α * q)) * d β n (α * q) q)

/-- Paper `z*(q) = min(1, ẑ(q))`, the `z` minimizing `μ(q,z)`. -/
noncomputable def zstar (α β n q : ℝ) : ℝ := min 1 (zhat α β n q)

/-! ## Statements to prove -/

variable {α β n : ℝ}

/-- **Observation** (revenue.tex): on `p+q ≥ 1`, `r₁⁻ + r₂⁺ = s`. -/
theorem r1lo_add_r2hi {p q : ℝ} (hp : 0 ≤ p) (hpq : 1 ≤ p + q) :
    r1lo β n p q + r2hi n p q = sSum β n p := by
  unfold r1lo r2hi sSum
  have key : min p (max 0 (1 - q)) + min q 1 = 1 := by
    rcases le_total 1 q with hq1 | hq1
    · rw [max_eq_left (by linarith), min_eq_right hp, min_eq_right (by linarith)]
      norm_num
    · rw [max_eq_right (by linarith), min_eq_right (by linarith), min_eq_left (by linarith)]
      ring
  have : n * min p (max 0 (1 - q)) + n * min q 1 = n := by
    rw [← mul_add, key, mul_one]
  linarith [this]

/-- **Observation** (revenue.tex): on `p+q ≥ 1`, `r₁⁺ + r₂⁻ = s`. -/
theorem r1hi_add_r2lo {p q : ℝ} (hq : 0 ≤ q) (hpq : 1 ≤ p + q) :
    r1hi β n p q + r2lo n p q = sSum β n p := by
  unfold r1hi r2lo sSum
  have key : min p 1 + min q (max 0 (1 - p)) = 1 := by
    rcases le_total 1 p with hp1 | hp1
    · rw [max_eq_left (by linarith), min_eq_right (by linarith), min_eq_right hq]
      norm_num
    · rw [max_eq_right (by linarith), min_eq_left (by linarith), min_eq_right (by linarith)]
      ring
  have : n * min p 1 + n * min q (max 0 (1 - p)) = n := by
    rw [← mul_add, key, mul_one]
  linarith [this]

/-- **Observation** (case4.tex l.40): `d(p,q) > 0` on `p+q > 1` (with `0 < p`,
`0 < n`). The `p=0,q>1` corner has `d=0`, hence the `0 < p` hypothesis; the
`q≤0` corner (e.g. `q=0, p>1`) also has `d≤0`, hence the `0 < q` hypothesis
(always satisfied downstream, where `q > 1/(α+1) > 0`). -/
theorem d_pos (hn : 0 < n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p + q) :
    0 < d β n p q := by
  unfold d r1hi r1lo
  have h : min p (max 0 (1 - q)) < min p 1 := by
    rcases le_total 1 q with hq1 | hq1
    · rw [max_eq_left (by linarith), min_eq_right hp.le]
      exact lt_min hp (by norm_num)
    · rw [max_eq_right (by linarith), min_eq_right (by linarith)]
      exact lt_min (by linarith) (by linarith)
  nlinarith [mul_pos hn (sub_pos.mpr h)]

/-- **Observation** (case4.tex l.6): on the knife-edge, `p + q > 1` with
`p = α·q` gives `q > 1/(α+1)`. -/
theorem q_lb (h : Constraints α β n) {q : ℝ} (hpq : 1 < α * q + q) :
    1 / (α + 1) < q := by
  have ha : 0 < α + 1 := by linarith [h.c1_lo]
  rw [div_lt_iff₀ ha]
  nlinarith [hpq]

/-- **Bridge**: on the knife-edge, `Basic.V α β n p q` is the image of `[0,1]`
under `z ↦ (r₁(q,z), r₂(q,z))`, so `Basic.μ = ⨅ z ∈ [0,1], μz`. -/
theorem μ_eq_inf_z (h : Constraints α β n) {p q : ℝ}
    (hpaq : p = α * q) (hpq1 : 1 < p + q) :
    μ α β n p q = sInf (Set.image (μz α β n p q) (Set.Icc 0 1)) := by
  -- positivity on the knife-edge
  have hα1 : (0:ℝ) < α + 1 := by linarith [h.c1_lo]
  have hqlb : 1 / (α + 1) < q := q_lb h (hpaq ▸ hpq1)
  have hqpos : 0 < q := lt_trans (div_pos one_pos hα1) hqlb
  have hppos : 0 < p := by rw [hpaq]; exact mul_pos (by linarith [h.c1_lo]) hqpos
  -- revenue identities and the gap
  have hsum1 : r1lo β n p q + r2hi n p q = min p β + n := by
    have h1 := r1lo_add_r2hi (β := β) (n := n) hppos.le hpq1.le; rwa [sSum] at h1
  have hsum2 : r1hi β n p q + r2lo n p q = min p β + n := by
    have h2 := r1hi_add_r2lo (β := β) (n := n) hqpos.le hpq1.le; rwa [sSum] at h2
  have hdpos : 0 < d β n p q := d_pos (n_pos h) hppos hqpos hpq1
  have hdne : d β n p q ≠ 0 := ne_of_gt hdpos
  have hd_eq : d β n p q = r1hi β n p q - r1lo β n p q := rfl
  have hr2lo_eq : r2lo n p q = r2hi n p q - d β n p q := by unfold d; linarith [hsum1, hsum2]
  -- V is exactly the interpolating segment
  have hV : V α β n p q = {rr : ℝ × ℝ | r1lo β n p q ≤ rr.1 ∧ rr.1 ≤ r1hi β n p q ∧
      r2lo n p q ≤ rr.2 ∧ rr.2 ≤ r2hi n p q ∧ rr.1 + rr.2 = min p β + n} := by
    unfold V
    rw [if_neg (not_le.mpr hpq1), if_neg (by rw [hpaq]; exact lt_irrefl _),
        if_neg (by rw [hpaq]; exact lt_irrefl _)]
  unfold μ
  congr 1
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨r1, r2, hmem, hm⟩
    rw [hV] at hmem
    simp only [Set.mem_setOf_eq] at hmem
    obtain ⟨hle1, hle2, hle3, hle4, hsum⟩ := hmem
    refine ⟨(r1 - r1lo β n p q) / (d β n p q), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) hdpos.le
    · exact (div_le_one hdpos).mpr (by rw [hd_eq]; linarith)
    · have hz1 : r1c β n p q ((r1 - r1lo β n p q) / (d β n p q)) = r1 := by
        rw [r1c, div_mul_cancel₀ _ hdne]; ring
      have hz2 : r2c β n p q ((r1 - r1lo β n p q) / (d β n p q)) = r2 := by
        rw [r2c, div_mul_cancel₀ _ hdne]; linarith [hsum, hsum1]
      rw [μz, hz1, hz2]; exact hm.symm
  · rintro ⟨z, ⟨hz0, hz1u⟩, hm⟩
    have hzd_le : z * d β n p q ≤ d β n p q := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - z) hdpos.le]
    have hzd_nonneg : 0 ≤ z * d β n p q := mul_nonneg hz0 hdpos.le
    refine ⟨r1c β n p q z, r2c β n p q z, ?_, ?_⟩
    · rw [hV]
      simp only [Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [r1c]; linarith
      · rw [r1c]; linarith [hd_eq]
      · rw [r2c]; linarith [hr2lo_eq]
      · rw [r2c]; linarith
      · rw [r1c, r2c]; linarith [hsum1]
    · exact hm.symm

/-! ### Knife-edge observations (case4.tex l.32) -/

/-- On the knife-edge `p = α·q` with `q > 1/(α+1)`, `r₂⁺(q) = r₂*(p)`. -/
theorem knife_r2hi_eq (h : Constraints α β n) {p q : ℝ} (hpaq : p = α * q)
    (hqlb : 1 / (α + 1) < q) : r2hi n p q = r2star α n p := by
  have hα0 : (0:ℝ) < α := by linarith [h.c1_lo]
  have hα1 : (0:ℝ) < α + 1 := by linarith [h.c1_lo]
  have key : 1 < (α + 1) * q := by rw [div_lt_iff₀ hα1] at hqlb; linarith
  have hpq_div : (α * q) / α = q := by rw [mul_comm]; exact mul_div_cancel_right₀ q (ne_of_gt hα0)
  rw [r2hi, r2star, hpaq, hpq_div]
  congr 1
  rcases le_total q 1 with hq1 | hq1
  · rw [min_eq_left hq1, min_eq_right hq1, max_eq_right (by nlinarith [key])]
  · rw [min_eq_right hq1, min_eq_left hq1,
      max_eq_right (by nlinarith [mul_nonneg hα0.le (by linarith : (0:ℝ) ≤ q)])]

/-- On the knife-edge `p = α·q`, `r₁⁺(q) ≤ r₁*(q)` (the paper's `r₁*(q) ≥ r₁⁺(q)`). -/
theorem knife_r1hi_le {p q : ℝ} (hpaq : p = α * q) :
    r1hi β n p q ≤ r1star α β n q := by
  rw [hpaq, r1hi, r1star, min_comm (α * q) β, min_comm (α * q) 1]
  exact le_max_right _ _

/-- The mediant inequality: the mediant of two fractions lies below their max. -/
private lemma mediant_le_max {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    (a + c) / (b + d) ≤ max (a / b) (c / d) := by
  rcases le_total (a / b) (c / d) with hle | hle
  · rw [max_eq_right hle, div_le_div_iff₀ (by linarith) hd]
    nlinarith [(div_le_div_iff₀ hb hd).mp hle]
  · rw [max_eq_left hle, div_le_div_iff₀ (by linarith) hb]
    nlinarith [(div_le_div_iff₀ hd hb).mp hle]

/-- Abstract lower bound for `μ(q,z)`: with `r₁(z) = Rlo + z·D` and
`r₂(z) = B − z·D`, the value `max((A+B)/s, A/Rhi)` bounds `μ(q,z)` from below.
The `cp`/`cap` corner (`r₂(z)=0`) is handled by the caller via `hcorner`. -/
private lemma muz_ge_value {A B Rlo Rhi D s cp : ℝ}
    (hApos : 0 < A) (_hBnn : 0 ≤ B) (hDpos : 0 < D) (hRlopos : 0 < Rlo)
    (hRhi : Rhi = Rlo + D) (hs : s = Rlo + B) (hDB : D ≤ B)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hcorner : B - z * D = 0 → (A + B) / s ≤ cp) :
    max ((A + B) / s) (A / Rhi)
      ≤ max (A / (Rlo + z * D)) (ratio cp B (B - z * D)) := by
  have hr1cpos : 0 < Rlo + z * D := by nlinarith [mul_nonneg hz0 hDpos.le]
  have hr2cnn : 0 ≤ B - z * D := by nlinarith [mul_le_of_le_one_left hDpos.le hz1]
  have hr1c_le : Rlo + z * D ≤ Rhi := by rw [hRhi]; nlinarith [mul_le_of_le_one_left hDpos.le hz1]
  have hRhipos : 0 < Rhi := by rw [hRhi]; linarith
  have hspos : 0 < s := by rw [hs]; linarith
  apply max_le
  · rcases eq_or_lt_of_le hr2cnn with h0 | hpos
    · rw [ratio, if_pos h0.symm]
      exact le_trans (hcorner h0.symm) (le_max_right _ _)
    · rw [ratio, if_neg (ne_of_gt hpos)]
      have hsum : (Rlo + z * D) + (B - z * D) = s := by rw [hs]; ring
      calc (A + B) / s = (A + B) / ((Rlo + z * D) + (B - z * D)) := by rw [hsum]
        _ ≤ max (A / (Rlo + z * D)) (B / (B - z * D)) := mediant_le_max hr1cpos hpos
  · refine le_trans ?_ (le_max_left _ _)
    rw [div_le_div_iff₀ hRhipos hr1cpos]
    nlinarith [mul_le_mul_of_nonneg_left hr1c_le hApos.le]

/-- Abstract value of `μ(q, z*)`: at the minimizing `z* = min(1, ẑ)` the value is
`max((A+B)/s, A/Rhi)`. Split on `ẑ ≥ 1` (value `A/Rhi`) vs `ẑ ≤ 1` (both ratio
curves equal `(A+B)/s`). No `cap` corner arises since `r₂(q,z*) > 0`. -/
private lemma muz_value {A B Rlo Rhi D s cp zh : ℝ}
    (hApos : 0 < A) (hBpos : 0 < B) (hDpos : 0 < D) (hRlopos : 0 < Rlo)
    (hRhi : Rhi = Rlo + D) (hs : s = Rlo + B) (hAge : Rhi ≤ A)
    (hzh : zh = B * (A - Rlo) / ((A + B) * D)) :
    max (A / (Rlo + min 1 zh * D)) (ratio cp B (B - min 1 zh * D))
      = max ((A + B) / s) (A / Rhi) := by
  have hAB : 0 < A + B := by linarith
  have hABne : A + B ≠ 0 := hAB.ne'
  have hDne : D ≠ 0 := hDpos.ne'
  have hAne : A ≠ 0 := hApos.ne'
  have hBne : B ≠ 0 := hBpos.ne'
  have hden : 0 < (A + B) * D := mul_pos hAB hDpos
  have hRhipos : 0 < Rhi := by rw [hRhi]; linarith
  have hspos : 0 < s := by rw [hs]; linarith
  have hsne : s ≠ 0 := hspos.ne'
  rcases le_total 1 zh with h1 | h1
  · -- ẑ ≥ 1 : z* = 1, value = A / Rhi
    simp only [min_eq_left h1, one_mul]
    have hstep : (A + B) * D ≤ B * (A - Rlo) := by
      rw [hzh, le_div_iff₀ hden] at h1; linarith
    have hBDlt : 0 < B - D := by nlinarith [hstep, mul_pos hBpos hRlopos, hAB]
    have hval_ineq : (A + B) / s ≤ A / Rhi := by
      rw [div_le_div_iff₀ hspos hRhipos, hRhi, hs]; nlinarith [hstep]
    have hg2_le : B / (B - D) ≤ A / Rhi := by
      rw [div_le_div_iff₀ hBDlt hRhipos, hRhi]; nlinarith [hstep]
    rw [← hRhi, ratio, if_neg hBDlt.ne', max_eq_left hg2_le, max_eq_right hval_ineq]
  · -- ẑ ≤ 1 : z* = ẑ, both ratio curves equal (A+B)/s
    rw [min_eq_right h1]
    have hstep2 : B * (A - Rlo) ≤ (A + B) * D := by
      rw [hzh, div_le_iff₀ hden] at h1; linarith
    have hzhD : zh * D = B * (A - Rlo) / (A + B) := by rw [hzh]; field_simp
    have hr1c_val : Rlo + zh * D = A * s / (A + B) := by rw [hzhD, hs]; field_simp; ring
    have hr2c_val : B - zh * D = B * s / (A + B) := by rw [hzhD, hs]; field_simp; ring
    have hr2pos : 0 < B - zh * D := by rw [hr2c_val]; exact div_pos (mul_pos hBpos hspos) hAB
    rw [ratio, if_neg hr2pos.ne', hr1c_val, hr2c_val]
    have e1 : A / (A * s / (A + B)) = (A + B) / s := by field_simp
    have e2 : B / (B * s / (A + B)) = (A + B) / s := by field_simp
    have hval2 : A / Rhi ≤ (A + B) / s := by
      rw [div_le_div_iff₀ hRhipos hspos, hRhi, hs]; nlinarith [hstep2]
    rw [e1, e2, max_self, max_eq_left hval2]

/-- Plain-variable arithmetic for the `cap` corner: `(A+B)/s ≤ α·β + n`
given `A ≤ β+n`, `B ≤ n`, `s ≥ 1+n`, and the constraints `α ≥ 2, β,n > 0`. -/
private lemma cap_corner_bound {A B n α β s : ℝ} (hA : A ≤ β + n) (hB : B ≤ n)
    (hs : 1 + n ≤ s) (hspos : 0 < s) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hn : 0 < n) :
    (A + B) / s ≤ α * β + n := by
  have hcap_pos : (0:ℝ) < α * β + n := by nlinarith
  rw [div_le_iff₀ hspos]
  nlinarith [mul_le_mul_of_nonneg_left hs hcap_pos.le,
    mul_nonneg (by linarith : (0:ℝ) ≤ β) (by linarith : (0:ℝ) ≤ α - 1),
    mul_nonneg hn.le (by nlinarith : (0:ℝ) ≤ α * β - 1), sq_nonneg n, hA, hB]

/-- **thm:4.1** (closed form of the infimum over `z`). -/
theorem thm_4_1 (h : Constraints α β n) {p q : ℝ}
    (hpaq : p = α * q) (hpq1 : 1 < p + q) :
    sInf (Set.image (μz α β n p q) (Set.Icc 0 1)) = μz α β n p q (zstar α β n q)
    ∧ μz α β n p q (zstar α β n q)
      = max ((r1star α β n q + r2star α n p) / sSum β n p)
            (r1star α β n q / r1hi β n p q) := by
  -- abbreviations for the paper's quantities
  set A := r1star α β n q with hAdef
  set B := r2star α n p with hBdef
  set Rlo := r1lo β n p q with hRlodef
  set Rhi := r1hi β n p q with hRhidef
  set D := d β n p q with hDdef
  set s := sSum β n p with hsdef
  -- positivity on the knife-edge
  have hα0 : (0:ℝ) < α := by linarith [h.c1_lo]
  have hα1 : (0:ℝ) < α + 1 := by linarith [h.c1_lo]
  have hβ0 : (0:ℝ) < β := by linarith [h.c1_lo, h.c1_mid]
  have hn0 : (0:ℝ) < n := n_pos h
  have hqlb : 1 / (α + 1) < q := q_lb h (hpaq ▸ hpq1)
  have hqpos : 0 < q := lt_trans (div_pos one_pos hα1) hqlb
  have hppos : 0 < p := by rw [hpaq]; exact mul_pos hα0 hqpos
  -- knife-edge observations
  have hr2 : r2hi n p q = B := knife_r2hi_eq h hpaq hqlb
  have hAR : Rhi ≤ A := knife_r1hi_le hpaq
  have hDpos : 0 < D := d_pos hn0 hppos hqpos hpq1
  have hsum1 : Rlo + r2hi n p q = min p β + n := by
    have h1 := r1lo_add_r2hi (β := β) (n := n) hppos.le hpq1.le; rwa [sSum] at h1
  have hRlopos : 0 < Rlo := by
    rw [hRlodef, r1lo]
    nlinarith [lt_min hppos hβ0,
      mul_nonneg hn0.le (le_min hppos.le (le_max_left (0:ℝ) (1 - q)))]
  have hBnn : 0 ≤ B := by rw [← hr2, r2hi]; exact mul_nonneg hn0.le (le_min hqpos.le (by norm_num))
  have hRlo_le_Rhi : Rlo ≤ Rhi := by
    rw [hRlodef, hRhidef, r1lo, r1hi]
    have hmx : max 0 (1 - q) ≤ 1 := max_le (by norm_num) (by linarith [hqpos])
    nlinarith [mul_le_mul_of_nonneg_left (min_le_min (le_refl p) hmx) hn0.le]
  have hApos : 0 < A := lt_of_lt_of_le hRlopos (le_trans hRlo_le_Rhi hAR)
  have hs_eq : s = Rlo + B := by rw [hsdef, sSum, ← hr2]; linarith [hsum1]
  have hspos : 0 < s := by rw [hs_eq]; linarith [hRlopos, hBnn]
  have hRhipos : 0 < Rhi := lt_of_lt_of_le hRlopos hRlo_le_Rhi
  -- r1c/r2c positivity/sign on [0,1]
  have hr2lo_eq : r2lo n p q = r2hi n p q - D := by
    have h2 := r1hi_add_r2lo (β := β) (n := n) hqpos.le hpq1.le
    rw [sSum] at h2; rw [hDdef, d]; linarith [hsum1]
  have hRhi_eq : Rhi = Rlo + D := by rw [hRhidef, hRlodef, hDdef, d]; ring
  have hr1c_fold : ∀ z, r1c β n p q z = Rlo + z * D := by
    intro z; rw [r1c, ← hRlodef, ← hDdef]
  have hr2c_fold : ∀ z, r2c β n p q z = B - z * D := by
    intro z; rw [r2c, ← hDdef, hr2]
  have hr2lo0 : 0 ≤ r2lo n p q := mul_nonneg hn0.le (le_min hqpos.le (le_max_left _ _))
  have hr2lo_BD : r2lo n p q = B - D := by rw [hr2lo_eq, hr2]
  have hDB : D ≤ B := by rw [hr2lo_BD] at hr2lo0; linarith
  have hr2c_nonneg : ∀ z, z ≤ 1 → 0 ≤ r2c β n p q z := by
    intro z hz1
    rw [hr2c_fold z]
    nlinarith [mul_le_of_le_one_left hDpos.le hz1, hDB]
  have hr1c_pos : ∀ z, 0 ≤ z → 0 < r1c β n p q z := by
    intro z hz0
    rw [hr1c_fold z]; nlinarith [mul_nonneg hz0 hDpos.le, hRlopos]
  have hμz_eq : ∀ z, μz α β n p q z
      = max (ratio (cap α β n) A (r1c β n p q z)) (ratio (cap α β n) B (r2c β n p q z)) := by
    intro z; rw [μz, ← hAdef, ← hBdef]
  -- crude upper bounds for the `cap` corner
  have hA_ub : A ≤ β + n := by
    rw [hAdef, r1star]
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left
        (max_le (by norm_num) (by linarith [hqpos]) : max 0 (1 - q) ≤ 1) hn0.le]
    · nlinarith [mul_le_mul_of_nonneg_left (min_le_left 1 (α * q)) hn0.le, min_le_left β (α * q)]
  have hB_ub : B ≤ n := by
    rw [← hr2, r2hi]
    nlinarith [mul_le_mul_of_nonneg_left (min_le_right q 1) hn0.le]
  -- zstar ∈ [0,1]
  have hzhat_eq : zhat α β n q = B * (A - Rlo) / ((A + B) * D) := by
    rw [zhat, ← hpaq, ← hAdef, ← hBdef, ← hRlodef, ← hDdef]
  have hzhat_nonneg : 0 ≤ zhat α β n q := by
    rw [hzhat_eq]
    apply div_nonneg (mul_nonneg hBnn (by linarith [hAR, hRlo_le_Rhi]))
    exact mul_nonneg (by linarith [hApos, hBnn]) hDpos.le
  have hzstar_mem : zstar α β n q ∈ Set.Icc (0:ℝ) 1 := by
    rw [Set.mem_Icc, zstar]
    exact ⟨le_min (by norm_num) hzhat_nonneg, min_le_left _ _⟩
  -- make the abbreviations opaque so the arithmetic tactics stay fast
  clear_value A B Rlo Rhi D s
  have hBpos : 0 < B := by rw [← hr2, r2hi]; exact mul_pos hn0 (lt_min hqpos one_pos)
  have hVal : μz α β n p q (zstar α β n q)
      = max ((A + B) / s) (A / Rhi) := by
    have hzstar_eq : zstar α β n q = min 1 (B * (A - Rlo) / ((A + B) * D)) := by
      rw [zstar, hzhat_eq]
    have hzst_nonneg : 0 ≤ min 1 (B * (A - Rlo) / ((A + B) * D)) :=
      le_min (by norm_num) (by rw [← hzhat_eq]; exact hzhat_nonneg)
    have hr1pos : 0 < Rlo + min 1 (B * (A - Rlo) / ((A + B) * D)) * D := by
      nlinarith only [mul_nonneg hzst_nonneg hDpos.le, hRlopos]
    rw [hμz_eq (zstar α β n q), hr1c_fold, hr2c_fold, hzstar_eq, ratio, if_neg hr1pos.ne']
    exact muz_value hApos hBpos hDpos hRlopos hRhi_eq hs_eq hAR rfl
  -- the concrete `cap`-corner bound `(A+B)/s ≤ cap`, valid whenever `B = z·D`
  have hcorner : ∀ z, 0 ≤ z → z ≤ 1 → B - z * D = 0 → (A + B) / s ≤ cap α β n := by
    intro z hz0 hz1 h0
    have hBleD : B ≤ D := by nlinarith only [mul_le_of_le_one_left hDpos.le hz1, h0]
    have hr2lo_zero : r2lo n p q = 0 := by
      rw [hr2lo_BD]; linarith only [le_antisymm hBleD hDB]
    have hp1 : 1 ≤ p := by
      rw [r2lo] at hr2lo_zero
      have hmin0 : min q (max 0 (1 - p)) = 0 := by
        rcases mul_eq_zero.mp hr2lo_zero with h' | h'
        · exact absurd h' (ne_of_gt hn0)
        · exact h'
      by_contra hlt
      push Not at hlt
      exact absurd hmin0 (ne_of_gt (lt_min hqpos (lt_max_of_lt_right (by linarith only [hlt]))))
    have hs_lb : 1 + n ≤ s := by
      rw [hsdef, sSum]
      linarith only [le_min hp1 (by linarith only [h.c1_lo, h.c1_mid] : (1:ℝ) ≤ β)]
    rw [cap]
    exact cap_corner_bound hA_ub hB_ub hs_lb hspos h.c1_lo
      (by linarith [h.c1_lo, h.c1_mid]) hn0
  have hLBval : ∀ z ∈ Set.Icc (0:ℝ) 1, max ((A + B) / s) (A / Rhi) ≤ μz α β n p q z := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := hz
    have hr1cpos := hr1c_pos z hz0
    have hratio1 : ratio (cap α β n) A (r1c β n p q z) = A / r1c β n p q z := by
      rw [ratio, if_neg (ne_of_gt hr1cpos)]
    rw [hμz_eq z, hratio1, hr1c_fold z, hr2c_fold z]
    exact muz_ge_value hApos hBnn hDpos hRlopos hRhi_eq hs_eq hDB hz0 hz1 (hcorner z hz0 hz1)
  -- assembly
  refine ⟨?_, hVal⟩
  have hLeast : IsLeast (Set.image (μz α β n p q) (Set.Icc 0 1))
      (μz α β n p q (zstar α β n q)) := by
    constructor
    · exact ⟨zstar α β n q, hzstar_mem, rfl⟩
    · rintro y ⟨z, hz, rfl⟩; rw [hVal]; exact hLBval z hz
  exact hLeast.csInf_eq

/-- **thm:mu4**: at the special point `(p₄,q₄) = (α·q₁, q₁)`, the case-4 value is `μ₄`. -/
theorem thm_mu4 (h : Constraints α β n) :
    μz α β n (p4 α β n) (q4 α β n) (zstar α β n (q4 α β n)) = μ4 α β n := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hβ : (0:ℝ) < β := by linarith [h.c1_lo, h.c1_mid]
  have hq1pos := q1_pos h
  have hpaq : p4 α β n = α * q4 α β n := by rw [p4, q4]
  have hp0 : 0 ≤ p4 α β n := by rw [p4]; exact (mul_pos hα hq1pos).le
  have hq0 : 0 ≤ q4 α β n := by rw [q4]; exact hq1pos.le
  have hpq1 : 1 < p4 α β n + q4 α β n := by
    rw [p4, q4]; nlinarith [one_lt_alpha_mul_q1 h, hq1pos]
  rw [(thm_4_1 h hpaq hpq1).2, p4, q4]
  -- the four revenue values at `(α·q₁, q₁)`
  have hA : r1star α β n (q1 α β n) = n + α * q1 α β n := r1star_q1 h
  have hB : r2star α n (α * q1 α β n) = n * q1 α β n := by
    rw [r2star]
    have hdiv : (α * q1 α β n) / α = q1 α β n := by
      rw [mul_comm]; exact mul_div_cancel_right₀ _ (ne_of_gt hα)
    rw [hdiv, min_eq_right (q1_lt_one h).le,
        max_eq_right (by nlinarith [one_lt_alpha_mul_q1 h, hq1pos])]
  have hRhi : r1hi β n (α * q1 α β n) (q1 α β n) = α * q1 α β n + n := by
    rw [r1hi, min_eq_left (alpha_mul_q1_lt_beta h).le,
        min_eq_right (one_lt_alpha_mul_q1 h).le, mul_one]
  have hS : sSum β n (α * q1 α β n) = α * q1 α β n + n := by
    rw [sSum, min_eq_left (alpha_mul_q1_lt_beta h).le]
  rw [hA, hB, hRhi, hS]
  have hden : 0 < α * q1 α β n + n := by nlinarith [mul_pos hα hq1pos]
  have h2nd : (n + α * q1 α β n) / (α * q1 α β n + n) = 1 := by
    rw [div_eq_one_iff_eq (ne_of_gt hden)]; ring
  have hαn : (α + n) ≠ 0 := ne_of_gt (alpha_add_n_pos h)
  have hL2ne : n ^ 2 + α * n + α * β ≠ 0 := by positivity
  have hX : (n + α * q1 α β n + n * q1 α β n) / (α * q1 α β n + n) = μ4 α β n := by
    rw [μ4, L2, q1]; field_simp; ring
  have hμ4ge : (1:ℝ) ≤ μ4 α β n := by
    rw [μ4]; have : 0 ≤ β * n / L2 α β n := by rw [L2]; positivity
    linarith
  rw [h2nd, hX, max_eq_left hμ4ge]

/-- `μ(p₄, q₄) = μ₄` -/
theorem μ_p4_q4 (h : Constraints α β n) :
    μ α β n (p4 α β n) (q4 α β n) = μ4 α β n := by
  have hpaq : p4 α β n = α * q4 α β n := by rw [p4, q4]
  have hpq1 : 1 < p4 α β n + q4 α β n := by
    rw [p4, q4]; nlinarith [one_lt_alpha_mul_q1 h, q1_pos h]
  rw [μ_eq_inf_z h hpaq hpq1, (thm_4_1 h hpaq hpq1).1, thm_mu4 h]

/-- **thm:4.2** (the case-4 lower bound): on the knife-edge with `p+q>1`,
`inf_z μ(q,z) ≥ min(μ₂, μ₄)`. -/
theorem thm_4_2 (h : Constraints α β n) {p q : ℝ}
    (hpaq : p = α * q) (hpq1 : 1 < p + q) :
    min (μ2 α β n) (μ4 α β n) ≤ μz α β n p q (zstar α β n q) := by
  have hα := alpha_pos h
  have hn := n_pos h
  have hβ : (0:ℝ) < β := by linarith [h.c1_lo, h.c1_mid]
  have hα1 : (0:ℝ) < α + 1 := by linarith [h.c1_lo]
  have hqlb : 1 / (α + 1) < q := q_lb h (hpaq ▸ hpq1)
  have hqpos : 0 < q := lt_trans (div_pos one_pos hα1) hqlb
  have hq1pos := q1_pos h
  have hr2 : r2star α n p = n * min q 1 := by rw [← knife_r2hi_eq h hpaq hqlb, r2hi]
  -- reduce to `(r1* + r2*) / s`
  rw [(thm_4_1 h hpaq hpq1).2]
  refine le_trans ?_ (le_max_left _ _)
  have hsSum : sSum β n p = min β (α * q) + n := by rw [sSum, hpaq, min_comm]
  rcases le_total q 1 with hqle1 | hqge1
  · -- q ≤ 1 : bound below by μ₄
    refine le_trans (min_le_right _ _) ?_
    have hr2v : r2star α n p = n * q := by rw [hr2, min_eq_left hqle1]
    have hαq_le_α : α * q ≤ α := by nlinarith [mul_le_mul_of_nonneg_left hqle1 hα.le]
    have hαqβ : α * q ≤ β := by linarith [h.c1_mid]
    have hs : sSum β n p = α * q + n := by rw [hsSum, min_eq_right hαqβ]
    have hden_r : 0 < α * q + n := by nlinarith [mul_pos hα hqpos]
    have hden_l : 0 < α * q1 α β n + n := by nlinarith [mul_pos hα hq1pos]
    rcases le_total q (q1 α β n) with hqq1 | hqq1
    · -- q ≤ q₁ : (β+n)/(αq+n), decreasing
      have hμ4 : μ4 α β n = (β + n) / (α * q1 α β n + n) := by
        rw [μ4, L2, q1]; field_simp; ring
      have hr1lb : β + n - n * q ≤ r1star α β n q := by
        rw [r1star]; refine le_trans ?_ (le_max_left _ _)
        nlinarith [mul_le_mul_of_nonneg_left (le_max_right 0 (1 - q)) hn.le]
      rw [hμ4, hs, hr2v, div_le_div_iff₀ hden_l hden_r]
      nlinarith [mul_nonneg (by linarith [hr1lb] : (0:ℝ) ≤ r1star α β n q + n * q - (β + n))
          hden_l.le,
        mul_nonneg (by linarith : (0:ℝ) ≤ β + n)
          (by nlinarith [mul_le_mul_of_nonneg_left hqq1 hα.le] :
            (0:ℝ) ≤ α * q1 α β n + n - (α * q + n))]
    · -- q₁ ≤ q ≤ 1 : 1 + nq/(αq+n), increasing
      have h1αq : 1 ≤ α * q := by
        nlinarith [one_lt_alpha_mul_q1 h, mul_le_mul_of_nonneg_left hqq1 hα.le]
      have hr1lb2 : α * q + n ≤ r1star α β n q := by
        rw [r1star]; refine le_trans (le_of_eq ?_) (le_max_right _ _)
        rw [min_eq_right hαqβ, min_eq_left h1αq, mul_one]
      have hμ4c : μ4 α β n = 1 + n * q1 α β n / (α * q1 α β n + n) := by
        rw [μ4, L2, q1]; field_simp; ring
      have step : 1 + n * q / (α * q + n) ≤ (r1star α β n q + n * q) / (α * q + n) := by
        have he : (1:ℝ) + n * q / (α * q + n) = (α * q + n + n * q) / (α * q + n) := by
          field_simp
        rw [he, div_le_div_iff₀ hden_r hden_r]
        nlinarith [mul_le_mul_of_nonneg_right hr1lb2 hden_r.le]
      have step2 : 1 + n * q1 α β n / (α * q1 α β n + n) ≤ 1 + n * q / (α * q + n) := by
        have : n * q1 α β n / (α * q1 α β n + n) ≤ n * q / (α * q + n) := by
          rw [div_le_div_iff₀ hden_l hden_r]
          nlinarith [mul_nonneg (mul_nonneg hn.le hn.le)
            (by linarith [hqq1] : (0:ℝ) ≤ q - q1 α β n)]
        linarith
      rw [hs, hr2v, hμ4c]
      exact le_trans step2 step
  · -- q ≥ 1 : bound below by μ₂
    refine le_trans (min_le_left _ _) ?_
    have hr2C : r2star α n p = n := by rw [hr2, min_eq_right hqge1, mul_one]
    have h1αq : 1 ≤ α * q := by nlinarith [mul_le_mul_of_nonneg_left hqge1 hα.le, h.c1_lo]
    have hr1lbC : min β (α * q) + n ≤ r1star α β n q := by
      rw [r1star]; refine le_trans (le_of_eq ?_) (le_max_right _ _)
      rw [min_eq_left h1αq, mul_one]
    have hαqpos : 0 < α * q := mul_pos hα hqpos
    have hmn : 0 < min β (α * q) + n := by
      have : 0 < min β (α * q) := lt_min hβ hαqpos; linarith
    have hsqrt : Real.sqrt (L2 α β n) ≤ β + n := by
      rw [show β + n = Real.sqrt ((β + n) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      apply Real.sqrt_le_sqrt
      rw [L2]
      nlinarith [mul_nonneg (by linarith [h.c1_mid] : (0:ℝ) ≤ β - α) hβ.le,
        mul_nonneg hn.le (by linarith [h.c1_mid, h.c1_lo] : (0:ℝ) ≤ 2 * β - α)]
    have hμ2bound : μ2 α β n ≤ (β + 2 * n) / (β + n) := by
      rw [μ2, one_div, q2, inv_div, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [mul_nonneg (by linarith [hsqrt] : (0:ℝ) ≤ β + n - Real.sqrt (L2 α β n))
        (by linarith : (0:ℝ) ≤ β + n)]
    rw [hr2C, hsSum]
    calc μ2 α β n ≤ (β + 2 * n) / (β + n) := hμ2bound
      _ ≤ (min β (α * q) + 2 * n) / (min β (α * q) + n) := by
          rw [div_le_div_iff₀ (by linarith) hmn]
          nlinarith [mul_nonneg hn.le (by linarith [min_le_left β (α * q)] :
            (0:ℝ) ≤ β - min β (α * q))]
      _ ≤ (r1star α β n q + n) / (min β (α * q) + n) := by
          rw [div_le_div_iff₀ hmn hmn]
          nlinarith [mul_le_mul_of_nonneg_right hr1lbC hmn.le]

/-- **thm:4** (paper-facing, `z`-free — same shape as `thm_2`/`thm_3`): on the
knife-edge `p = α·q` with `p + q > 1` (and `0 ≤ p, q`), `μ(p,q) ≥ min(μ₂,μ₄)`.
The `min cap` handles the `x/0` corners of the `cap` convention; downstream
`cStar ≤ cap` recovers `cStar ≤ μ`. Proved from `thm_4_2` via `μ_eq_inf_z`. -/
theorem thm_4 (h : Constraints α β n) {p q : ℝ}
    (hpaq : p = α * q) (hpq1 : 1 < p + q) :
    min (μ2 α β n) (μ4 α β n) ≤ μ α β n p q := by
  rw [μ_eq_inf_z h hpaq hpq1, (thm_4_1 h hpaq hpq1).1]
  exact thm_4_2 h hpaq hpq1

end DataMktOligoHard
