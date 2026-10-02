/-
# Injectivity of a Böttcher coordinate on the far region

Let `p_c = T_c ∘ T_c` be the holomorphic quartic second iterate of the tricorn map
`T_c z = conj z ^ 2 + c`, and let `φ` be *any* analytic solution of the Böttcher problem
on the escape set `{G_c > 0}`:

* `φ ∘ p_c = φ ^ 4`,
* `‖φ z‖ = exp (G_c z)`,
* `φ z / z → 1` at infinity.

`Work.Bottcher.Core.eq_bottcher_of_analytic` identifies `φ` with the explicit product
formula `Work.Bottcher.bottcher c` on the far region `{escapeRadius c ≤ ‖z‖}`.  This file
shows that `bottcher c` is *injective* on the closed far region `{farR c ≤ ‖z‖}`
(`farR c = 4096 (‖c‖² + 3‖c‖ + 1)`), whence `φ` is injective there.

The injectivity of `bottcher c` far out is a consequence of the explicit inverse branch
`Work.Bottcher.Inverse.farInvPsi`:

* `‖bottcherSeries c z‖ ≤ 1/32` for `farR c ≤ ‖z‖` (`norm_bottcherSeries_le_far` plus
  `farR c ≥ 4096 K`, `K = ‖c‖² + 3‖c‖ + 1 ≥ 1`);
* hence `bottcher c z = z · exp (B_c z)` satisfies `‖z‖/2 ≤ ‖bottcher c z‖` and
  `‖z - bottcher c z‖ ≤ ‖z‖/16 ≤ ‖bottcher c z‖/8` (the standard estimate
  `‖exp x - 1‖ ≤ 2‖x‖` and `‖exp x‖ ≥ 1/2` for `‖x‖ ≤ 1/2`);
* so `z` lies in the ball `closedBall (bottcher c z) (‖bottcher c z‖/8)` on which the far
  inverse branch of the Böttcher coordinate is unique (`farInvPsi_unique`), giving
  `z = farInvPsi c (bottcher c z)`; two points with the same image therefore coincide.
-/
import Mathlib
import Submission.Work.Bottcher.Inverse.BottcherReflect
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic
import Submission.Work.Bottcher.Inverse.norm_bottcherSeries_le_far
import Submission.Work.Bottcher.Inverse.norm_bottcherSeries_sub_le
import Submission.Work.Bottcher.Inverse.exists_farInverseBottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Inverse

open Filter Function
open scoped Topology ComplexConjugate

noncomputable section

/-! ## Elementary consequences of the definition of `farR` -/

/-- `K = ‖c‖² + 3‖c‖ + 1 ≥ 1`. -/
theorem one_le_farInvC (c : ℂ) : 1 ≤ ‖c‖ ^ 2 + 3 * ‖c‖ + 1 := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  nlinarith [sq_nonneg ‖c‖]

/-- The far radius of the inverse branch is dominated by half of `farR c`. -/
theorem farInvR_le_half_farR (c : ℂ) : farInvR c ≤ farR c / 2 := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [farInvR, farR]
  nlinarith [sq_nonneg ‖c‖]

/-! ## The Böttcher series is small far out -/

/-- `‖B_c z‖ ≤ 1/32` for `‖z‖ ≥ farR c`. -/
theorem norm_bottcherSeries_le_thirtysecond (c z : ℂ) (hz : farR c ≤ ‖z‖) :
    ‖Work.Bottcher.bottcherSeries c z‖ ≤ 1 / 32 := by
  have hK := one_le_farInvC c
  have hKpos : (0 : ℝ) < ‖c‖ ^ 2 + 3 * ‖c‖ + 1 := lt_of_lt_of_le zero_lt_one hK
  have h1 : 4096 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) ≤ ‖z‖ := by
    rw [farR] at hz
    linarith
  have h2 : (4096 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1)) ^ 2 ≤ ‖z‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h3 : 32 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1)
      ≤ (4096 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1)) ^ 2 := by
    nlinarith [hK, hKpos]
  have h4 : 32 * (‖c‖ ^ 2 + 3 * ‖c‖ + 1) ≤ ‖z‖ ^ 2 := le_trans h3 h2
  have h5 := norm_bottcherSeries_le_far c z (le_trans (le_farR_64 c) hz)
  have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (farR_pos c) hz
  have h6 : (‖c‖ ^ 2 + 3 * ‖c‖ + 1) / ‖z‖ ^ 2 ≤ 1 / 32 := by
    rw [div_le_iff₀ (pow_pos hzpos 2)]
    linarith
  linarith

/-- `‖exp x‖ ≥ 1/2` whenever `‖x‖ ≤ 1/2`. -/
theorem half_le_norm_exp {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) : (1 / 2 : ℝ) ≤ ‖Complex.exp x‖ := by
  rw [Complex.norm_exp]
  have h1 : -(1 / 2 : ℝ) ≤ x.re := by
    have h2 := Complex.re_le_norm (-x)
    rw [Complex.neg_re, norm_neg] at h2
    linarith
  have h3 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have := Real.add_one_le_exp (-(1 / 2 : ℝ))
    linarith
  calc (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := h3
    _ ≤ Real.exp x.re := Real.exp_le_exp.mpr h1

/-! ## Two estimates for the product formula far out -/

/-- Far out, `bottcher c` does not shrink by more than a factor `2`:
`‖z‖/2 ≤ ‖bottcher c z‖`. -/
theorem norm_bottcher_ge_half (c z : ℂ) (hz : farR c ≤ ‖z‖) :
    ‖z‖ / 2 ≤ ‖Work.Bottcher.bottcher c z‖ := by
  have hB := norm_bottcherSeries_le_thirtysecond c z hz
  have hBhalf : ‖Work.Bottcher.bottcherSeries c z‖ ≤ 1 / 2 := by linarith
  have hexp := half_le_norm_exp hBhalf
  rw [Work.Bottcher.bottcher, norm_mul]
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  nlinarith

/-- Far out, `bottcher c` moves every point by at most an eighth of the modulus of its
image: `‖z - bottcher c z‖ ≤ ‖bottcher c z‖/8`. -/
theorem norm_sub_bottcher_le (c z : ℂ) (hz : farR c ≤ ‖z‖) :
    ‖z - Work.Bottcher.bottcher c z‖ ≤ ‖Work.Bottcher.bottcher c z‖ / 8 := by
  have hB := norm_bottcherSeries_le_thirtysecond c z hz
  have hge := norm_bottcher_ge_half c z hz
  have hdisp : ‖z - Work.Bottcher.bottcher c z‖ ≤ ‖z‖ / 16 := by
    have hrew : z - Work.Bottcher.bottcher c z
        = z * (1 - Complex.exp (Work.Bottcher.bottcherSeries c z)) := by
      rw [Work.Bottcher.bottcher]; ring
    rw [hrew, norm_mul, norm_sub_rev (1 : ℂ)]
    have hexp := Complex.norm_exp_sub_one_le
      (x := Work.Bottcher.bottcherSeries c z) (by linarith)
    have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    nlinarith
  linarith

/-! ## Injectivity of the product formula on the closed far region -/

/-- On `{farR c ≤ ‖z‖}` the product-formula Böttcher coordinate is a right inverse of the
far inverse branch `farInvPsi c`, hence injective there. -/
theorem bottcher_injOn_far (c : ℂ) {a b : ℂ} (ha : farR c ≤ ‖a‖) (hb : farR c ≤ ‖b‖)
    (h : Work.Bottcher.bottcher c a = Work.Bottcher.bottcher c b) : a = b := by
  have hwa : farInvR c ≤ ‖Work.Bottcher.bottcher c a‖ := by
    have h1 := norm_bottcher_ge_half c a ha
    have h2 := farInvR_le_half_farR c
    linarith
  have hmem : a ∈ Metric.closedBall (Work.Bottcher.bottcher c a)
      (‖Work.Bottcher.bottcher c a‖ / 8) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact norm_sub_bottcher_le c a ha
  have h1 : a = farInvPsi c (Work.Bottcher.bottcher c a) :=
    farInvPsi_unique c (Work.Bottcher.bottcher c a) hwa hmem rfl
  have hwb : farInvR c ≤ ‖Work.Bottcher.bottcher c b‖ := by rw [← h]; exact hwa
  have hmem' : b ∈ Metric.closedBall (Work.Bottcher.bottcher c b)
      (‖Work.Bottcher.bottcher c b‖ / 8) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact norm_sub_bottcher_le c b hb
  have h2 : b = farInvPsi c (Work.Bottcher.bottcher c b) :=
    farInvPsi_unique c (Work.Bottcher.bottcher c b) hwb hmem' rfl
  rw [h1, h2, h]

/-! ## The main theorem -/

theorem injOn_far (c : ℂ) (φ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ φ {z : ℂ | 0 < Work.Bottcher.green c z})
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z → ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ)))
    {a b : ℂ} (ha : Work.Bottcher.Inverse.farR c ≤ ‖a‖) (hb : Work.Bottcher.Inverse.farR c ≤ ‖b‖)
    (hφ : φ a = φ b) : a = b := by
  have haR : Work.Bottcher.escapeRadius c ≤ ‖a‖ := le_trans (escapeRadius_le_farR c) ha
  have hbR : Work.Bottcher.escapeRadius c ≤ ‖b‖ := le_trans (escapeRadius_le_farR c) hb
  have hmono : AnalyticOnNhd ℂ φ {z : ℂ | Work.Bottcher.escapeRadius c ≤ ‖z‖} :=
    han.mono (fun z hz => green_pos_of_escapeRadius_le c z hz)
  have hφa : φ a = Work.Bottcher.bottcher c a :=
    Work.Bottcher.Core.eq_bottcher_of_analytic c φ hmono
      (fun z hz => hfe z (green_pos_of_escapeRadius_le c z hz))
      (fun z hz => hmod z (green_pos_of_escapeRadius_le c z hz)) has haR
  have hφb : φ b = Work.Bottcher.bottcher c b :=
    Work.Bottcher.Core.eq_bottcher_of_analytic c φ hmono
      (fun z hz => hfe z (green_pos_of_escapeRadius_le c z hz))
      (fun z hz => hmod z (green_pos_of_escapeRadius_le c z hz)) has hbR
  have hbot : Work.Bottcher.bottcher c a = Work.Bottcher.bottcher c b := by
    rw [← hφa, ← hφb]
    exact hφ
  exact bottcher_injOn_far c ha hb hbot

end

end Work.Bottcher.Inverse
