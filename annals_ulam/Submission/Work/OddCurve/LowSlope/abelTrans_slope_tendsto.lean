import Mathlib
import Submission.Work.OddRadon.Abel
import Submission.Work.OddCurve.LowSlope.abs_rpow_sub_div_le

/-!
# The right-hand derivative of the Abel transform `T_β γ` at `c`

`Work.OddRadon.abelTrans β γ c = ∫_0^c γ s (c² - s²)^β ds`, and the exponent-lowering recursion
`T_β' = 2βc T_{β-1}` says that its right-hand derivative at `c` is `2βc · T_{β-1} γ c`.  This file
proves the one-sided difference-quotient form

`(T_β γ (c+h) - T_β γ c)/h → 2βc · T_{β-1} γ c` as `h → 0⁺`

for `γ` which is merely **continuous and bounded** on `(0, 2c)` and `β > 0` (the hypothesis that
makes the boundary term `γ c · (c²-c²)^β` vanish and the kernel `(c²-s²)^{β-1}` integrable).

The difference of the two integrals is split into the fixed-domain part and the boundary tongue:

* the tongue `∫_c^{c+h} γ s ((c+h)²-s²)^β` is `O(h^β) = o(h)` because the kernel vanishes at its own
  right endpoint;
* on the fixed domain `(0,c)` the difference quotients converge pointwise to the derivative of the
  kernel in `c` (chain rule) and are dominated by the integrable function
  `M · 6cβ ((c²-s²)^{β-1} + (2c)^{2β-2})` (this is `Work.OddCurve.LowSlope.abs_rpow_sub_div_le`),
  so dominated convergence applies.

No derivative of `γ` is ever needed: only the kernel is differentiated.
-/

namespace Work.OddCurve.LowSlope

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

/-- A function continuous on `(a,b)` is a.e. strongly measurable for the restriction of Lebesgue
measure to `(a,b]` (the two intervals differ by the null set `{b}`). -/
private lemma aestronglyMeasurable_of_continuousOn_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Ioo a b)) :
    AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)) := by
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b))]
  exact hf.aestronglyMeasurable measurableSet_Ioo

/-- A function continuous on `(a,b)` and bounded there by `C` is interval integrable on `(a,b)`. -/
private lemma intervalIntegrable_of_continuousOn_Ioo_of_bound {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Ioo a b)) (hb : ∀ s ∈ Set.Ioo a b, |f s| ≤ C) :
    IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun' ?_ ?_
  · rw [Set.uIoc_of_le hab.le, ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b))]
    exact hf.aestronglyMeasurable measurableSet_Ioo
  · rw [Set.uIoc_of_le hab.le, Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b)).symm]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs]
    exact hb s hs

/-- The Abel kernel `s ↦ (c² - s²)^p` is interval integrable on `(0,c)` for `p > -1` and `c > 0`
(the endpoint singularity at `s = c` is integrable exactly in this range). -/
private lemma intervalIntegrable_csq_sub_sq_rpow {c p : ℝ} (hc : 0 < c) (hp : -1 < p) :
    IntervalIntegrable (fun s : ℝ => (c ^ 2 - s ^ 2) ^ p) volume (0 : ℝ) c := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ p) volume (0:ℝ) c :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have h2 : IntervalIntegrable (fun s : ℝ => (c - s) ^ p) volume (0:ℝ) c := by
    simpa using (h1.comp_sub_left c).symm
  have hcont : ContinuousOn (fun s : ℝ => (c ^ 2 - s ^ 2) ^ p) (Set.Ioo 0 c) := by
    apply ContinuousOn.rpow
    · exact continuousOn_const.sub (continuousOn_id.pow 2)
    · exact continuousOn_const
    · intro x hx
      left
      exact ne_of_gt (by nlinarith [hx.1, hx.2, hc])
  refine (h2.const_mul (c ^ p + (2*c) ^ p)).mono_fun' ?_ ?_
  · rw [Set.uIoc_of_le hc.le,
        ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := c))]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · rw [Set.uIoc_of_le hc.le]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    have h1' : 0 ≤ c - s := by linarith [hs.2]
    have h2' : 0 ≤ c + s := by linarith [hs.1, hc.le]
    have hkey : (c ^ 2 - s ^ 2) ^ p = (c - s) ^ p * (c + s) ^ p := by
      rw [show c ^ 2 - s ^ 2 = (c - s) * (c + s) by ring, Real.mul_rpow h1' h2']
    have h3' : (c + s) ^ p ≤ c ^ p + (2 * c) ^ p := by
      rcases lt_or_ge 0 p with hp0 | hp0
      · have hle : c + s ≤ 2 * c := by linarith [hs.2]
        exact (Real.rpow_le_rpow h2' hle hp0.le).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) p))
      · exact (Real.rpow_le_rpow_of_nonpos hc (by linarith [hs.1]) hp0).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) p))
    have h4 : 0 ≤ (c - s) ^ p := Real.rpow_nonneg h1' p
    have h5 : (c ^ 2 - s ^ 2) ^ p ≤ (c ^ p + (2*c) ^ p) * (c - s) ^ p := by
      rw [hkey]
      calc (c-s)^p * (c+s)^p ≤ (c-s)^p * (c^p + (2*c)^p) := mul_le_mul_of_nonneg_left h3' h4
        _ = (c^p + (2*c)^p) * (c-s)^p := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by nlinarith [hs.1, hs.2, hc]) p)]
    exact h5

/-- **The fixed-domain dominated-convergence step.**  The difference quotients of the kernel in `c`
converge to `2βc (c²-s²)^{β-1}` for each `s ∈ (0,c)` (a.e. `s`: the only failure point is `s = c`),
and are dominated by `M · 6cβ ((c²-s²)^{β-1} + (2c)^{2β-2})`, which is integrable. -/
private lemma abelTrans_diffQuot_tendsto {β M c : ℝ} (hβ : 0 < β) (hc : 0 < c) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Set.Ioo (0 : ℝ) (2 * c)))
    (hγb : ∀ s ∈ Set.Ioo (0 : ℝ) (2 * c), |γ s| ≤ M) :
    Filter.Tendsto
      (fun h : ℝ => ∫ s in (0 : ℝ)..c,
        γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c)) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (γ c)) (hγb c ⟨hc, by linarith⟩)
  have hmem : Set.Iio c ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    Filter.le_def.mp nhdsWithin_le_nhds (Set.Iio c) (Iio_mem_nhds hc)
  have hval : (∫ s, γ s * (2 * β * c * (c ^ 2 - s ^ 2) ^ (β - 1))
        ∂(volume.restrict (Set.Ioc 0 c)))
      = 2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c := by
    rw [← intervalIntegral.integral_of_le hc.le]
    simp only [Work.OddRadon.abelTrans]
    rw [show (fun s : ℝ => γ s * (2 * β * c * (c ^ 2 - s ^ 2) ^ (β - 1)))
        = (fun s : ℝ => 2 * β * c * (γ s * (c ^ 2 - s ^ 2) ^ (β - 1))) from
      funext (fun s => by ring)]
    rw [intervalIntegral.integral_const_mul]
  have hkey : Tendsto
      (fun h : ℝ => ∫ s, γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h
        ∂(volume.restrict (Set.Ioc 0 c)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (∫ s, γ s * (2 * β * c * (c ^ 2 - s ^ 2) ^ (β - 1))
        ∂(volume.restrict (Set.Ioc 0 c)))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Set.Ioc 0 c)) (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
      (F := fun h s => γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h)
      (f := fun s => γ s * (2 * β * c * (c ^ 2 - s ^ 2) ^ (β - 1)))
      (bound := fun s => M * (6 * c * β) * (c ^ 2 - s ^ 2) ^ (β - 1)
        + M * (6 * c * β) * (2 * c) ^ (2 * β - 2))
      ?_ ?_ ?_ ?_
    · -- a.e. strong measurability of the integrands
      filter_upwards [self_mem_nhdsWithin, hmem] with h hpos hlt
      have h0 : (0:ℝ) < h := hpos
      have hγcont : ContinuousOn γ (Set.Ioo 0 c) :=
        hγc.mono (fun x hx => ⟨hx.1, by linarith [hx.2, hc]⟩)
      have hk1 : ContinuousOn (fun s : ℝ => ((c+h)^2 - s^2)^β) (Set.Ioo 0 c) := by
        apply ContinuousOn.rpow (continuousOn_const.sub (continuousOn_id.pow 2)) continuousOn_const
        intro x hx
        left
        change (c + h) ^ 2 - x ^ 2 ≠ 0
        exact ne_of_gt (by nlinarith [hx.1, hx.2, h0, hc])
      have hk0 : ContinuousOn (fun s : ℝ => (c^2 - s^2)^β) (Set.Ioo 0 c) := by
        apply ContinuousOn.rpow (continuousOn_const.sub (continuousOn_id.pow 2)) continuousOn_const
        intro x hx
        left
        change c ^ 2 - x ^ 2 ≠ 0
        exact ne_of_gt (by nlinarith [hx.1, hx.2, hc])
      exact aestronglyMeasurable_of_continuousOn_Ioo ((hγcont.mul (hk1.sub hk0)).div_const h)
    · -- the dominating bound
      filter_upwards [self_mem_nhdsWithin, hmem] with h hpos hlt
      have h0 : (0:ℝ) < h := hpos
      have hhc : h < c := hlt
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := c))]
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
      change ‖γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h‖ ≤
        M * (6 * c * β) * (c ^ 2 - s ^ 2) ^ (β - 1) + M * (6 * c * β) * (2 * c) ^ (2 * β - 2)
      have hγ : |γ s| ≤ M := hγb s ⟨hs.1, by linarith [hs.2, hc]⟩
      have h1 : |γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h|
          = |γ s| * |(((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h| := by
        rw [mul_div_assoc, abs_mul]
      rw [Real.norm_eq_abs, h1]
      calc |γ s| * |(((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h|
          ≤ M * (6 * c * β * ((c ^ 2 - s ^ 2) ^ (β - 1) + (2 * c) ^ (2 * β - 2))) :=
            mul_le_mul hγ (abs_rpow_sub_div_le hβ hc h0 hhc hs) (abs_nonneg _) hM0
        _ = M * (6 * c * β) * (c ^ 2 - s ^ 2) ^ (β - 1)
            + M * (6 * c * β) * (2 * c) ^ (2 * β - 2) := by
            ring
    · -- integrability of the dominating function
      have hint : Integrable (fun s : ℝ => (c ^ 2 - s ^ 2) ^ (β - 1))
          (volume.restrict (Set.Ioc 0 c)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le).mp
          (intervalIntegrable_csq_sub_sq_rpow hc (by linarith))
      have hcst : Integrable (fun _ : ℝ => (2 * c) ^ (2 * β - 2))
          (volume.restrict (Set.Ioc 0 c)) :=
        integrableOn_const (C := (2 * c) ^ (2 * β - 2))
          (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      exact (hint.const_mul (M * (6 * c * β))).add (hcst.const_mul (M * (6 * c * β)))
    · -- pointwise convergence of the difference quotients (chain rule in `c`)
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := c))]
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
      change Tendsto (fun h : ℝ => γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (γ s * (2 * β * c * (c ^ 2 - s ^ 2) ^ (β - 1))))
      have hpos' : 0 < c ^ 2 - s ^ 2 := by nlinarith [hs.1, hs.2, hc]
      have hK : HasDerivAt (fun x : ℝ => (x^2 - s^2)^β) (2 * β * c * (c^2 - s^2)^(β-1)) c := by
        have hinner : HasDerivAt (fun x : ℝ => x^2 - s^2) (2*c) c := by
          have h := (hasDerivAt_pow 2 c).sub_const (s^2)
          simpa using h
        refine ((Real.hasDerivAt_rpow_const (x := c^2-s^2) (p := β)
          (Or.inl (ne_of_gt hpos'))).comp c hinner).congr_deriv ?_
        ring
      have hslope := hK.tendsto_slope
      have htrans : Tendsto (fun h : ℝ => c + h) (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhdsWithin c (Set.Ioi c)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have hcont : Continuous (fun h : ℝ => c + h) := by fun_prop
          have hh := (hcont.continuousAt (x := 0)).tendsto.mono_left
            (nhdsWithin_le_nhds (s := Set.Ioi 0))
          simpa using hh
        · filter_upwards [self_mem_nhdsWithin] with h hh
          have h0 : (0:ℝ) < h := hh
          change c < c + h
          linarith
      have h2 : Tendsto (fun h : ℝ => slope (fun x : ℝ => (x^2 - s^2)^β) c (c+h))
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (2*β*c*(c^2-s^2)^(β-1))) :=
        (hslope.mono_left (nhdsWithin_mono c (fun x hx => ne_of_gt hx))).comp htrans
      refine Tendsto.congr' ?_ (h2.const_mul (γ s))
      filter_upwards with h
      rw [slope_def_field]
      ring_nf
  rw [show (fun h : ℝ => ∫ s, γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h
        ∂(volume.restrict (Set.Ioc 0 c)))
      = (fun h : ℝ => ∫ s in (0:ℝ)..c,
          γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h) from
        funext (fun h => (intervalIntegral.integral_of_le hc.le).symm)] at hkey
  rw [hval] at hkey
  exact hkey

/-- **The boundary tongue is `o(h)`.**  On `(c, c+h)` the kernel is bounded by
`((c+h)²-c²)^β = (2ch+h²)^β → 0` and `|γ| ≤ M`, so the integral is `≤ M h (2ch+h²)^β`. -/
private lemma tendsto_tail_div {β M c : ℝ} (hβ : 0 < β) (hc : 0 < c) {γ : ℝ → ℝ}
    (hγb : ∀ s ∈ Set.Ioo 0 (2 * c), |γ s| ≤ M) :
    Filter.Tendsto (fun h : ℝ => (∫ s in c..(c + h), γ s * ((c + h) ^ 2 - s ^ 2) ^ β) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (γ c)) (hγb c ⟨hc, by linarith⟩)
  have hmem : Set.Iio c ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    Filter.le_def.mp nhdsWithin_le_nhds (Set.Iio c) (Iio_mem_nhds hc)
  refine squeeze_zero_norm' (a := fun h : ℝ => M * (2*c*h + h^2)^β) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, hmem] with h hpos hlt
    have h0 : (0:ℝ) < h := hpos
    have hhc : h < c := hlt
    have hle : c ≤ c + h := by linarith
    have hbound : ‖∫ s in c..(c+h), γ s * ((c+h)^2 - s^2)^β‖
        ≤ (M * ((c+h)^2 - c^2)^β) * |(c+h) - c| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro s hs
      rw [Set.uIoc_of_le hle] at hs
      have hγ : |γ s| ≤ M := hγb s ⟨by linarith [hs.1], by linarith [hs.2, hhc, hc]⟩
      have hbase : 0 ≤ (c+h)^2 - s^2 := by nlinarith [hs.1, hs.2, h0, hc]
      have hmono : (c+h)^2 - s^2 ≤ (c+h)^2 - c^2 := by nlinarith [hs.1]
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hbase β)]
      calc |γ s| * ((c+h)^2 - s^2)^β ≤ M * ((c+h)^2 - s^2)^β :=
            mul_le_mul_of_nonneg_right hγ (Real.rpow_nonneg hbase β)
        _ ≤ M * ((c+h)^2 - c^2)^β :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase hmono hβ.le) hM0
    have hnorm : ‖(∫ s in c..(c+h), γ s * ((c+h)^2 - s^2)^β)/h‖
        = ‖∫ s in c..(c+h), γ s * ((c+h)^2 - s^2)^β‖ / h := by
      simp only [norm_div, Real.norm_eq_abs, abs_of_pos h0]
    rw [hnorm]
    calc ‖∫ s in c..(c+h), γ s * ((c+h)^2 - s^2)^β‖ / h
        ≤ (M * ((c+h)^2 - c^2)^β * |(c+h) - c|) / h := div_le_div_of_nonneg_right hbound h0.le
      _ = M * ((c+h)^2 - c^2)^β := by
          rw [show |(c+h) - c| = h by rw [abs_of_pos (by linarith : (0:ℝ) < c + h - c)]; ring]
          field_simp
      _ = M * (2*c*h + h^2)^β := by
          rw [show (c+h)^2 - c^2 = 2*c*h + h^2 by ring]
  · have h1 : Tendsto (fun h : ℝ => 2*c*h + h^2) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hcont : Continuous (fun h : ℝ => 2*c*h + h^2) := by fun_prop
      have := (hcont.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have h2 : Tendsto (fun h : ℝ => (2*c*h + h^2)^β) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h3 := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.comp h1
      rw [Real.zero_rpow hβ.ne'] at h3
      exact h3
    simpa using h2.const_mul M

theorem abelTrans_slope_tendsto {β M c : ℝ} (hβ : 0 < β) (hc : 0 < c) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Set.Ioo (0 : ℝ) (2 * c)))
    (hγb : ∀ s ∈ Set.Ioo (0 : ℝ) (2 * c), |γ s| ≤ M) :
    Filter.Tendsto
      (fun h : ℝ => (Work.OddRadon.abelTrans β γ (c + h) - Work.OddRadon.abelTrans β γ c) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c)) := by
  have hmain := abelTrans_diffQuot_tendsto hβ hc hγc hγb
  have htail := tendsto_tail_div hβ hc hγb
  have hsum := hmain.add htail
  rw [add_zero] at hsum
  refine Tendsto.congr' ?_ hsum
  have hmem : Set.Iio c ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    Filter.le_def.mp nhdsWithin_le_nhds (Set.Iio c) (Iio_mem_nhds hc)
  filter_upwards [self_mem_nhdsWithin, hmem] with h hpos hlt
  have h0 : (0:ℝ) < h := hpos
  have hhc : h < c := hlt
  have hle : c ≤ c + h := by linarith
  have hγcont : ContinuousOn γ (Set.Ioo 0 c) :=
    hγc.mono (fun x hx => ⟨hx.1, by linarith [hx.2, hc]⟩)
  have hk1 : ContinuousOn (fun s : ℝ => ((c+h)^2 - s^2)^β) (Set.Ioo 0 c) := by
    apply ContinuousOn.rpow (continuousOn_const.sub (continuousOn_id.pow 2)) continuousOn_const
    intro x hx
    left
    change (c + h) ^ 2 - x ^ 2 ≠ 0
    exact ne_of_gt (by nlinarith [hx.1, hx.2, h0, hc])
  have hk0 : ContinuousOn (fun s : ℝ => (c^2 - s^2)^β) (Set.Ioo 0 c) := by
    apply ContinuousOn.rpow (continuousOn_const.sub (continuousOn_id.pow 2)) continuousOn_const
    intro x hx
    left
    change c ^ 2 - x ^ 2 ≠ 0
    exact ne_of_gt (by nlinarith [hx.1, hx.2, hc])
  have hI1 : IntervalIntegrable (fun s : ℝ => γ s * ((c+h)^2 - s^2)^β) volume (0:ℝ) c := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_bound (C := M * ((c+h)^2)^β) hc
      (hγcont.mul hk1) ?_
    intro s hs
    have hγ : |γ s| ≤ M := hγb s ⟨hs.1, by linarith [hs.2, hc]⟩
    have hbase : 0 ≤ (c+h)^2 - s^2 := by nlinarith [hs.1, hs.2, h0, hc]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hbase β)]
    calc |γ s| * ((c+h)^2 - s^2)^β ≤ M * ((c+h)^2 - s^2)^β :=
          mul_le_mul_of_nonneg_right hγ (Real.rpow_nonneg hbase β)
      _ ≤ M * ((c+h)^2)^β := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase ?_ hβ.le)
            (le_trans (abs_nonneg (γ c)) (hγb c ⟨hc, by linarith⟩))
          nlinarith [hs.1, hs.2, h0]
  have hI0 : IntervalIntegrable (fun s : ℝ => γ s * (c^2 - s^2)^β) volume (0:ℝ) c := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_bound (C := M * (c^2)^β) hc
      (hγcont.mul hk0) ?_
    intro s hs
    have hγ : |γ s| ≤ M := hγb s ⟨hs.1, by linarith [hs.2, hc]⟩
    have hbase : 0 ≤ c^2 - s^2 := by nlinarith [hs.1, hs.2, hc]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hbase β)]
    calc |γ s| * (c^2 - s^2)^β ≤ M * (c^2 - s^2)^β :=
          mul_le_mul_of_nonneg_right hγ (Real.rpow_nonneg hbase β)
      _ ≤ M * (c^2)^β := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase ?_ hβ.le)
            (le_trans (abs_nonneg (γ c)) (hγb c ⟨hc, by linarith⟩))
          nlinarith [hs.1, hs.2, hc]
  have hI2 : IntervalIntegrable (fun s : ℝ => γ s * ((c+h)^2 - s^2)^β) volume c (c+h) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · refine hγc.mono ?_
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      exact ⟨by linarith [hx.1, hc], by linarith [hx.2, hhc, hc]⟩
    · apply ContinuousOn.rpow (continuousOn_const.sub (continuousOn_id.pow 2)) continuousOn_const
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      change (c + h) ^ 2 - x ^ 2 ≠ 0 ∨ 0 < β
      rcases eq_or_lt_of_le hx.2 with hx2 | hx2
      · right; exact hβ
      · left; exact ne_of_gt (by nlinarith [hx.1, hx2])
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hPY : (∫ s in (0:ℝ)..c, γ s*((c+h)^2-s^2)^β) - (∫ s in (0:ℝ)..c, γ s*(c^2-s^2)^β)
      = ∫ s in (0:ℝ)..c, γ s*(((c+h)^2-s^2)^β-(c^2-s^2)^β) := by
    rw [← intervalIntegral.integral_sub hI1 hI0]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  have hdiv : (∫ s in (0:ℝ)..c, γ s*(((c+h)^2-s^2)^β-(c^2-s^2)^β))/h
      = ∫ s in (0:ℝ)..c, γ s*(((c+h)^2-s^2)^β-(c^2-s^2)^β)/h :=
    (intervalIntegral.integral_div h _).symm
  have key1 : (∫ s in (0:ℝ)..(c+h), γ s*((c+h)^2-s^2)^β) - (∫ s in (0:ℝ)..c, γ s*(c^2-s^2)^β)
      = (∫ s in (0:ℝ)..c, γ s*(((c+h)^2-s^2)^β-(c^2-s^2)^β))
        + ∫ s in c..(c+h), γ s*((c+h)^2-s^2)^β := by
    rw [← hsplit]
    linarith [hPY]
  simp only [Work.OddRadon.abelTrans]
  rw [key1, add_div, hdiv]

end

end Work.OddCurve.LowSlope
