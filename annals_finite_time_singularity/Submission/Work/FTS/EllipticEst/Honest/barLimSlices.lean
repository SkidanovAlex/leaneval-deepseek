/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slice facts for the honest class at the right endpoint `π/2`

This module collects the elementary `θ`-slice facts about honest data `Hon α F Ψ` that the
"bar-limit" argument (`Work.FTS.EllipticEst.Honest.honestBarLim`) needs:

* `hon_slice_contDiffOn`, `hon_zslice_contDiffOn`: the `θ`-slices and the `z`-slices of `Ψ` are
  smooth on the open intervals (`Hon.sm`);
* `hon_slice_deriv2_integrableOn_Iθ`, `hon_slice_deriv2_integrableOn_Ioo`: the second `θ`-derivative
  of a slice is square-integrable against `σ θ = sin(2θ)^{-η}` (`Hon.memB`), on `Iθ` and on the open
  interval (the difference is a null set);
* `hon_F_sq_integrableOn_Ioo`, `hon_pzIter2_sq_integrableOn_Ioo`: the same for `F` (`Hon.memF`) and
  `z²∂_zzΨ` (`Hon.memA`);
* `hon_Lzero1_slice`: the equation `L₀(u_z) = F + α²z²∂_zzΨ + α(5+α)z∂_zΨ` on the open quadrant;
* `hon_slice_deriv_limit`: for every `z > 0` the derivative of the slice has a finite limit at
  `π/2⁻` (it follows from `∂_θθΨ ∈ L¹`), via the generic one-sided limit lemma
  `exists_tendsto_nhdsWithin_Iio_of_integrableOn_deriv`.  (The slice itself has a finite limit as
  well, and by `HonSliceRightTendsto` that limit is `0`; that fact is not needed here.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `σ θ = sin(2θ)^{-η} ≥ 1` on the open angular interval. -/
theorem one_le_sEta' {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : -(Work.Spaces.eta) ≤ (0 : ℝ) := by
    have := Work.Spaces.eta_pos
    linarith
  have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1 hη
  simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h

/-- The `θ`-slices of honest data are smooth on the open angular interval. -/
theorem hon_slice_contDiffOn {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  intro n
  have hf : ContDiff ℝ n (fun θ : ℝ => (z, θ)) := by fun_prop
  have hcomp := ContDiffOn.comp (f := fun θ : ℝ => (z, θ)) (g := Function.uncurry Ψ)
    (h.sm n) hf.contDiffOn (fun θ hθ => ⟨hz, hθ⟩)
  have heq : (Function.uncurry Ψ ∘ fun θ : ℝ => (z, θ)) = fun θ => Ψ z θ := rfl
  rwa [heq] at hcomp

/-- The `z`-slices of honest data are smooth on `(0,∞)`. -/
theorem hon_zslice_contDiffOn {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun s => Ψ s θ) (Set.Ioi 0) := by
  intro n
  have hf : ContDiff ℝ n (fun s : ℝ => (s, θ)) := by fun_prop
  have hcomp := ContDiffOn.comp (f := fun s : ℝ => (s, θ)) (g := Function.uncurry Ψ)
    (h.sm n) hf.contDiffOn (fun s hs => ⟨hs, hθ⟩)
  have heq : (Function.uncurry Ψ ∘ fun s : ℝ => (s, θ)) = fun s => Ψ s θ := rfl
  rwa [heq] at hcomp

/-- The second `θ`-derivative of a slice is `σ`-square-integrable on `Iθ` (`Hon.memB`). -/
theorem hon_slice_deriv2_integrableOn_Iθ {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have h1 := h.memB.1 z hzI
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => ?_) measurableSet_Icc
    rw [HkIntegrand_zero_eq, sq_profile_eq (Work.Spaces.pthIter 2 Ψ) z θ
      (sin_two_nonneg_of_mem_Iθ hθ)]
    rfl
  have hwz : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwz
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mul_const h2 _
  have h4 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun h3 (fun θ _ => ?_) measurableSet_Icc
    rw [← div_eq_mul_inv, div_eq_iff hw]
    ring
  refine MeasureTheory.IntegrableOn.congr_fun h4 (fun θ _ => ?_) measurableSet_Icc
  rw [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero]
  simp only [Work.Spaces.pth]

/-- The same, restricted to the open angular interval. -/
theorem hon_slice_deriv2_integrableOn_Ioo {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) :=
  (hon_slice_deriv2_integrableOn_Iθ h hz).mono_set
    (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-- `F z ·` is `σ`-square-integrable (`Hon.memF`). -/
theorem hon_F_sq_integrableOn_Ioo {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have h1 := h.memF.1 z hzI
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => ?_) measurableSet_Icc
    rw [HkIntegrand_zero_eq, sq_profile_eq F z θ (sin_two_nonneg_of_mem_Iθ hθ)]
    rfl
  have hwz : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwz
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => ((F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * ((Work.Spaces.w z) ^ 2)⁻¹) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mul_const h2 _
  have h4 : MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun h3 (fun θ _ => ?_) measurableSet_Icc
    rw [← div_eq_mul_inv, div_eq_iff hw]
    ring
  exact h4.mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-- `∂_zzΨ(z,·)` is `σ`-square-integrable (`Hon.memA`). -/
theorem hon_pzIter2_sq_integrableOn_Ioo {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have h1 := h.memA.1 z hzI
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => ?_) measurableSet_Icc
    rw [HkIntegrand_zero_eq, sq_profile_eq (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      z θ (sin_two_nonneg_of_mem_Iθ hθ)]
    rfl
  have hwz : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hzw : z ^ 2 * Work.Spaces.w z ≠ 0 := mul_ne_zero (pow_ne_zero 2 (ne_of_gt hz)) hwz
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) * ((z ^ 2 * Work.Spaces.w z) ^ 2)⁻¹) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mul_const h2 _
  have h4 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun h3 (fun θ _ => ?_) measurableSet_Icc
    rw [← div_eq_mul_inv, div_eq_iff (pow_ne_zero 2 hzw)]
    ring
  exact h4.mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-- **The equation on a slice**, in the form used by the bar-limit argument. -/
theorem hon_Lzero1_slice {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ
      = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + α * (5 + α) * z * Work.Spaces.pz Ψ z θ := by
  have hb := h.eq z hz θ hθ0 hθ1
  rw [Work.Elliptic.bslOp_apply] at hb
  simp only [Work.Elliptic.Lzero] at hb
  have hkey : Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ
      = Work.Elliptic.Lzero Ψ z θ := rfl
  rw [hkey]
  simp only [Work.Elliptic.Lzero]
  nlinarith [hb]

/-- **One-sided limit from an integrable derivative.** -/
theorem exists_tendsto_nhdsWithin_Iio_of_integrableOn_deriv {a b : ℝ} (hab : a < b)
    {f f' : ℝ → ℝ} (hf'm : MeasureTheory.AEStronglyMeasurable f' volume)
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint : MeasureTheory.IntegrableOn f' (Set.Ioc a b)) :
    ∃ L : ℝ, Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds L) := by
  obtain ⟨m, ham, hmb⟩ : ∃ m, a < m ∧ m < b := ⟨(a + b) / 2, by linarith, by linarith⟩
  have hgt : ∀ᶠ x in nhdsWithin b (Set.Iio b), a < x :=
    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hab)
  have htail : Filter.Tendsto (fun x => ∫ t in x..b, f' t)
      (nhdsWithin b (Set.Iio b)) (nhds 0) := by
    have hf'_int : MeasureTheory.Integrable (Set.indicator (Set.Ioc a b) (fun t => ‖f' t‖)) volume := by
      rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
      exact hint.norm
    have key := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := nhdsWithin b (Set.Iio b))
      (F := fun x : ℝ => Set.indicator (Set.Ioc x b) f')
      (f := fun _ => (0 : ℝ))
      (bound := Set.indicator (Set.Ioc a b) (fun t => ‖f' t‖))
      (by filter_upwards with x
          exact hf'm.indicator measurableSet_Ioc)
      (by filter_upwards [hgt] with x hax
          filter_upwards with t
          by_cases ht : t ∈ Set.Ioc x b
          · have ht' : t ∈ Set.Ioc a b := ⟨lt_trans hax ht.1, ht.2⟩
            rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
          · rw [Set.indicator_of_notMem ht, norm_zero]
            exact Set.indicator_nonneg (fun t _ => norm_nonneg (f' t)) t)
      hf'_int
      (by
        have haeb : ∀ᵐ t ∂(volume : MeasureTheory.Measure ℝ), t ≠ b := by
          rw [MeasureTheory.ae_iff]
          simpa using (MeasureTheory.measure_singleton b)
        filter_upwards [haeb] with t htb
        by_cases hbt : t < b
        · have hev : ∀ᶠ x in nhdsWithin b (Set.Iio b), t < x :=
            nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hbt)
          refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
          refine hev.mono (fun x hx => ?_)
          show (0 : ℝ) = (Set.Ioc x b).indicator f' t
          rw [Set.indicator_of_notMem (fun hmem => absurd hmem.1 (not_lt.mpr (le_of_lt hx)))]
        · have htb' : b < t := lt_of_le_of_ne (not_lt.mp hbt) htb.symm
          refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
          refine Filter.Eventually.of_forall (fun x => ?_)
          show (0 : ℝ) = (Set.Ioc x b).indicator f' t
          rw [Set.indicator_of_notMem (fun hmem => absurd hmem.2 (not_le.mpr htb'))])
    rw [MeasureTheory.integral_zero] at key
    refine Filter.Tendsto.congr' ?_ key
    filter_upwards [hgt, self_mem_nhdsWithin] with x hax hxb
    rw [intervalIntegral.integral_of_le (le_of_lt hxb)]
    exact MeasureTheory.integral_indicator measurableSet_Ioc
  refine ⟨f m + ∫ t in m..b, f' t, ?_⟩
  have hdiff : Filter.Tendsto (fun x => (f m + ∫ t in m..b, f' t) - ∫ t in x..b, f' t)
      (nhdsWithin b (Set.Iio b)) (nhds ((f m + ∫ t in m..b, f' t) - 0)) :=
    (tendsto_const_nhds (x := f m + ∫ t in m..b, f' t)).sub htail
  rw [sub_zero] at hdiff
  refine Filter.Tendsto.congr' ?_ hdiff
  have hgtm : ∀ᶠ x in nhdsWithin b (Set.Iio b), m < x :=
    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hmb)
  filter_upwards [hgtm, self_mem_nhdsWithin] with x hmx hxb
  have hcont1 : ContinuousOn f (Set.Ioo a b) :=
    fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
  have hcont : ContinuousOn f (Set.Icc m x) :=
    hcont1.mono (fun y hy => ⟨lt_of_lt_of_le ham hy.1, lt_of_le_of_lt hy.2 hxb⟩)
  have hInt : IntervalIntegrable f' volume m x := by
    rw [intervalIntegrable_iff]
    refine hint.mono_set ?_
    intro t ht
    rw [Set.uIoc_of_le (le_of_lt hmx)] at ht
    exact ⟨lt_trans ham ht.1, le_trans ht.2 (le_of_lt hxb)⟩
  have hFTC : ∫ t in m..x, f' t = f x - f m :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hmx) hcont
      (fun y hy => hderiv y ⟨lt_trans ham hy.1, lt_trans hy.2 hxb⟩) hInt
  have hIx : IntervalIntegrable f' volume x b := by
    rw [intervalIntegrable_iff]
    refine hint.mono_set ?_
    intro t ht
    rw [Set.uIoc_of_le (le_of_lt hxb)] at ht
    exact ⟨lt_trans (lt_trans ham hmx) ht.1, ht.2⟩
  have hadd : (∫ t in m..b, f' t) = (∫ t in m..x, f' t) + (∫ t in x..b, f' t) :=
    (intervalIntegral.integral_add_adjacent_intervals hInt hIx).symm
  rw [hadd, hFTC]
  ring

/-- `∂_θθΨ(z,·) ∈ L¹` on `Ioc 0 (π/2)`. -/
theorem hon_slice_deriv2_integrableOn_Ioc {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
      (Set.Ioc 0 (Real.pi / 2)) := by
  have hIoo := hon_slice_deriv2_integrableOn_Ioo h hz
  have hsq : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine hIoo.mono' ((measurable_deriv _).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta' hθ
    nlinarith [sq_nonneg (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ), h1,
      mul_nonneg (sq_nonneg (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)) (by linarith : (0:ℝ) ≤ Work.FTS.EllipticEst.sEta θ)]
  have habs : MeasureTheory.IntegrableOn
      (fun θ => |deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hmaj : MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2 + 1)
        (Set.Ioo 0 (Real.pi / 2)) :=
      hsq.add (MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := Set.Ioo 0 (Real.pi / 2))
        (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
    refine hmaj.mono' (by simpa only [Real.norm_eq_abs] using
      (measurable_deriv (fun t => deriv (fun θ' => Ψ z θ') t)).aestronglyMeasurable.norm) ?_
    filter_upwards with θ
    have h1 : |deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ|
        ≤ (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ| - 1 / 2),
        sq_abs (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ),
        abs_nonneg (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)]
    simpa only [Real.norm_eq_abs, abs_abs] using h1
  have hmeas : Set.Ioo 0 (Real.pi / 2) =ᵐ[volume] Set.Ioc 0 (Real.pi / 2) := by
    have hnull : volume ({(Real.pi / 2 : ℝ)} : Set ℝ) = 0 := MeasureTheory.measure_singleton _
    have hpair : ∀ᵐ x : ℝ, x ∉ ({(Real.pi / 2 : ℝ)} : Set ℝ) := by
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    filter_upwards [hpair] with x hx
    refine propext ⟨fun h1 => ⟨h1.1, le_of_lt h1.2⟩, fun h1 =>
      ⟨h1.1, lt_of_le_of_ne h1.2 hx⟩⟩
  have habs_Ioc : MeasureTheory.IntegrableOn
      (fun θ => |deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ|) (Set.Ioc 0 (Real.pi / 2)) := by
    change MeasureTheory.Integrable (fun θ => |deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ|)
      (volume.restrict (Set.Ioc 0 (Real.pi / 2)))
    rw [← MeasureTheory.Measure.restrict_congr_set hmeas]
    exact habs
  exact habs_Ioc.mono' (measurable_deriv _).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun θ => le_of_eq (Real.norm_eq_abs _)))

/-- **The derivative of the slice has a finite limit at `π/2⁻`.** -/
theorem hon_slice_deriv_limit {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    ∃ L : ℝ, Filter.Tendsto (fun θ => deriv (fun θ' => Ψ z θ') θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L) := by
  have hsm := hon_slice_contDiffOn h hz
  refine exists_tendsto_nhdsWithin_Iio_of_integrableOn_deriv (a := 0) (b := Real.pi / 2)
    Real.pi_div_two_pos (measurable_deriv _).aestronglyMeasurable ?_
    (hon_slice_deriv2_integrableOn_Ioc h hz)
  intro x hx
  have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact ((h1.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioo.mem_nhds hx)).hasDerivAt

end Work.FTS.EllipticEst.Honest
