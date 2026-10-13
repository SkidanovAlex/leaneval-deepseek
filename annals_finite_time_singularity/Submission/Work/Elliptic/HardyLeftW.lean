import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Gbar_hardy_lintegral_ofReal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open scoped ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary algebraic facts about the weight `w` on `(0,1)` -/

private lemma w_sq_eq (z : ℝ) (_hz : z ≠ 0) :
    (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w, div_pow]
  ring

private lemma one_le_one_add_pow_four {z : ℝ} (hz : 0 ≤ z) : (1 : ℝ) ≤ (1 + z) ^ 4 := by
  have h0 : 0 ≤ 1 + z := by linarith
  calc (1 : ℝ) = 1 ^ 4 := by norm_num
    _ ≤ (1 + z) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4

private lemma w_sq_le_inv_four (z : ℝ) (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    (Work.Spaces.w z) ^ 2 ≤ 16 * z ^ (-(4 : ℝ)) := by
  have hz0 : 0 < z := hz.1
  have h4 : (1 + z) ^ 4 ≤ 16 := by
    have h0 : 0 ≤ 1 + z := by linarith
    calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 (by linarith [hz.2]) 4
      _ = 16 := by norm_num
  have hz4 : 0 < z ^ 4 := by positivity
  have hrw : z ^ (-(4 : ℝ)) = (z ^ 4)⁻¹ := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (le_of_lt hz0), Real.rpow_natCast]
  rw [w_sq_eq z (ne_of_gt hz0), hrw, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right h4 (le_of_lt hz4)

private lemma inv_four_le_w_sq (z : ℝ) (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    z ^ (-(4 : ℝ)) ≤ (Work.Spaces.w z) ^ 2 := by
  have hz0 : 0 < z := hz.1
  have h1 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_one_add_pow_four (le_of_lt hz0)
  have hz4 : 0 < z ^ 4 := by positivity
  have hrw : z ^ (-(4 : ℝ)) = (z ^ 4)⁻¹ := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (le_of_lt hz0), Real.rpow_natCast]
  rw [hrw, inv_eq_one_div, w_sq_eq z (ne_of_gt hz0)]
  exact div_le_div_of_nonneg_right h1 (le_of_lt hz4)

/-- The source localised to `(0,1)`: `z ↦ 1_{(0,1)}(z)·f z / z²`. -/
private def FL (f : ℝ → ℝ) (z : ℝ) : ℝ := (Set.Ioo (0 : ℝ) 1).indicator f z / z ^ 2

/-! ## Measurability and integrability of `f` and of `f t / t` -/

/-- On `(0,1)` one has `f t = -(deriv U t) · t`; this is the measurability source for `f`. -/
private lemma f_eq_slope {f U : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = -(deriv U t) * t := by
  intro t ht
  have h1 : f t / t = -(deriv U t) := by
    have h := (hderiv t ht).deriv
    rw [h]; ring
  exact (div_eq_iff (ne_of_gt ht.1)).mp h1

private lemma aesm_f {f U : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z) :
    AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have hfm : Measurable (fun t : ℝ => -(deriv U t) * t) :=
    ((measurable_deriv U).neg).mul measurable_id
  refine hfm.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (f_eq_slope hderiv t ht).symm

/-- `f t / t` is integrable on `(0,1)`: it is dominated by `((f t)² w t² + 1)/2`. -/
private lemma integrable_div_self {f U : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z)
    (hint : IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo (0 : ℝ) 1)) :
    IntegrableOn (fun t : ℝ => f t / t) (Set.Ioo (0 : ℝ) 1) := by
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) 1)) := aesm_f hderiv
  have hgmeas : AEStronglyMeasurable (fun t : ℝ => f t / t)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    hfmeas.mul measurable_id.inv.aestronglyMeasurable
  have hM : Integrable (fun t : ℝ => ((f t) ^ 2 * (Work.Spaces.w t) ^ 2 + 1) / 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have h1 : Integrable (fun t : ℝ => (f t) ^ 2 * (Work.Spaces.w t) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hint
    have h2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    exact (h1.add h2).div_const 2
  refine Integrable.mono' hM hgmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := ht.1
  have hb : (f t / t) ^ 2 ≤ (f t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
    have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    have ht4 : (0 : ℝ) < t ^ 4 := by positivity
    have hkey : (1 : ℝ) / t ^ 2 ≤ (Work.Spaces.w t) ^ 2 := by
      rw [w_sq_eq t (ne_of_gt ht0), div_le_div_iff₀ ht2 ht4]
      have h1 : (1 : ℝ) ≤ (1 + t) ^ 4 := one_le_one_add_pow_four (le_of_lt ht0)
      have h2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      nlinarith
    calc (f t / t) ^ 2 = (f t) ^ 2 * ((1 : ℝ) / t ^ 2) := by rw [div_pow]; ring
      _ ≤ (f t) ^ 2 * (Work.Spaces.w t) ^ 2 := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
  rw [Real.norm_eq_abs]
  have h1 : 2 * |f t / t| ≤ (f t / t) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|f t / t| - 1), sq_abs (f t / t), abs_nonneg (f t / t)]
  linarith

/-- The fundamental theorem of calculus for `U`: `U z = -∫_0^z f t / t dt` on `(0,1)`. -/
private lemma ftc_U {f U : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z)
    (hcont : ContinuousOn U (Set.Icc 0 1)) (h0 : U 0 = 0)
    (hdiv : IntegrableOn (fun t : ℝ => f t / t) (Set.Ioo (0 : ℝ) 1)) :
    ∀ z ∈ Set.Ioo (0 : ℝ) 1, U z = -∫ t in (0 : ℝ)..z, f t / t := by
  intro z hz
  have hz0 : 0 < z := hz.1
  have hsub : Set.Ioc (0 : ℝ) z ⊆ Set.Ioo (0 : ℝ) 1 :=
    fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hz.2⟩
  have hint : IntervalIntegrable (fun t : ℝ => -(f t / t)) volume 0 z :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hz0.le).mpr (hdiv.mono_set hsub)).neg
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) z, HasDerivAt U (-(f x / x)) x :=
    fun x hx => hderiv x ⟨hx.1, lt_trans hx.2 hz.2⟩
  have hccc : ContinuousOn U (Set.Icc 0 z) :=
    hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 (le_of_lt hz.2)⟩)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz0.le hccc hder hint
  rw [intervalIntegral.integral_neg, h0, sub_zero] at h
  linarith [h]

/-! ## Integrability of the localised source -/

private lemma integrable_FL_sq {f U : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z)
    (hint : IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo (0 : ℝ) 1)) :
    IntegrableOn (fun z : ℝ => FL f z ^ 2) (Set.Ioi 0) := by
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) 1)) := aesm_f hderiv
  have hmeas : AEStronglyMeasurable (fun z : ℝ => (f z / z ^ 2) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ => ((z ^ 2)⁻¹ : ℝ))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      (measurable_id.pow_const 2).inv.aestronglyMeasurable
    exact (hfmeas.mul h1).pow 2
  have h1 : IntegrableOn (fun z : ℝ => (f z / z ^ 2) ^ 2) (Set.Ioo (0 : ℝ) 1) := by
    refine Integrable.mono' hint hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hz0 : 0 < z := hz.1
    have hbn : ‖(f z / z ^ 2) ^ 2‖ = (f z / z ^ 2) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hbn, div_pow]
    have hz4 : (0 : ℝ) < (z ^ 2) ^ 2 := by positivity
    have hkey : (1 : ℝ) / (z ^ 2) ^ 2 ≤ (Work.Spaces.w z) ^ 2 := by
      have h1 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_one_add_pow_four (le_of_lt hz0)
      have hzz : (z ^ 2) ^ 2 = z ^ 4 := by ring
      have hz4 : (0 : ℝ) < z ^ 4 := by positivity
      rw [hzz, w_sq_eq z (ne_of_gt hz0)]
      exact div_le_div_of_nonneg_right h1 hz4.le
    calc (f z) ^ 2 / (z ^ 2) ^ 2 = (f z) ^ 2 * ((1 : ℝ) / (z ^ 2) ^ 2) := by ring
      _ ≤ (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
  have h2 : Integrable ((Set.Ioo (0 : ℝ) 1).indicator (fun z : ℝ => (f z / z ^ 2) ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr h1
  have h3 : (fun z : ℝ => FL f z ^ 2)
      = (Set.Ioo (0 : ℝ) 1).indicator (fun z : ℝ => (f z / z ^ 2) ^ 2) := by
    funext z
    by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
    · simp only [FL, Set.indicator_of_mem hz]
    · simp only [FL, Set.indicator_of_notMem hz]
      simp
  rw [h3]
  exact h2.integrableOn

/-! ## The main theorem -/

/-- Weighted Hardy inequality on the left half-line: for `U` continuous on `[0,1]` with `U 0 = 0` and derivative `-(f z / z)` on `(0,1)`, and `f²w²` integrable on `(0,1)`, one has `U²w²` integrable on `(0,1)` with `∫_{(0,1)} U²w² ≤ 107 ∫_{(0,1)} f²w²`. Here `w z = (1+z)²/z²` is `Work.Spaces.w`. Intended route: `U z = -∫_0^z f t/t dt`, then `w² ≤ 16 z^{-4}` on `(0,1)`, the weighted Hardy inequality `∫ U²/z⁴ ≤ (2/3)∫ U'²/z²`, and `z^{-4} ≤ w²`; this gives the constant `32/3 ≤ 107`. -/
theorem HardyLeftW (f U : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt U (-(f z / z)) z)
    (hcont : ContinuousOn U (Set.Icc 0 1)) (h0 : U 0 = 0)
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (U z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioo 0 1) ∧
      ∫ z in Set.Ioo (0 : ℝ) 1, (U z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ 107 * ∫ z in Set.Ioo (0 : ℝ) 1, (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  set J : ℝ := ∫ z in Set.Ioo (0 : ℝ) 1, (f z) ^ 2 * (Work.Spaces.w z) ^ 2 with hJ
  have hJnn : 0 ≤ J := integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdiv : IntegrableOn (fun t : ℝ => f t / t) (Set.Ioo (0 : ℝ) 1) :=
    integrable_div_self hderiv hint
  have hftc := ftc_U hderiv hcont h0 hdiv
  have hFLsq : IntegrableOn (fun z : ℝ => FL f z ^ 2) (Set.Ioi 0) := integrable_FL_sq hderiv hint
  have hlib := Gbar_hardy_lintegral_ofReal 2 (by norm_num) (FL f) hFLsq
  -- Step 0: pointwise identification of the two integrands on `(0,1)`.
  have hA : ∀ᵐ z ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      ENNReal.ofReal ((z ^ (-(2 : ℝ)) * ∫ s in (0 : ℝ)..z, s ^ ((2 : ℝ) - 1) * FL f s) ^ 2)
        = ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hz0 : 0 < z := hz.1
    have key : ∫ s in (0 : ℝ)..z, s ^ ((2 : ℝ) - 1) * FL f s = -U z := by
      have e1 : ∫ s in (0 : ℝ)..z, s ^ ((2 : ℝ) - 1) * FL f s
          = ∫ s in (0 : ℝ)..z, f s / s := by
        rw [intervalIntegral.integral_of_le hz0.le, intervalIntegral.integral_of_le hz0.le]
        refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
        have hs1 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs.1, lt_of_le_of_lt hs.2 hz.2⟩
        simp only [FL, Set.indicator_of_mem hs1, show (2 : ℝ) - 1 = 1 by norm_num,
          Real.rpow_one]
        field_simp
      rw [e1, hftc z hz]
      ring
    have key2 : (z ^ (-(2 : ℝ)) * (-U z)) ^ 2 = (U z) ^ 2 * z ^ (-(4 : ℝ)) := by
      have h1 : (z ^ (-(2 : ℝ))) ^ 2 = z ^ (-(4 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hz0)]
        congr 1
        norm_num
      rw [mul_neg, neg_sq, mul_pow, h1]
      ring
    rw [key, key2]
  -- Step 1: `w² ≤ 16 z^{-4}` on `(0,1)`.
  have step1 : ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 16 * ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) := by
    have h16 : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ 16 * ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) := by
      intro z hz
      have hle : (U z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ 16 * ((U z) ^ 2 * z ^ (-(4 : ℝ))) := by
        have h1 := w_sq_le_inv_four z hz
        have h2 : (0 : ℝ) ≤ (U z) ^ 2 := sq_nonneg _
        nlinarith [h1, h2]
      calc ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ ENNReal.ofReal (16 * ((U z) ^ 2 * z ^ (-(4 : ℝ)))) := ENNReal.ofReal_le_ofReal hle
        _ = 16 * ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
            norm_num
    calc ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫⁻ z in Set.Ioo (0 : ℝ) 1,
            16 * ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) :=
          setLIntegral_mono' measurableSet_Ioo h16
      _ = 16 * ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ))) :=
          lintegral_const_mul' 16 _ (by norm_num)
  -- Step 2: the localised Hardy inequality (proved in the workspace).
  have step2 : ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * z ^ (-(4 : ℝ)))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((z ^ (-(2 : ℝ)) * ∫ s in (0 : ℝ)..z, s ^ ((2 : ℝ) - 1) * FL f s) ^ 2) := by
    rw [← lintegral_congr_ae hA]
    exact lintegral_mono_set Ioo_subset_Ioi_self
  -- The comparison of the sources.
  have hFLint : ∫ z in Set.Ioi (0 : ℝ), FL f z ^ 2 ≤ J := by
    have h_eq : (fun z : ℝ => FL f z ^ 2)
        = (Set.Ioo (0 : ℝ) 1).indicator (fun z : ℝ => (f z / z ^ 2) ^ 2) := by
      funext z
      by_cases hz : z ∈ Set.Ioo (0 : ℝ) 1
      · simp only [FL, Set.indicator_of_mem hz]
      · simp only [FL, Set.indicator_of_notMem hz]
        simp
    rw [h_eq, integral_indicator measurableSet_Ioo]
    rw [Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.mpr Ioo_subset_Ioi_self]
    have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        (f z / z ^ 2) ^ 2 ≤ (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hz0 : 0 < z := hz.1
      have hz4 : (0 : ℝ) < (z ^ 2) ^ 2 := by positivity
      have hkey : (1 : ℝ) / (z ^ 2) ^ 2 ≤ (Work.Spaces.w z) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_one_add_pow_four (le_of_lt hz0)
        have hzz : (z ^ 2) ^ 2 = z ^ 4 := by ring
        have hz4 : (0 : ℝ) < z ^ 4 := by positivity
        rw [hzz, w_sq_eq z (ne_of_gt hz0)]
        exact div_le_div_of_nonneg_right h1 hz4.le
      calc (f z / z ^ 2) ^ 2 = (f z) ^ 2 * ((1 : ℝ) / (z ^ 2) ^ 2) := by rw [div_pow]; ring
        _ ≤ (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    exact integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg (f z / z ^ 2)) hint hpt
  -- Step 3: assemble.
  have hconst : 4 / (2 * (3 * 2 - 2) : ℝ) = 1 / 2 := by norm_num
  have hmain : ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ENNReal.ofReal (107 * J) := by
    refine (step1.trans (mul_le_mul_of_nonneg_left (step2.trans hlib) (by norm_num))).trans ?_
    rw [show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hconst]
    linarith [hFLint, hJnn]
  -- Measurability of the integrand and the final conversions.
  have hUcont : ContinuousOn U (Set.Ioo (0 : ℝ) 1) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hw2meas : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
    have h1 : Measurable (fun z : ℝ => ((1 + z) ^ 2 : ℝ)) :=
      (measurable_const.add measurable_id).pow_const 2
    have h2 : Measurable (fun z : ℝ => ((z ^ 2)⁻¹ : ℝ)) := (measurable_id.pow_const 2).inv
    have h3 : Measurable (fun z : ℝ => ((1 + z) ^ 2 : ℝ) * (z ^ 2)⁻¹) := h1.mul h2
    have h4 : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = (fun z : ℝ => (((1 + z) ^ 2 : ℝ) * (z ^ 2)⁻¹) ^ 2) := by
      funext z
      rw [Work.Spaces.w, div_eq_mul_inv]
    rw [h4]
    exact h3.pow_const 2
  have hUmeas : AEStronglyMeasurable (fun z : ℝ => (U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ((hUcont.pow 2).aestronglyMeasurable measurableSet_Ioo).mul hw2meas.aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
      (fun z : ℝ => (U z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfin : ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≠ ∞ := ne_top_of_lt (lt_of_le_of_lt hmain ENNReal.ofReal_lt_top)
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hUmeas hnn).mp hfin, ?_⟩
  have hconv : ∫ z in Set.Ioo (0 : ℝ) 1, (U z) ^ 2 * (Work.Spaces.w z) ^ 2
      = (∫⁻ z in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnn hUmeas
  rw [hconv]
  calc (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((U z) ^ 2 * (Work.Spaces.w z) ^ 2)).toReal
      ≤ (ENNReal.ofReal (107 * J)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = 107 * J := ENNReal.toReal_ofReal (by linarith)

end

end Work.Elliptic
