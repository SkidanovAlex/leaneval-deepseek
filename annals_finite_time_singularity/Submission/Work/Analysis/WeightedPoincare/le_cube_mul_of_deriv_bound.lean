import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Analysis.WeightedPoincare.sq_deriv_sqrt_le
import Submission.Work.Analysis.WeightedPoincare.intervalIntegral_le_of_integrableOn_Ioo_le
import Submission.Work.Analysis.WeightedPoincare.sq_le_two_div_mul_integral_sq_add_integral_abs_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Analysis.WeightedPoincare

/-! ### Helper -/

/-- On `[z/2, z]` with `0 < z` a nonnegative `f` satisfies `f t ≤ z^4 * (f t / t^4)` pointwise,
hence its integral is bounded by `z^4` times the integral of `f t / t^4`. -/
theorem integral_le_pow4_mul_of_nonneg {f : ℝ → ℝ} {z : ℝ} (hz0 : 0 < z)
    (hnn : ∀ t ∈ Set.Icc (z / 2) z, 0 ≤ f t)
    (h1 : IntervalIntegrable f MeasureTheory.volume (z / 2) z)
    (h2 : IntervalIntegrable (fun t => f t / t ^ 4) MeasureTheory.volume (z / 2) z) :
    ∫ t in (z / 2)..z, f t ≤ z ^ 4 * ∫ t in (z / 2)..z, f t / t ^ 4 := by
  have hle : z / 2 ≤ z := by linarith
  have hpt : ∀ t ∈ Set.Icc (z / 2) z, f t ≤ z ^ 4 * (f t / t ^ 4) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1, hz0]
    have ht4 : 0 < t ^ 4 := by positivity
    have hft : f t = f t / t ^ 4 * t ^ 4 := (div_mul_cancel₀ (f t) (ne_of_gt ht4)).symm
    have hz4 : z ^ 4 * (f t / t ^ 4) = f t / t ^ 4 * z ^ 4 := by ring
    have htz : t ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ (le_of_lt ht0) ht.2 4
    have hnn' : 0 ≤ f t / t ^ 4 := div_nonneg (hnn t ht) (le_of_lt ht4)
    calc f t = f t / t ^ 4 * t ^ 4 := hft
      _ ≤ f t / t ^ 4 * z ^ 4 := mul_le_mul_of_nonneg_left htz hnn'
      _ = z ^ 4 * (f t / t ^ 4) := hz4.symm
  have hmono := intervalIntegral.integral_mono_on hle h1 (h2.const_mul (z ^ 4)) hpt
  rwa [intervalIntegral.integral_const_mul] at hmono

/-! ### Main theorem -/

/-- The local Poincare bound for a `t^{-4}`-weighted energy: if `P ≥ 0` is differentiable on
`(0,1)` with derivative `Pd`, if `P1 ≥ 0` there with `(t * Pd t)^2 ≤ 4 * P t * P1 t` on `(0,1)`,
and if `t ↦ P t / t^4` and `t ↦ P1 t / t^4` are integrable on `(0,1)` with integrals bounded by
`J0` resp. `J1`, then `P z ≤ z^3 * (4 * J0 + J1)` for every `z ∈ (0,1)`. -/
theorem le_cube_mul_of_deriv_bound {P Pd P1 : ℝ → ℝ} {z J0 J1 : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1)
    (hd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt P (Pd t) t)
    (hPnn : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ P t)
    (hP1nn : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ P1 t)
    (hbnd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (t * Pd t) ^ 2 ≤ 4 * P t * P1 t)
    (hint0 : MeasureTheory.IntegrableOn (fun t => P t / t ^ 4) (Set.Ioo (0 : ℝ) 1))
    (hint1 : MeasureTheory.IntegrableOn (fun t => P1 t / t ^ 4) (Set.Ioo (0 : ℝ) 1))
    (hJ0 : ∫ t in Set.Ioo (0 : ℝ) 1, P t / t ^ 4 ≤ J0)
    (hJ1 : ∫ t in Set.Ioo (0 : ℝ) 1, P1 t / t ^ 4 ≤ J1) :
    P z ≤ z ^ 3 * (4 * J0 + J1) := by
  -- elementary interval facts
  have hle : z / 2 ≤ z := by linarith
  have hIoc : Set.Ioc (z / 2) z ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hz1⟩
  have hIcc : Set.Icc (z / 2) z ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hz1⟩
  -- the two `1/t^4`-integrands are nonnegative on `(0,1)`
  have hnn0 : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ P t / t ^ 4 := by
    intro t ht
    have ht4 : 0 < t ^ 4 := by have : 0 < t := ht.1; positivity
    exact div_nonneg (hPnn t ht) (le_of_lt ht4)
  have hnn1 : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ P1 t / t ^ 4 := by
    intro t ht
    have ht4 : 0 < t ^ 4 := by have : 0 < t := ht.1; positivity
    exact div_nonneg (hP1nn t ht) (le_of_lt ht4)
  have hJ0nn : 0 ≤ J0 :=
    le_trans (MeasureTheory.setIntegral_nonneg measurableSet_Ioo hnn0) hJ0
  -- it suffices to prove the bound with `ε` error, for every `ε > 0`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- the regularised square root and its derivative
  let S : ℝ → ℝ := fun t => Real.sqrt (P t + ε)
  let S' : ℝ → ℝ := fun t => Pd t / (2 * Real.sqrt (P t + ε))
  have hpos : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < P t + ε := by
    intro t ht
    have := hPnn t ht
    linarith
  have hPcont : ContinuousOn P (Set.Ioo (0 : ℝ) 1) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hScont : ContinuousOn S (Set.Icc (z / 2) z) :=
    (Real.continuous_sqrt.comp_continuousOn (hPcont.add_const ε)).mono hIcc
  have hSsq : ∀ t ∈ Set.Ioo (0 : ℝ) 1, S t ^ 2 = P t + ε :=
    fun t ht => Real.sq_sqrt (le_of_lt (hpos t ht))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt S (S' t) t := by
    intro t ht
    have h2 : HasDerivAt (fun s => Real.sqrt (P s + ε))
        (Pd t / (2 * Real.sqrt (P t + ε))) t :=
      ((hd t ht).add_const ε).sqrt (ne_of_gt (hpos t ht))
    exact h2
  have hderiv_eq : ∀ t ∈ Set.Ioo (0 : ℝ) 1, deriv S t = S' t :=
    fun t ht => (hderiv t ht).deriv
  have hS'bound : ∀ t ∈ Set.Ioo (0 : ℝ) 1, S' t ^ 2 ≤ P1 t / t ^ 4 * t ^ 2 := by
    intro t ht
    have h := sq_deriv_sqrt_le hε ht.1 (hd t ht) (hPnn t ht) (hP1nn t ht) (hbnd t ht)
    have h1 : deriv (fun s => Real.sqrt (P s + ε)) t = S' t := hderiv_eq t ht
    rwa [h1] at h
  -- integrability ingredients
  have hP0int : IntervalIntegrable (fun t => P t / t ^ 4) MeasureTheory.volume (z / 2) z := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hle]
    exact hint0.mono_set hIoc
  have hP1int : IntervalIntegrable (fun t => P1 t / t ^ 4) MeasureTheory.volume (z / 2) z := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hle]
    exact hint1.mono_set hIoc
  have hPint : IntervalIntegrable P MeasureTheory.volume (z / 2) z := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    exact hPcont.mono hIcc
  have hPeps_int : IntervalIntegrable (fun t => P t + ε) MeasureTheory.volume (z / 2) z := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    exact (hPcont.mono hIcc).add_const ε
  have hPprod_int : IntervalIntegrable (fun t => P1 t / t ^ 4 * t ^ 2)
      MeasureTheory.volume (z / 2) z := by
    have hK : MeasureTheory.IntegrableOn (fun t => P1 t / t ^ 4 * t ^ 2)
        (Set.Icc (z / 2) z) :=
      (hint1.mono_set hIcc).mul_continuousOn (continuous_id.pow 2).continuousOn isCompact_Icc
    rw [intervalIntegrable_iff, Set.uIoc_of_le hle]
    exact hK.mono_set Set.Ioc_subset_Icc_self
  have hGint : IntervalIntegrable (fun t => (P t + ε) + (P1 t / t ^ 4) * t ^ 2 + 1)
      MeasureTheory.volume (z / 2) z := by
    have h3 : IntervalIntegrable (fun t => P1 t / t ^ 4 * t ^ 2 + 1)
        MeasureTheory.volume (z / 2) z :=
      hPprod_int.add intervalIntegrable_const
    have h4 : IntervalIntegrable (fun t => (P t + ε) + (P1 t / t ^ 4 * t ^ 2 + 1))
        MeasureTheory.volume (z / 2) z :=
      hPeps_int.add h3
    simpa only [add_assoc] using h4
  have hSsq_int : IntervalIntegrable (fun t => S t ^ 2) MeasureTheory.volume (z / 2) z := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    exact hScont.pow 2
  -- measurability
  have hSmeas : MeasureTheory.AEStronglyMeasurable S
      (MeasureTheory.volume.restrict (Set.Ioc (z / 2) z)) :=
    (hScont.mono (by intro t ht; exact ⟨le_of_lt ht.1, ht.2⟩)).aestronglyMeasurable
      measurableSet_Ioc
  have hS'meas : MeasureTheory.AEStronglyMeasurable S'
      (MeasureTheory.volume.restrict (Set.Ioc (z / 2) z)) := by
    refine (measurable_deriv S).aestronglyMeasurable.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact hderiv_eq t (hIoc ht)
  -- `S'` is interval integrable (dominated by `(P1 t / t^4) * t^2 + 1`)
  have hS'int : IntervalIntegrable S' MeasureTheory.volume (z / 2) z := by
    refine (hPprod_int.add (intervalIntegrable_const (c := (1 : ℝ)))).mono_fun' ?_ ?_
    · have h : MeasureTheory.AEStronglyMeasurable S'
          (MeasureTheory.volume.restrict (Set.uIoc (z / 2) z)) := by
        rw [Set.uIoc_of_le hle]
        exact hS'meas
      exact h
    · rw [Set.uIoc_of_le hle]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := hIoc ht
      have ht4 : 0 < t ^ 4 := by have : 0 < t := ht'.1; positivity
      have hnn : 0 ≤ P1 t / t ^ 4 * t ^ 2 :=
        mul_nonneg (div_nonneg (hP1nn t ht') (le_of_lt ht4)) (sq_nonneg t)
      have hb := hS'bound t ht'
      have hsqrt : Real.sqrt (P1 t / t ^ 4 * t ^ 2) ≤ (P1 t / t ^ 4 * t ^ 2 + 1) / 2 := by
        have h := two_mul_le_add_sq (Real.sqrt (P1 t / t ^ 4 * t ^ 2)) (1 : ℝ)
        rw [Real.sq_sqrt hnn] at h
        linarith
      rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact le_trans (Real.sqrt_le_sqrt hb) (le_trans hsqrt (by linarith))
  -- `2 * S * S'` and its absolute value are interval integrable (dominated by `G`)
  have hSS'meas : MeasureTheory.AEStronglyMeasurable (fun t => 2 * S t * S' t)
      (MeasureTheory.volume.restrict (Set.Ioc (z / 2) z)) := by
    have h2 : MeasureTheory.AEStronglyMeasurable (fun t => 2 * S t)
        (MeasureTheory.volume.restrict (Set.Ioc (z / 2) z)) := hSmeas.const_mul 2
    have h3 := h2.mul hS'meas
    exact h3
  have hSS'int : IntervalIntegrable (fun t => 2 * S t * S' t) MeasureTheory.volume (z / 2) z := by
    refine hGint.mono_fun' ?_ ?_
    · have h : MeasureTheory.AEStronglyMeasurable (fun t => 2 * S t * S' t)
          (MeasureTheory.volume.restrict (Set.uIoc (z / 2) z)) := by
        rw [Set.uIoc_of_le hle]
        exact hSS'meas
      exact h
    · rw [Set.uIoc_of_le hle]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := hIoc ht
      have hb := hS'bound t ht'
      have hss : 2 * |S t| * |S' t| ≤ S t ^ 2 + S' t ^ 2 := by
        have h := two_mul_le_add_sq |S t| |S' t|
        rw [sq_abs, sq_abs] at h
        exact h
      have hsq := hSsq t ht'
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
  have habsint : IntervalIntegrable (fun t => 2 * |S t * S' t|) MeasureTheory.volume (z / 2) z :=
    hSS'int.abs.congr fun t _ => by
      rw [show (2 : ℝ) * S t * S' t = 2 * (S t * S' t) from by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hS'2_int : IntervalIntegrable (fun t => S' t ^ 2) MeasureTheory.volume (z / 2) z := by
    refine hPprod_int.mono_fun' ?_ ?_
    · have h : MeasureTheory.AEStronglyMeasurable (fun t => S' t ^ 2)
          (MeasureTheory.volume.restrict (Set.uIoc (z / 2) z)) := by
        rw [Set.uIoc_of_le hle]
        exact hS'meas.pow 2
      exact h
    · rw [Set.uIoc_of_le hle]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S' t))]
      exact hS'bound t (hIoc ht)
  -- the averaged increment bound
  have hmain := sq_le_two_div_mul_integral_sq_add_integral_abs_mul hz0 hScont
    (fun t ht => hderiv t ⟨by linarith [ht.1], lt_trans ht.2 hz1⟩) hSS'int habsint hSsq_int
  -- bound on `∫ S^2`
  have hB : ∫ t in (z / 2)..z, S t ^ 2 ≤ z ^ 4 * J0 + ε * (z / 2) := by
    have heq : ∫ t in (z / 2)..z, S t ^ 2 = ∫ t in (z / 2)..z, (P t + ε) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hle] at ht
      exact hSsq t (hIcc ht)
    rw [heq]
    have hsplit : ∫ t in (z / 2)..z, (P t + ε) = (∫ t in (z / 2)..z, P t) + ε * (z / 2) := by
      rw [intervalIntegral.integral_add hPint intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hsplit]
    have hPle : ∫ t in (z / 2)..z, P t ≤ z ^ 4 * ∫ t in (z / 2)..z, P t / t ^ 4 :=
      integral_le_pow4_mul_of_nonneg hz0 (fun t ht => hPnn t (hIcc ht)) hPint hP0int
    have hJ := intervalIntegral_le_of_integrableOn_Ioo_le hz0 hz1 hnn0 hint0 hJ0
    have h4 : z ^ 4 * (∫ t in (z / 2)..z, P t / t ^ 4) ≤ z ^ 4 * J0 :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    linarith
  -- bound on `∫ (S')^2`
  have hS'2_le : ∫ t in (z / 2)..z, S' t ^ 2 ≤ z ^ 2 * J1 := by
    have hpt : ∀ t ∈ Set.Icc (z / 2) z, S' t ^ 2 ≤ z ^ 2 * (P1 t / t ^ 4) := by
      intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := hIcc ht
      have ht4 : 0 < t ^ 4 := by have : 0 < t := ht'.1; positivity
      have hfnn : 0 ≤ P1 t / t ^ 4 := div_nonneg (hP1nn t ht') (le_of_lt ht4)
      have htz : t ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (le_of_lt ht'.1) ht.2 2
      have h2 : P1 t / t ^ 4 * t ^ 2 ≤ z ^ 2 * (P1 t / t ^ 4) := by
        have := mul_le_mul_of_nonneg_left htz hfnn
        linarith
      linarith [hS'bound t ht']
    have hmono := intervalIntegral.integral_mono_on hle hS'2_int (hP1int.const_mul (z ^ 2)) hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    have hJ := intervalIntegral_le_of_integrableOn_Ioo_le hz0 hz1 hnn1 hint1 hJ1
    have h4 : z ^ 2 * (∫ t in (z / 2)..z, P1 t / t ^ 4) ≤ z ^ 2 * J1 :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    linarith
  -- bound on `∫ 2 |S S'|`
  have hptA : ∀ t ∈ Set.Icc (z / 2) z, 2 * |S t * S' t| ≤ (1 / z) * S t ^ 2 + z * S' t ^ 2 := by
    intro t ht
    have h1 : (0 : ℝ) ≤ (|S t| - z * |S' t|) ^ 2 := sq_nonneg _
    have h2 : (|S t| - z * |S' t|) ^ 2
        = S t ^ 2 - 2 * z * (|S t| * |S' t|) + z ^ 2 * S' t ^ 2 := by
      simp only [sub_sq, sq_abs, mul_pow]
      ring
    have h3 : 2 * z * (|S t| * |S' t|) ≤ S t ^ 2 + z ^ 2 * S' t ^ 2 := by linarith
    have h4 : 2 * (|S t| * |S' t|) ≤ (S t ^ 2 + z ^ 2 * S' t ^ 2) / z := by
      rw [le_div_iff₀ hz0]
      linarith
    have h5 : (1 / z) * S t ^ 2 + z * S' t ^ 2 = (S t ^ 2 + z ^ 2 * S' t ^ 2) / z := by
      field_simp
    have h6 : 2 * |S t * S' t| = 2 * (|S t| * |S' t|) := by rw [abs_mul]
    linarith
  have hA : ∫ t in (z / 2)..z, 2 * |S t * S' t| ≤
      (1 / z) * (∫ t in (z / 2)..z, S t ^ 2) + z * (∫ t in (z / 2)..z, S' t ^ 2) := by
    have hgint : IntervalIntegrable (fun t => (1 / z) * S t ^ 2 + z * S' t ^ 2)
        MeasureTheory.volume (z / 2) z :=
      (hSsq_int.const_mul (1 / z)).add (hS'2_int.const_mul z)
    have hmono := intervalIntegral.integral_mono_on hle habsint hgint hptA
    have hsplit : ∫ t in (z / 2)..z, ((1 / z) * S t ^ 2 + z * S' t ^ 2)
        = (1 / z) * (∫ t in (z / 2)..z, S t ^ 2) + z * (∫ t in (z / 2)..z, S' t ^ 2) := by
      rw [intervalIntegral.integral_add (hSsq_int.const_mul (1 / z)) (hS'2_int.const_mul z),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rwa [hsplit] at hmono
  -- arithmetic
  have hzB : (2 / z) * (∫ t in (z / 2)..z, S t ^ 2) ≤ 2 * z ^ 3 * J0 + ε := by
    have h := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 2 / z)
    have he : (2 / z) * (z ^ 4 * J0 + ε * (z / 2)) = 2 * z ^ 3 * J0 + ε := by
      field_simp
    linarith [h, he]
  have hzA : ∫ t in (z / 2)..z, 2 * |S t * S' t| ≤ z ^ 3 * J0 + ε / 2 + z ^ 3 * J1 := by
    have h1 := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 1 / z)
    have h2 := mul_le_mul_of_nonneg_left hS'2_le (le_of_lt hz0)
    have he1 : (1 / z) * (z ^ 4 * J0 + ε * (z / 2)) = z ^ 3 * J0 + ε / 2 := by
      field_simp
    have he2 : z * (z ^ 2 * J1) = z ^ 3 * J1 := by ring
    linarith [hA, h1, h2, he1, he2]
  have hbound : S z ^ 2 ≤ 3 * z ^ 3 * J0 + (3 / 2) * ε + z ^ 3 * J1 := by
    linarith [hmain, hzB, hzA]
  have hSval : S z ^ 2 = P z + ε := hSsq z ⟨hz0, hz1⟩
  have hz3J0 : 0 ≤ z ^ 3 * J0 := mul_nonneg (by positivity) hJ0nn
  linarith [hbound, hSval, hz3J0, hε]

end Work.Analysis.WeightedPoincare
