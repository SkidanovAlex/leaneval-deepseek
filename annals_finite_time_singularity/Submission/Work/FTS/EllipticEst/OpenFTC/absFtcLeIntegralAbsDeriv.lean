import Mathlib
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
-- ===== merged: Submission.Work.Analysis.WeightedPoincare.le_cube_mul_of_deriv_bound =====
section

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
end
-- ===== merged: Submission.Work.Blocks.HkMem_of_majorant_aesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

/-
**`HkMem` from a pointwise majorant, with only a.e. strong measurability.**

`Work.Spaces.HkMem α k f` is the pair of *honesty* requirements on the iterated `H^k`-integral
of `f`: every angular slice `θ ↦ HkIntegrand α k f z θ` (`z ∈ Iz`) is integrable on `Iθ`, and
`z ↦ ∫_θ HkIntegrand α k f z θ` is integrable on `Iz`.

If a majorant `M` of the integrand is known to have integrable slices `M z ·` on `Iθ` and an
integrable `θ`-integral `z ↦ ∫_θ M z θ` on `Iz`, then `HkMem α k f` follows as soon as the
integrand is measurable where it matters: a.e.-strongly-measurable on each slice (for the
`Integrable.mono'` step) and its `θ`-integral a.e.-strongly-measurable on `Iz` (for the outer
step).  The two measurability hypotheses are *not* derivable from a pointwise bound alone, so
they are carried explicitly; the domination hypothesis is pointwise on the closed quadrant, and
is converted to an a.e. statement with respect to the restricted measures by
`ae_restrict_of_forall_mem`.

The only structural input about `HkIntegrand` is its nonnegativity
(`Work.Spaces.HkIntegrand_nonneg`), which turns the pointwise bound into a bound on the norms
(as required by `Integrable.mono'`) and makes the `θ`-integral nonnegative, so that its absolute
value is bounded by `∫_θ M z θ`.
-/
theorem HkMem_of_majorant_aesm (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (houter : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  constructor
  · -- every angular slice of the integrand is integrable on `Iθ`
    intro z hz
    refine Integrable.mono' (hMslice z hz) (hslice z hz) ?_
    filter_upwards [ae_restrict_of_forall_mem hmesθ (fun θ hθ => hle z hz θ hθ)]
      with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
    exact hθ
  · -- the `z`-integral of the angular slices is integrable on `Iz`
    refine Integrable.mono' hMz houter ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
      (hMslice z hz)
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hle z hz θ hθ))

end Work.Blocks
end
-- ===== merged: Submission.Work.Blocks.interp_amgm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Blocks

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The AM–GM and coefficient lemmas of the box assembly

The arithmetic core of the compact case of the two-dimensional mixed weighted interpolation
(`Work.Blocks.interp_mixed_compact_clean`).  After the per-slice estimate
(`Work.Blocks.interp_slice_DzG`) has been integrated against `w²` and the `z`-integral of
`J(z) = -∫_θ D_zG·∂_θ²(D_zG)σ` has been converted by the radial integration by parts
(`Work.Blocks.interp_z_ibp_clean`, side conditions `Work.Blocks.slice_Dz_support`,
`slice_pthIter2_support`, `slice_z_contDiffOn_one`) plus the Fubini swap
(`Work.Blocks.interp_swap_clean`) into the pairing `∫_θ(∫_z w² X Y)σ` with

  `X = D_z²G + b·D_zG`,   `b z = (z-3)/(1+z)`,   `Y = ∂_θ²G`,   `σ = sin(2θ)^{-η}`,

the estimate is closed by the two pointwise facts proved here:

* `abs_mul_le_alpha_sq`: `|X·Y| ≤ α²X² + Y²/(4α²)` (so `∫∫w²|X||Y|σ ≤ α²∫∫w²X²σ + (1/(4α²))∫∫w²Y²σ`);
* `sq_add_b_mul_sq_le`: `(X + b·Y)² ≤ 2X² + 18Y²` for `|b| ≤ 3` (so `∫∫w²X²σ ≤ 2 ddInt G + 18 dInt G`),

together with `abs_bcoef_le`: `|(z-3)/(1+z)| ≤ 3` for `z ≥ 0`.  Multiplying the resulting
inequality by `((1+η)/(1-η))` and using `α ≤ 1/4` (so that `α² ≤ α⁴/α²·const`, `1/(4α²) ≤ const/α⁴`
and `α² ≤ const`) produces the box statement `α² mixInt G ≤ C(α⁴ ddInt G + ttInt G + α² dInt G)`
of `Work.Blocks.interp_mixed_compact_clean`.
-/


/-- `(X + b·Y)² ≤ 2X² + 18Y²` for `|b| ≤ 3` — the coefficient estimate for `X = D_z²G + b·D_zG`. -/
theorem sq_add_b_mul_sq_le {X Y b : ℝ} (hb : |b| ≤ 3) :
    (X + b * Y) ^ 2 ≤ 2 * X ^ 2 + 18 * Y ^ 2 := by
  have h1 : (X + b * Y) ^ 2 ≤ 2 * X ^ 2 + 2 * (b * Y) ^ 2 := by
    nlinarith [sq_nonneg (X - b * Y)]
  have hb2 : b ^ 2 ≤ 9 := by
    have := abs_le.mp hb
    nlinarith [this.1, this.2]
  have h2 : (b * Y) ^ 2 ≤ 9 * Y ^ 2 := by
    rw [mul_pow]
    nlinarith [sq_nonneg Y]
  linarith

/-- The coefficient `b z = (z-3)/(1+z)` of the radial integration by parts is bounded by `3`
on the half-line `z ≥ 0`. -/
theorem abs_bcoef_le (z : ℝ) (hz : 0 ≤ z) : |(z - 3) / (1 + z)| ≤ 3 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos h1, div_le_iff₀ h1]
  have h2 : |z - 3| ≤ z + 3 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith

end

end Work.Blocks
end
-- ===== merged: Submission.Work.Blocks.interp_swap_clean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks





end Work.Blocks
end
end
-- ===== merged: Submission.Work.ChiExplicit.chi_antitoneOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.ChiExplicit.chi` is antitone on `[0, ∞)`

The explicit cut-off is `chi x = Real.smoothTransition (2 - |x|)`.  On the positive half-line
`|x| = x`, so `chi x = smoothTransition (2 - x)`: a *monotone* function (`smoothTransition.monotone`)
composed with the *antitone* map `x ↦ 2 - x`.  Hence `chi` is antitone on `[0, ∞)`.

This is the weak form of "the cut-off decreases in the radius": it combines with the flat parts
(`chi = 1` for `|x| ≤ 1`, `chi = 0` for `|x| ≥ 2`) to give the whole monotonicity of `chi` in `|x|`
on the annulus `1 ≤ |x| ≤ 2` where the cut-off is actually used.

The proof only needs the definitional reduction `chi_apply_abs` and `Real.smoothTransition.monotone`.
-/

open Set

namespace Work.ChiExplicit

/-- **The explicit cut-off is antitone on the non-negative half-line.**
For `0 ≤ x ≤ y`, `chi y ≤ chi x`: both are `smoothTransition` applied to `2 - x ≥ 2 - y`, and
`smoothTransition` is monotone. -/
theorem chi_antitoneOn : AntitoneOn Work.ChiExplicit.chi (Set.Ici (0:ℝ)) := by
  intro x hx y hy hxy
  rw [chi_apply_abs, chi_apply_abs, abs_of_nonneg hy, abs_of_nonneg hx]
  exact Real.smoothTransition.monotone (by linarith)

end Work.ChiExplicit
end
-- ===== merged: Submission.Work.ChiExplicit.chi_contDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set

namespace Work.ChiExplicit

/-- **`chi` is `C^n` for every `n`.**  The argument `x ↦ 2 - ‖x‖` is not differentiable at `0`, but
the singularity is harmless: on the open half-lines `x > 0` and `x < 0` the function agrees with
`Real.smoothTransition (2 - x)` resp. `Real.smoothTransition (2 + x)`, both smooth, while on the
neighbourhood `(-1, 1)` of the origin it is the constant `1`.  These three open sets cover `ℝ`. -/
theorem chi_contDiff (n : ℕ∞) : ContDiff ℝ n Work.ChiExplicit.chi := by
  -- On `x > 0`, `chi x = smoothTransition (2 - x)`.
  have hpos : ContDiffOn ℝ n chi (Ioi (0 : ℝ)) := by
    have h : ContDiffOn ℝ n (fun x => Real.smoothTransition (2 - x)) (Ioi (0 : ℝ)) :=
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).contDiffOn
    exact h.congr (fun x hx => by rw [chi_apply_abs, abs_of_pos hx])
  -- On `x < 0`, `chi x = smoothTransition (2 + x)`.
  have hneg : ContDiffOn ℝ n chi (Iio (0 : ℝ)) := by
    have h : ContDiffOn ℝ n (fun x => Real.smoothTransition (2 + x)) (Iio (0 : ℝ)) :=
      (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id)).contDiffOn
    exact h.congr (fun x hx => by rw [chi_apply_abs, abs_of_neg hx]; ring_nf)
  -- On `(-1, 1)`, `chi` is the constant `1`.
  have hzero : ContDiffOn ℝ n chi (Ioo (-1 : ℝ) 1) :=
    contDiffOn_const.congr (fun x hx => by
      rw [chi_eq_one (le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩))])
  -- The three open sets cover `ℝ`.
  have h12 : ContDiffOn ℝ n chi (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) :=
    hpos.union_of_isOpen hneg isOpen_Ioi isOpen_Iio
  have h3 : ContDiffOn ℝ n chi ((Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) ∪ Ioo (-1 : ℝ) 1) :=
    h12.union_of_isOpen hzero (isOpen_Ioi.union isOpen_Iio) isOpen_Ioo
  rw [show (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) ∪ Ioo (-1 : ℝ) 1 = univ from ?_] at h3
  · exact contDiffOn_univ.mp h3
  · ext x; simp only [mem_union, mem_Ioi, mem_Iio, mem_Ioo, mem_univ]
    constructor
    · intro _; trivial
    · intro _
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨by linarith, by linarith⟩
      · exact Or.inl (Or.inl h)

end Work.ChiExplicit
end
-- ===== merged: Submission.Work.Coercivity.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The linearized operators -/

/-- The paper's operator `L₁₂` applied to a function of `(z,θ)`; the result is a
function of the radial variable `z` alone.  With `Work.Spaces.K θ = 3 sin θ cos²θ`,
this is `L₁₂(f)(z) = ∫_z^∞ ∫_0^{π/2} K(θ') f(s,θ')/s dθ' ds`. -/
def L12f (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => FM.L12 Spaces.K f z

/-- `𝓛(f) = f + z ∂_z f - 2 f/(1+z)`. -/
def L (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ + Spaces.Dz f z θ - 2 * f z θ / (1 + z)

/-- `𝓛_Γ(f) = 𝓛(f) - (2 z Γ(θ)/(c(1+z)²)) L₁₂(f)`. -/
def LGamma (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => L f z θ - (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z

/-- `𝕡(f)(z,θ) = f(z,θ) - (Γ(θ)/c) (2 z²/(1+z)³) L₁₂(f)(0)`. -/
def Proj (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ - (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * L12f f 0

/-- The angular transport term `3 sin(2θ) ∂_θ f /(1+z) = 3 D_θ f/(1+z)`. -/
def Transport (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => 3 * Spaces.Dth f z θ / (1 + z)

/-- `𝓛_Γ^T(f) = 𝓛_Γ(f) - 𝕡(3 sin(2θ) ∂_θ f/(1+z))`. -/
def LGammaT (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => LGamma α f z θ - Proj α (Transport f) z θ

/-! ## Inner products, weights and energies -/


/-- The `ρ`-weighted `L²` inner product: `∫∫ g₁ g₂ ρ`. -/
def wip (ρ g₁ g₂ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, g₁ z θ * g₂ z θ * ρ z θ


/-- The squared `L²` norm of a *radial* function, `∫_0^∞ g(z)² dz`. -/
def L2Sqz (g : ℝ → ℝ) : ℝ := ∫ z in Spaces.Iz, (g z) ^ 2


/-- The weight `w/√(sin(2θ)^γ)`; note `wtGam (gam α) = Spaces.Wt α`. -/
def wtGam (γ z θ : ℝ) : ℝ := Spaces.w z * (Real.sin (2 * θ)) ^ (-(γ / 2))

/-- The weight `w/√(sin(2θ)^η)` with the paper's `η = 99/100`. -/
def wtEta (z θ : ℝ) : ℝ := wtGam Spaces.eta z θ

/-- `|f w|²_{L²}`. -/
def Ef (f : ℝ → ℝ → ℝ) : ℝ := Spaces.L2Sq (fun z θ => f z θ * Spaces.w z)

/-- `|D_z f · w/√(sin(2θ)^η)|²_{L²}`. -/
def EDz (f : ℝ → ℝ → ℝ) : ℝ := Spaces.L2Sq (fun z θ => Spaces.Dz f z θ * wtEta z θ)

/-- `|D_θ f · w/√(sin(2θ)^γ)|²_{L²}`. -/
def EDth (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  Spaces.L2Sq (fun z θ => Spaces.Dth f z θ * wtGam (Spaces.gam α) z θ)

/-- `|f · w/√(sin(2θ)^η)|²_{L²}`. -/
def EfEta (f : ℝ → ℝ → ℝ) : ℝ := Spaces.L2Sq (fun z θ => f z θ * wtEta z θ)

/-- `|z^{-1} L₁₂(f)|²_{L²_z}` (radial `L²` norm, no angular factor). -/
def EL12z (f : ℝ → ℝ → ℝ) : ℝ := L2Sqz (fun z => L12f f z / z)

/-- `|D_θ f · w|²_{L²}` — the `L²` norm of the angular derivative with the *radial*
weight only (the error term of Proposition `L2CoercivityTransport`). -/
def EDthW (f : ℝ → ℝ → ℝ) : ℝ :=
  wip (fun z _ => Spaces.w z ^ 2) (Spaces.Dth f) (Spaces.Dth f)



/-- The paper's inner product on `ℋ¹`:
`10(D_zf,D_zg w²/sin^η) + 10^10(fw,gw/sin^η) + 10^17(fw,gw) + 10^21(D_θf,D_θg w²/sin^γ)`. -/
def H1IP (α : ℝ) (f g : ℝ → ℝ → ℝ) : ℝ :=
  10 * wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) (Spaces.Dz f) (Spaces.Dz g)
    + (10 : ℝ) ^ 10 * wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) f g
    + (10 : ℝ) ^ 17 * wip (fun z _ => Spaces.w z ^ 2) f g
    + (10 : ℝ) ^ 21 * wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.gam α))
        (Spaces.Dth f) (Spaces.Dth g)

/-- The paper's inductive step for the inner product on `ℋ^k`:
`(f,g)_{ℋ^k} = (f,g)_{ℋ^{k-1}} + c₁(D_θf,D_θg)_{ℋ^{k-1}} + c₂(D_zf,D_zg)_{ℋ^{k-1}}`. -/
def HkIPStep (c₁ c₂ : ℝ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ)
    (f g : ℝ → ℝ → ℝ) : ℝ :=
  IP f g + c₁ * IP (Spaces.Dth f) (Spaces.Dth g) + c₂ * IP (Spaces.Dz f) (Spaces.Dz g)

/-- The admissible class of the `ℋ^k` coercivity layer: `f` is smooth on a neighbourhood
of the closed quadrant, and **every** mixed `D`-derivative `D_z^b D_θ^a f` with `a + b ≤ k`
lies in `ℋ^k` and has vanishing `L₁₂`-zero-mode `L₁₂(D_z^bD_θ^a f)(0) = 0`.  The zero-mode
conditions are the paper's projector conditions ("if `g` vanishes quadratically at `z = 0`
and `L₁₂(g)(0) = 0` then the same can be said about `𝓛_Γ^T(g)`"); they are exactly what
makes the commutator defects `E₁`, `E₂` lie honestly in `ℋⁿ`.  The class is closed under
`D_θ` and `D_z` (`HkAdm_dth`), which is what the induction needs. -/
def HkAdm (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  Spaces.SmoothNbhd f ∧
    (∀ a b : ℕ, a + b ≤ k → Spaces.HkMem α k (Spaces.mixed b a f)) ∧
    (∀ a b : ℕ, a + b ≤ k → L12f (Spaces.mixed b a f) 0 = 0)

/-- `IP` is an admissible inner product on `ℋ^k` in the sense of the paper's
§"Higher order derivatives and the inner product on `ℋ^k`".  It is a **globally** additive
and homogeneous functional with nonnegative diagonal — the paper's induction writes
`IP (D_θ𝓛_Γ^T f) (D_θ f) = IP (𝓛_Γ^T(D_θ f)) (D_θ f) + IP E₁ (D_θ f)` and applies
Cauchy–Schwarz, both of which need linearity *unrestricted by membership* — while the
comparability with the `ℋ^k` norm and the coercivity of `𝓛_Γ^T` are required only on the
admissible class `HkAdm α k`.  (Restricting linearity as well makes the induction step
false: outside the `L₁₂`-zero-mode case the defect `E₁` is not in `ℋⁿ`, so no
membership-restricted clause applies to it.) -/
def IsHkIP (α : ℝ) (k : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ) : Prop :=
  (∀ (f₁ f₂ g : ℝ → ℝ → ℝ), Spaces.SmoothNbhd f₁ → Spaces.SmoothNbhd f₂ →
    Spaces.SmoothNbhd g → Spaces.HkMem α k f₁ → Spaces.HkMem α k f₂ →
    Spaces.HkMem α k g → IP (f₁ + f₂) g = IP f₁ g + IP f₂ g) ∧
  (∀ (c : ℝ) (f g : ℝ → ℝ → ℝ), Spaces.SmoothNbhd f → Spaces.SmoothNbhd g →
    Spaces.HkMem α k f → Spaces.HkMem α k g →
    IP (fun z θ => c * f z θ) g = c * IP f g) ∧
  (∀ (h : ℝ → ℝ → ℝ), 0 ≤ IP h h) ∧
  (∀ f, HkAdm α k f → Spaces.HkSq α k f ≤ IP f f) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ f, HkAdm α k f → IP f f ≤ C * Spaces.HkSq α k f) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ f, HkAdm α k f → c * Spaces.HkSq α k f ≤ IP (LGammaT α f) f)


/-- The commutator defect `E₂` of `D_z` and `𝓛_Γ^T`, in the `ℋ^n` norm:
`D_z 𝓛_Γ^T f = 𝓛_Γ^T(D_z f) + E₂` with `E₂ ∈ ℋⁿ` and
`|E₂|_{ℋⁿ} ≤ C(|f|_{ℋⁿ} + |D_θ f|_{ℋⁿ})`. -/
def CommutZ (α : ℝ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Spaces.SmoothNbhd f → Spaces.HkMem α n f →
    Spaces.HkMem α n (Spaces.Dth f) →
    Spaces.HkSq α n (fun z θ =>
        Spaces.Dz (LGammaT α f) z θ - LGammaT α (Spaces.Dz f) z θ)
      ≤ C * (Spaces.HkSq α n f + Spaces.HkSq α n (Spaces.Dth f))

/-- The paper's condition (GammaAssumption): `|Γ/c - K|_{L²([0,π/2])} ≤ 7/10`. -/
def GammaL2Bnd (α : ℝ) : Prop :=
  ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α - Spaces.K θ) ^ 2 ≤ (7 / 10 : ℝ) ^ 2

/-- The paper's pointwise condition (GammaAssumption2):
`|sin(2θ) ∂_θΓ| ≤ 2αΓ` on the angular interval. -/
def GammaPointwiseBnd (α : ℝ) : Prop :=
  ∀ θ ∈ Spaces.Iθ, |Real.sin (2 * θ) * deriv (fun t => Spaces.Gam α t) θ| ≤ 2 * α * Spaces.Gam α θ


/-! ## The analytic hypothesis package for the integration by parts -/

/-- `u` is a function of the self-similar variables on which the `z`-integration by
parts of this chapter is valid.  This is the class of functions the paper works with:
for the Hardy lemma it says "We will establish the result for smooth functions with `f`
and `L₁₂(f)` vanishing (at least) quadratically at zero. The general case will follow by
approximation."  Concretely we require

* `u` is smooth on a neighbourhood of the closed quadrant (`Spaces.SmoothNbhd`), so that
  every `θ`-slice is differentiable on `(0,∞)` and every `z`-slice on `(0,π/2)`;
* the boundary term `z (u w)²` tends to `0` at `z = 0⁺` and at `z = ∞` (this is what
  makes the boundary term of the `z`-integration by parts vanish; it holds for every
  `u` vanishing to second order at `z = 0` and decaying at infinity);
* the weighted square `(u w)²` is integrable on each `θ`-slice and on the whole
  quadrant;
* the derivative `∂_z (z (u w)²)` is integrable on each `θ`-slice (the hypothesis needed
  by the fundamental theorem of calculus on `(0,∞)`).

The `θ`-integration by parts of §6 needs no extra boundary hypothesis: the boundary term
is `sin(2θ) u(z,θ)²`, which vanishes at both endpoints of `Iθ` for the functions used
there (`u = D_θ f` always carries a factor `sin(2θ)`). -/
structure IBP (u : ℝ → ℝ → ℝ) : Prop where
  /-- `u` is smooth on a neighbourhood of the closed quadrant. -/
  smooth : Spaces.SmoothNbhd u
  /-- the boundary term `z (u w)²` vanishes at `z = 0`. -/
  bd0 : ∀ θ ∈ Spaces.Iθ, Tendsto (fun z => z * (u z θ * Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0)
  /-- the boundary term `z (u w)²` vanishes at `z = ∞`. -/
  bdTop : ∀ θ ∈ Spaces.Iθ, Tendsto (fun z => z * (u z θ * Spaces.w z) ^ 2) atTop (𝓝 0)
  /-- the weighted square is integrable on each `θ`-slice. -/
  intSq : ∀ θ ∈ Spaces.Iθ, IntegrableOn (fun z => (u z θ * Spaces.w z) ^ 2) (Set.Ioi 0)
  /-- the weighted square is integrable on the quadrant. -/
  intSqProd : IntegrableOn (fun p : ℝ × ℝ => (u p.1 p.2 * Spaces.w p.1) ^ 2)
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the derivative of the boundary term is integrable on each `θ`-slice. -/
  intDeriv : ∀ θ ∈ Spaces.Iθ,
    IntegrableOn (fun z => deriv (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z) (Set.Ioi 0)
  /-- the integrand of `wip_L_self` is jointly integrable. -/
  intL : IntegrableOn (Function.uncurry (fun z θ => L u z θ * u z θ * Spaces.w z ^ 2))
    (Spaces.Iz ×ˢ Spaces.Iθ)

/-- The analytic hypotheses of the Hardy-weight lemma (`Lemma HardyWeight` of the paper):
`f` has integrable angular slices, the radial density `L₁₂(f)` is continuous and
integrable on `(0,∞)`, all the boundary terms `L₁₂(f)² · z^{1-2j}` (`j = 0,1,2`) and
`w · L₁₂(f)²` vanish at `0⁺` and at `∞`, and the integrals occurring in the proof
converge.  The paper assumes "`f w ∈ L²` and `L₁₂(f) w ∈ L²`", which is what forces
`L₁₂(f)(0) = 0` and hence the vanishing of the boundary terms. -/
structure HardyHyp (f : ℝ → ℝ → ℝ) : Prop where
  /-- the angular slices of `f` are integrable, so that `L12dens` is the honest density. -/
  hslice : ∀ z ∈ Set.Ioi 0, IntegrableOn (fun θ => Spaces.K θ * f z θ / z) Spaces.Iθ
  /-- `L12dens` is continuous on `(0,∞)` (for the fundamental theorem of calculus). -/
  hcont : ∀ z ∈ Set.Ioi 0, ContinuousAt (FM.L12dens Spaces.K f) z
  /-- the density is integrable on `(0,∞)`. -/
  hint : IntegrableOn (FM.L12dens Spaces.K f) (Set.Ioi 0)
  /-- the component integrals of `L₁₂(f)` converge. -/
  intA : ∀ j : ℕ, j ≤ 2 → IntegrableOn (fun z => (L12f f z) ^ 2 / z ^ (2 * (j : ℝ))) (Set.Ioi 0)
  /-- the comparison component integrals of `f` converge. -/
  intB : ∀ j : ℕ, j ≤ 2 →
    IntegrableOn (fun z => (∫ θ in Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ))) (Set.Ioi 0)
  /-- the boundary terms `L₁₂(f)² z^{1-2j}` vanish at `z = 0`. -/
  bd0 : ∀ j : ℕ, j ≤ 2 →
    Tendsto (fun z => (L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1)) (𝓝[>] 0) (𝓝 0)
    ∧ Tendsto (fun z => Spaces.w z * (L12f f z) ^ 2) (𝓝[>] 0) (𝓝 0)
  /-- the boundary terms `L₁₂(f)² z^{1-2j}` vanish at `z = ∞`. -/
  bdTop : ∀ j : ℕ, j ≤ 2 →
    Tendsto (fun z => (L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1)) atTop (𝓝 0)
    ∧ Tendsto (fun z => Spaces.w z * (L12f f z) ^ 2) atTop (𝓝 0)

/-- The joint-integrability data needed by the `L²` coercivity chain of §6: every product
of an ingredient of `𝓛_Γ^T` (or of its `D_θ`/`D_z` derivative) with `f` against the
square of the weight and the relevant angular weight is jointly integrable on the
quadrant.  Under these hypotheses every `wip` occurring in the paper's estimates is an
honest finite number rather than Lean's junk value for a non-integrable integrand. -/
structure CoerciveData (α : ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  /-- the `𝓛 f · f w²` product is integrable. -/
  intL : IntegrableOn (Function.uncurry (fun z θ => L f z θ * f z θ * Spaces.w z ^ 2))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `L₁₂`-term of `𝓛_Γ` against `f w²` is integrable. -/
  intL12 : IntegrableOn (Function.uncurry (fun z θ =>
    (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * L12f f z * f z θ
      * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `𝓛_Γ f · f w²` product is integrable. -/
  intLG : IntegrableOn (Function.uncurry (fun z θ => LGamma α f z θ * f z θ * Spaces.w z ^ 2))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the transport term against `f w²` is integrable. -/
  intT : IntegrableOn (Function.uncurry (fun z θ => Transport f z θ * f z θ * Spaces.w z ^ 2))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the projector correction against `f w²` is integrable. -/
  intP : IntegrableOn (Function.uncurry (fun z θ =>
    Proj α (Transport f) z θ * f z θ * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `𝓛_Γ^T f · f w²` product is integrable. -/
  intLGT : IntegrableOn (Function.uncurry (fun z θ =>
    LGammaT α f z θ * f z θ * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `K`-part of the `L₁₂` integration by parts. -/
  intK : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ))) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `(Γ/c - K)`-part of the `L₁₂` integration by parts. -/
  intG : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.w z / z * L12f f z * ((Spaces.Gam α θ / Spaces.c α - Spaces.K θ) * f z θ)))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-η}`-weighted `𝓛_Γ^T f · f w²` product is integrable. -/
  intLGTeta : IntegrableOn (Function.uncurry (fun z θ =>
    LGammaT α f z θ * f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-η}`-weighted `f² w²` product is integrable. -/
  intFeta : IntegrableOn (Function.uncurry (fun z θ =>
    f z θ * f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)))
    (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `|D_θ f w|²` product is integrable. -/
  intDth : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.Dth f z θ * Spaces.Dth f z θ * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-γ}`-weighted `(D_θ f)² w²` product is integrable. -/
  intDthGam : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.Dth f z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
      * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-γ}`-weighted `D_θ𝓛_Γ^T f · D_θ f w²` product is integrable. -/
  intDthDth : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.Dth (LGammaT α f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
      * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-η}`-weighted `D_z𝓛_Γ^T f · D_z f w²` product is integrable. -/
  intDzDz : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.Dz (LGammaT α f) z θ * Spaces.Dz f z θ * Spaces.w z ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ)
  /-- the `sin(2θ)^{-η}`-weighted `(D_z f)² w²` product is integrable. -/
  intDz : IntegrableOn (Function.uncurry (fun z θ =>
    Spaces.Dz f z θ * Spaces.Dz f z θ * Spaces.w z ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ)

/-! ## Elementary API -/











theorem LGammaT_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    LGammaT α f z θ
      = LGamma α f z θ - Proj α (Transport f) z θ := rfl

theorem Proj_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Proj α f z θ
      = f z θ - (Spaces.Gam α θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * L12f f 0 := rfl

theorem Transport_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Transport f z θ = 3 * Spaces.Dth f z θ / (1 + z) := rfl

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.HkIntegrand_endpoint_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `H^k`-integrand vanishes at the two angular endpoints

`HkIntegrand α n u z θ` is a sum of squares of weighted derivatives of `u`.
Every summand carries a factor that vanishes when `sin (2θ) = 0`:

* the first sum carries `1 / sin(2θ)^{η/2}`, hence is `0` at a zero of `sin(2θ)`
  (the positive power `0^{η/2}` is `0`, and `x / 0 = 0` in `ℝ`);
* in the second sum the only non-trivial summands have `1 ≤ i`, so they involve
  `mixed j i u = D_z^j D_θ^i u`; the outermost operation `D_θ` carries a factor
  `sin (2θ)`, and any `D_z`-iterate of a function vanishing on the line
  `{θ = θ₀}` still vanishes there.

Consequently the integrand is `0` at `θ = 0` and at `θ = π/2` for **every**
`α`, `n`, `u` and `z` (in particular without any regularity assumption on `u`).
This is the endpoint boundary condition needed so that integrating
`HkIntegrand` over `[0, π/2]` sees no contribution from the angular boundary.
-/

noncomputable section

open Work.Spaces

namespace Work.Coercivity

/-- At an angle where `sin (2θ) = 0`, every `D_θ`-iterate `D_θ^i u` with `i ≥ 1`
vanishes: the outermost `D_θ` is `sin (2θ) · ∂_θ`. -/
lemma DthIter_eq_zero_of_sin_eq_zero (u : ℝ → ℝ → ℝ) (i : ℕ) (hi : 1 ≤ i) (θ : ℝ)
    (h : Real.sin (2 * θ) = 0) (z : ℝ) : Work.Spaces.DthIter i u z θ = 0 := by
  cases i with
  | zero => omega
  | succ m => simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, h, zero_mul]

/-- If `g (·) θ` vanishes identically, then so does every `D_z`-iterate
`D_z^j g (·) θ`: `D_z = z ∂_z` is a derivation, and the derivative of the zero
function is zero. -/
lemma DzIter_eq_zero_of_forall_eq_zero (g : ℝ → ℝ → ℝ) (θ : ℝ) (hg : ∀ z, g z θ = 0)
    (j : ℕ) (z : ℝ) : Work.Spaces.DzIter j g z θ = 0 := by
  induction j generalizing z with
  | zero => simpa using hg z
  | succ m ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have hfun : (fun z' => Work.Spaces.DzIter m g z' θ) = fun _ => (0 : ℝ) :=
      funext fun z' => ih z'
    simp only [Work.Spaces.pz, hfun, deriv_const, mul_zero]

/-- At an angle where `sin (2θ) = 0`, every mixed derivative `mixed j i u` with
`i ≥ 1` vanishes.  This is the summand of the second sum of `HkIntegrand`. -/
lemma mixed_eq_zero_of_sin_eq_zero (u : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (θ : ℝ)
    (h : Real.sin (2 * θ) = 0) (z : ℝ) : Work.Spaces.mixed j i u z θ = 0 := by
  rw [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_forall_eq_zero (Work.Spaces.DthIter i u) θ
    (fun z' => DthIter_eq_zero_of_sin_eq_zero u i hi θ h z') j z

/-- The `H^k`-integrand vanishes at any angle `θ` with `sin (2θ) = 0`. -/
lemma HkIntegrand_eq_zero_of_sin_eq_zero (α : ℝ) (n : ℕ) (u : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α n u z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hden : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [h, Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero]
  rw [Finset.sum_eq_zero (fun i _ => by rw [hden, mul_zero, sq, mul_zero]),
      Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_)), add_zero]
  split_ifs with hc
  · rw [mixed_eq_zero_of_sin_eq_zero u j i hc.1 θ h z, zero_mul, sq, mul_zero]
  · rfl


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.HkIntegrand_le_succ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- The `H^k`-integrand is monotone in `k`: enlarging `k` only adds non-negative
terms, both in the first (pure `D_z`) sum and in the double (mixed) sum, and
moreover weakens the constraint `i + j ≤ k` on the mixed summands. -/
theorem HkIntegrand_le_succ (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α (k + 1) f z θ := by
  simp only [Work.Spaces.HkIntegrand]
  refine add_le_add ?_ ?_
  · -- the first sum: `range (k+1) ⊆ range (k+2)` and all summands are squares
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
    intro i _ _
    positivity
  · -- the double sum
    have inner : ∀ i : ℕ,
        (∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (∑ j ∈ Finset.range (k + 2),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
      intro i
      -- pointwise in `j`: the constraint `i + j ≤ k` implies `i + j ≤ k + 1`
      have hpt : ∀ j : ℕ,
          (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
        intro j
        split_ifs with h1 h2
        · exact le_refl _
        · exact absurd ⟨h1.1, by omega⟩ h2
        · positivity
        · exact le_refl 0
      calc (∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k + 1 then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
            Finset.sum_le_sum (fun j _ => hpt j)
        _ ≤ (∑ j ∈ Finset.range (k + 2),
              (if 1 ≤ i ∧ i + j ≤ k + 1 then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
            intro j _ _
            by_cases h2 : 1 ≤ i ∧ i + j ≤ k + 1
            · simp [h2]; positivity
            · simp [h2]
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 2),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
          Finset.sum_le_sum (fun i _ => inner i)
      _ ≤ (∑ i ∈ Finset.range (k + 2), ∑ j ∈ Finset.range (k + 2),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
          intro i _ _
          refine Finset.sum_nonneg (fun j _ => ?_)
          by_cases h2 : 1 ≤ i ∧ i + j ≤ k + 1
          · simp [h2]; positivity
          · simp [h2]

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.deriv_zero_on_Itheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.Coercivity

set_option autoImplicit false



end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.integrableOn_prod_of_box =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

set_option autoImplicit false
-- `hc` is kept as a hypothesis for compatibility with the caller's statement; the
-- argument below does not need it (the box `[c,d] × [0,π/2]` is compact for any `c ≤ d`).
set_option linter.unusedVariables false


end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.integral_Itheta_K =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped Real

namespace Work.Coercivity

/-- The angular weight `K(θ) = 3 sin θ cos²θ` integrates to `1` over `[0,π/2]`:
`∫₀^{π/2} 3 sin θ cos²θ dθ = 1`.  This is the normalisation which makes `K` a
probability-like kernel on the angular interval; it is the `α = 0` case of the
normalising constant `c(α) = ∫ Γ K`. -/
theorem integral_Itheta_K : ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ = (1 : ℝ) := by
  -- Reduce the set integral over `Iθ = [0,π/2]` to the interval integral `∫₀^{π/2}`.
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ π/2)]
  -- Fundamental theorem of calculus with the antiderivative `θ ↦ -cos³θ`.
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (π/2),
      HasDerivAt (fun θ : ℝ => - (Real.cos θ)^3) (Work.Spaces.K x) x := by
    intro x hx
    have h := ((Real.hasDerivAt_cos x).pow 3).neg
    convert h using 1
    simp only [Work.Spaces.K]; ring
  have hint : IntervalIntegrable Work.Spaces.K volume (0:ℝ) (π/2) := by
    apply Continuous.intervalIntegrable
    change Continuous (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2)
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Real.cos_pi_div_two, Real.cos_zero]
  norm_num

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.integral_sin_two_neg_rpow_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The angular integral of `sin(2θ)^{-q}` over `Iθ = [0,π/2]` is finite and bounded by
`4/(1-q)` for `0 < q < 1`.

The integrand has integrable singularities at both endpoints `θ = 0` and `θ = π/2`.
Jordan's inequality `sin(2θ) ≥ (4/π)θ` gives the pointwise majorant
`sin(2θ)^{-q} ≤ (π/4)^q (θ^{-q} + (π/2-θ)^{-q})` on `Iθ`, which is integrable with
integral `π (1/2)^q / (1-q) ≤ 4/(1-q)`. -/
theorem integral_sin_two_neg_rpow_le (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) ≤ 4 / (1 - q) := by
  have hden : (0 : ℝ) < 1 - q := by linarith
  -- The majorant, its integrability, and its integral.
  have hGint : Integrable
      (fun θ : ℝ => (Real.pi / 4) ^ q * (θ ^ (-q) + (Real.pi / 2 - θ) ^ (-q)))
      (volume.restrict Work.Spaces.Iθ) := by
    rw [Work.Spaces.Iθ]
    exact Work.Spaces.integrableOn_majorant_rpow q hq0 hq1
  have hGval : ∫ θ in Work.Spaces.Iθ,
        ((Real.pi / 4) ^ q * (θ ^ (-q) + (Real.pi / 2 - θ) ^ (-q)))
      = Real.pi * (1 / 2) ^ q / (1 - q) := by
    rw [Work.Spaces.Iθ]
    exact Work.Spaces.integral_majorant_rpow q hq0 hq1
  -- Nonnegativity of the integrand on `Iθ`.
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Real.rpow_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) (-q)
  -- The pointwise majorant.
  have hpoint : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.pi / 4) ^ q * (θ ^ (-q) + (Real.pi / 2 - θ) ^ (-q))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Work.Spaces.sin_rpow_le_majorant_pi q θ hq0 hθ
  -- Measurability of the integrand.
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q))
      (volume.restrict Work.Spaces.Iθ) :=
    (Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) (-q))
      |>.aestronglyMeasurable
  -- Domination of the norms.
  have hnorm : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖(Real.sin (2 * θ)) ^ (-q)‖
        ≤ (Real.pi / 4) ^ q * (θ ^ (-q) + (Real.pi / 2 - θ) ^ (-q)) := by
    filter_upwards [hpoint, hnonneg] with θ h1 h2
    rw [Real.norm_of_nonneg h2]
    exact h1
  constructor
  · exact hGint.mono' hmeas hnorm
  · calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        ≤ ∫ θ in Work.Spaces.Iθ,
            ((Real.pi / 4) ^ q * (θ ^ (-q) + (Real.pi / 2 - θ) ^ (-q))) :=
          integral_mono_of_nonneg hnonneg hGint hpoint
      _ = Real.pi * (1 / 2) ^ q / (1 - q) := hGval
      _ ≤ 4 / (1 - q) := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hden)
          have hhalf : (1 / 2 : ℝ) ^ q ≤ 1 :=
            Real.rpow_le_one (by norm_num) (by norm_num) (le_of_lt hq0)
          have hnum : Real.pi * (1 / 2) ^ q ≤ 4 := by
            calc Real.pi * (1 / 2) ^ q ≤ 4 * 1 :=
                  mul_le_mul (le_of_lt Real.pi_lt_four) hhalf (by positivity) (by norm_num)
              _ = 4 := by norm_num
          linarith

end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.prod_slice_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory


end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.setIntegral_iterated_le_of_pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set

namespace Work.Coercivity

set_option autoImplicit false


end Work.Coercivity
end
end
-- ===== merged: Submission.Work.Coercivity.slice_cs_K =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- Cauchy–Schwarz on an angular slice: for every `z`, if `θ ↦ (f z θ)²` is integrable on
`Iθ` then the squared angular average against `K = 3 sin θ cos²θ` is bounded by `3` times the
`θ`-energy of `f z ·`.

Intended proof: set `μ := volume.restrict Spaces.Iθ`. From `hL2` get
`AEStronglyMeasurable (fun θ => (f z θ) ^ 2) μ`, hence (composing with the continuous
`Real.sqrt` and using `Real.sqrt_sq_eq_abs`) `AEStronglyMeasurable (fun θ => |f z θ|) μ`;
`simp only [sq_abs]` turns `hL2` into `Integrable (fun θ => |f z θ| ^ 2) μ`, so
`MemLp (fun θ => |f z θ|) 2 μ` by `MeasureTheory.memLp_two_iff_integrable_sq`. Likewise
`hKi` plus continuity of `K` gives `MemLp Spaces.K 2 μ`. Then
`Work.Elliptic.integral_mul_sq_le_sq_mul_sq_aux μ` applied to `K` and `|f z ·|` (both
nonnegative a.e.; `0 ≤ᵐ K` from `hKnn` and `ae_restrict_of_forall_mem`) gives
`(∫ θ in Iθ, K θ * |f z θ|)² ≤ (∫ θ in Iθ, (K θ)²) * (∫ θ in Iθ, |f z θ|²)`.
Combine with `|∫ θ, K θ * f z θ| ≤ ∫ θ, |K θ * f z θ| = ∫ θ, K θ * |f z θ|`
(`abs_integral_le_integral_abs`; the equality uses `0 ≤ K` on `Iθ`), `hK2`, and
`∫ θ, |f z θ|² = ∫ θ, (f z θ)²`. Note no measurability of `f` is assumed: it is derived. -/
theorem slice_cs_K (f : ℝ → ℝ → ℝ) (z : ℝ)
    (hKnn : ∀ θ ∈ Spaces.Iθ, 0 ≤ Spaces.K θ)
    (hKi : MeasureTheory.IntegrableOn (fun θ => (Spaces.K θ) ^ 2) Spaces.Iθ)
    (hK2 : (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) ≤ 3)
    (hL2 : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Spaces.Iθ) :
    (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 ≤ 3 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2 := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Spaces.Iθ with hμ
  have hIθ_meas : MeasurableSet Spaces.Iθ := by
    rw [Spaces.Iθ]; exact measurableSet_Icc
  -- `K` is nonnegative a.e. on the slice
  have hKnn_ae : 0 ≤ᵐ[μ] Spaces.K := by
    rw [hμ]
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθ
    exact hKnn θ hθ
  -- `K` is measurable and `L²`
  have hKcont : Continuous Spaces.K := by
    unfold Spaces.K; fun_prop
  have hKmeas : MeasureTheory.AEStronglyMeasurable Spaces.K μ := hKcont.aestronglyMeasurable
  have hKint : MeasureTheory.Integrable (fun θ => (Spaces.K θ) ^ 2) μ := by
    rw [hμ]; exact hKi
  have hKmem : MeasureTheory.MemLp Spaces.K 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hKmeas).mpr hKint
  -- `|f z ·|` is measurable and `L²`
  have hf2_int : MeasureTheory.Integrable (fun θ => (f z θ) ^ 2) μ := by
    rw [hμ]; exact hL2
  have hmeas_sq : MeasureTheory.AEStronglyMeasurable (fun θ => (f z θ) ^ 2) μ :=
    hf2_int.aestronglyMeasurable
  have hmeas_abs : MeasureTheory.AEStronglyMeasurable (fun θ => |f z θ|) μ := by
    have h := Real.continuous_sqrt.comp_aestronglyMeasurable hmeas_sq
    simpa only [Real.sqrt_sq_eq_abs] using h
  have hint_abs2 : MeasureTheory.Integrable (fun θ => |f z θ| ^ 2) μ := by
    refine hf2_int.congr ?_
    filter_upwards with θ
    rw [sq_abs]
  have hmem_abs : MeasureTheory.MemLp (fun θ => |f z θ|) 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmeas_abs).mpr hint_abs2
  have habs_nn_ae : 0 ≤ᵐ[μ] (fun θ => |f z θ|) :=
    Filter.Eventually.of_forall fun θ => abs_nonneg _
  -- Cauchy–Schwarz
  have hcs := Work.Elliptic.integral_mul_sq_le_sq_mul_sq_aux μ hKmem hmem_abs hKnn_ae habs_nn_ae
  have hK2' : (∫ x, (Spaces.K x) ^ 2 ∂μ) ≤ 3 := by
    rw [hμ]; exact hK2
  have hfnn : 0 ≤ ∫ x, (f z x) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg (f z x))
  have habs2eq : (∫ x, |f z x| ^ 2 ∂μ) = ∫ x, (f z x) ^ 2 ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [sq_abs]
  -- Step 1: `∫ K * |f|` controls the square of the signed integral.
  have hstep1 : |∫ x, Spaces.K x * f z x ∂μ| ≤ ∫ x, Spaces.K x * |f z x| ∂μ := by
    refine (MeasureTheory.abs_integral_le_integral_abs (μ := μ)
      (f := fun x => Spaces.K x * f z x)).trans ?_
    apply le_of_eq
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hKnn_ae] with x hx
    rw [abs_mul, abs_of_nonneg hx]
  -- Step 2: Cauchy–Schwarz bound for `∫ K * |f|`.
  have hstep2 : (∫ x, Spaces.K x * |f z x| ∂μ) ^ 2 ≤ 3 * ∫ x, (f z x) ^ 2 ∂μ := by
    calc (∫ x, Spaces.K x * |f z x| ∂μ) ^ 2
        ≤ (∫ x, (Spaces.K x) ^ 2 ∂μ) * (∫ x, |f z x| ^ 2 ∂μ) := hcs
      _ = (∫ x, (Spaces.K x) ^ 2 ∂μ) * (∫ x, (f z x) ^ 2 ∂μ) := by rw [habs2eq]
      _ ≤ 3 * (∫ x, (f z x) ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_right hK2' hfnn
  calc (∫ x, Spaces.K x * f z x ∂μ) ^ 2
      = |∫ x, Spaces.K x * f z x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x, Spaces.K x * |f z x| ∂μ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hstep1 2
    _ ≤ 3 * ∫ x, (f z x) ^ 2 ∂μ := hstep2

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.slice_deriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open scoped NNReal ENNReal Topology

/-- **Cauchy-type estimate on a slice.**  If `G` is the sum of the power series `q` on the ball of
radius `r` around the origin of `ℝ × ℝ`, and `4ρ < r`, then for every `k` the `k`-th derivative of
`G` at a point `(0, δ)` with `|δ| ≤ ρ`, taken in the direction `(1, 0)`, is bounded by
`C k! / ρ^k` with a constant `C` independent of `k` and `δ`.

The proof shifts the origin to `a = (0, δ)`, rewrites the `k`-th derivative of `G` at `a` along the
diagonal `(1,0)` as `k!` times the `k`-th coefficient `(q.changeOrigin a) k` of the shifted series,
and bounds that coefficient by Cauchy's estimate for power series coefficients. -/
theorem slice_deriv_bound {G : ℝ × ℝ → ℝ} {q : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ} {r : ℝ≥0}
    (hq : HasFPowerSeriesOnBall G q 0 (r : ℝ≥0∞))
    {ρ : ℝ≥0} (hρ : 0 < ρ) (h4ρ : 4 * ρ < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (δ : ℝ), |δ| ≤ (ρ : ℝ) →
      ‖iteratedFDeriv ℝ k G ((0 : ℝ), δ) (fun _ => ((1 : ℝ), (0 : ℝ)))‖ ≤
        C * (k.factorial : ℝ) / (ρ : ℝ) ^ k := by
  -- Choose `s` with `4 ρ < s < r`.
  obtain ⟨s, hs4, hsr⟩ : ∃ s : ℝ≥0, 4 * ρ < s ∧ s < r := by
    refine ⟨((4 * ρ + r) / 2 : ℝ≥0), ?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul]
      push_cast
      have h4ρ' : (4 : ℝ) * (ρ : ℝ) < (r : ℝ) := by exact_mod_cast h4ρ
      linarith
    · rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul]
      push_cast
      have h4ρ' : (4 : ℝ) * (ρ : ℝ) < (r : ℝ) := by exact_mod_cast h4ρ
      linarith
  have hs0 : (0 : ℝ) < (s : ℝ) := by
    have h4ρ' : (4 : ℝ) * (ρ : ℝ) < (s : ℝ) := by exact_mod_cast hs4
    nlinarith [show (0 : ℝ) ≤ (ρ : ℝ) by positivity]
  have hs0_nn : (0 : ℝ≥0) < s := lt_of_lt_of_le (mul_pos (by norm_num) hρ) (le_of_lt hs4)
  have hs_rad : (s : ℝ≥0∞) < q.radius :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hsr) hq.r_le
  -- Cauchy's estimate for the coefficients of `q`.
  obtain ⟨M, hMpos, hM⟩ := q.norm_le_div_pow_of_pos_of_lt_radius (r := s) hs0_nn hs_rad
  refine ⟨2 * M, by positivity, fun k δ hδ => ?_⟩
  set a : ℝ × ℝ := ((0 : ℝ), δ) with ha_def
  have ha_norm : ‖a‖ ≤ (ρ : ℝ) := by
    rw [ha_def, Prod.norm_def]
    simpa using hδ
  have hρ_le_4ρ : ρ ≤ 4 * ρ := by
    rw [← NNReal.coe_le_coe]; push_cast
    nlinarith [show (0 : ℝ) ≤ (ρ : ℝ) by positivity]
  have hnorm_nn_ρ : ‖a‖₊ ≤ ρ := by
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact ha_norm
  have hnorm_nn_r : ‖a‖₊ < r := lt_of_le_of_lt hnorm_nn_ρ (lt_of_le_of_lt hρ_le_4ρ h4ρ)
  have hnorm_nn_s : ‖a‖₊ < s := lt_of_le_of_lt hnorm_nn_ρ (lt_of_le_of_lt hρ_le_4ρ hs4)
  have ha_r : (‖a‖₊ : ℝ≥0∞) < (r : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr hnorm_nn_r
  have ha_q : (‖a‖₊ : ℝ≥0∞) < q.radius :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hnorm_nn_s) (le_of_lt hs_rad)
  -- Shift the origin and use the diagonal formula for the `k`-th derivative.
  have hca := hq.changeOrigin ha_r
  have hfs := hca.factorial_smul ((1 : ℝ), (0 : ℝ)) k
  rw [zero_add] at hfs
  rw [← hfs, nsmul_eq_mul, norm_mul]
  have hkfac : ‖(k.factorial : ℝ)‖ = (k.factorial : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hkfac]
  have hz_le : ‖(q.changeOrigin a) k (fun _ => ((1 : ℝ), (0 : ℝ)))‖ ≤ ‖q.changeOrigin a k‖ := by
    have h := (q.changeOrigin a k).le_opNorm (fun _ => ((1 : ℝ), (0 : ℝ)))
    have h1 : (∏ i : Fin k, ‖((1 : ℝ), (0 : ℝ))‖) = 1 := by simp [Prod.norm_def]
    rwa [h1, mul_one] at h
  -- Cauchy's estimate for the shifted series.
  have hbound : ‖q.changeOrigin a k‖ ≤ (2 : ℝ) ^ (k + 1) * M / (s : ℝ) ^ k := by
    exact changeOrigin_opNorm_bound (p := q) (a := a) (M := M) (s := (s : ℝ)) (ρ := (ρ : ℝ))
      k hMpos hs0 (by positivity) (by exact_mod_cast hs4) hM ha_norm ha_q
  have hρpos : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have h2ρ : (2 : ℝ) * (ρ : ℝ) ≤ (s : ℝ) := by
    have h4ρ' : (4 : ℝ) * (ρ : ℝ) < (s : ℝ) := by exact_mod_cast hs4
    linarith
  have hmain : (2 : ℝ) ^ (k + 1) * M / (s : ℝ) ^ k ≤ 2 * M / (ρ : ℝ) ^ k := by
    rw [div_le_div_iff₀ (pow_pos hs0 k) (pow_pos hρpos k)]
    have key : ((2 : ℝ) * (ρ : ℝ)) ^ k ≤ (s : ℝ) ^ k := pow_le_pow_left₀ (by positivity) h2ρ k
    calc (2 : ℝ) ^ (k + 1) * M * (ρ : ℝ) ^ k = (2 * M) * ((2 : ℝ) * (ρ : ℝ)) ^ k := by
          rw [pow_succ, mul_pow]; ring
      _ ≤ (2 * M) * (s : ℝ) ^ k := by gcongr
      _ = 2 * M * (s : ℝ) ^ k := by ring
  calc (k.factorial : ℝ) * ‖(q.changeOrigin a) k (fun _ => ((1 : ℝ), (0 : ℝ)))‖
      ≤ (k.factorial : ℝ) * ‖q.changeOrigin a k‖ :=
        mul_le_mul_of_nonneg_left hz_le (Nat.cast_nonneg _)
    _ ≤ (k.factorial : ℝ) * ((2 : ℝ) ^ (k + 1) * M / (s : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ ≤ (k.factorial : ℝ) * (2 * M / (ρ : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _)
    _ = 2 * M * (k.factorial : ℝ) / (ρ : ℝ) ^ k := by ring

end Work.Coercivity
end
-- ===== merged: Submission.Work.Coercivity.thetaIntegral_analytic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped NNReal ENNReal Topology Real
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option linter.unusedSimpArgs false
set_option autoImplicit false

set_option quotPrecheck false

/-- The angular interval `[0, π/2]`. -/
local notation "Iθ" => Set.Icc (0:ℝ) (Real.pi / 2)

local notation "U" => Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (-1) (Real.pi / 2 + 1) : Set ℝ)












end Work.Coercivity
end
end
-- ===== merged: Submission.Work.ConstructionInstance.one_sub_one_sub_rpow_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

lemma one_sub_one_sub_rpow_le {β u : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) : 1 - (1 - u) ^ (3 * β) ≤ (3 * u) ^ β := by
  have h1u : 0 ≤ 1 - u := by linarith
  have hb0 : 0 ≤ (1 - u) ^ (3 : ℝ) := Real.rpow_nonneg h1u 3
  have hb1 : (1 - u) ^ (3 : ℝ) ≤ 1 := by
    have h := Real.rpow_le_rpow h1u (show 1 - u ≤ 1 by linarith) (show (0 : ℝ) ≤ 3 by norm_num)
    rwa [Real.one_rpow] at h
  have hbβ1 : ((1 - u) ^ (3 : ℝ)) ^ β ≤ 1 := by
    have h := Real.rpow_le_rpow hb0 hb1 hβ.le
    rwa [Real.one_rpow] at h
  have habs := A0_rpow_sub_le (β := β) (t := 1) (u := (1 - u) ^ (3 : ℝ)) hβ hβ1
      (by norm_num) hb0
  rw [Real.one_rpow,
      abs_of_nonneg (sub_nonneg.mpr hbβ1), abs_of_nonneg (sub_nonneg.mpr hb1)] at habs
  -- habs : 1 - ((1-u)^3)^β ≤ (1 - (1-u)^3)^β
  have hb3 : (1 - u) ^ (3 : ℝ) = (1 - u) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.rpow_mul h1u 3 β]
  refine le_trans habs ?_
  refine Real.rpow_le_rpow ?_ ?_ hβ.le
  · rw [hb3]
    have hfac : 1 - (1 - u) ^ (3 : ℕ) = u * (u ^ 2 - 3 * u + 3) := by ring
    rw [hfac]
    exact mul_nonneg hu0 (by nlinarith [sq_nonneg (2 * u - 3)])
  · rw [hb3]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) (show u - 3 ≤ 0 by linarith)]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.rpow_far_arith =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- Arithmetic residual estimate used when both the singular point and the evaluation point are
far from the origin: for `0 < α < 1` and `0 < d ≤ s`,
`1024 d ^ 2 s ^ (-4) + 4 d s ^ (-3) ≤ 1028 d ^ α s ^ (-2 - α)`.

Writing `u = d / s ∈ (0,1]` and `d = u s`, the three terms become `u ^ 2 s ^ (-2)`, `u s ^ (-2)`
and `d ^ α s ^ (-2 - α) = u ^ α s ^ (-2)`, so the claim reduces (after cancelling the common
positive factor `s ^ (-2)`) to the elementary comparison `rpow_sq_le_exp_small`. -/
theorem rpow_far_arith {α d s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hd : 0 < d) (hs : 0 < s)
    (hds : d ≤ s) :
    1024 * d ^ (2 : ℝ) * s ^ (-4 : ℝ) + 4 * d * s ^ (-3 : ℝ) ≤ 1028 * d ^ α * s ^ (-2 - α) := by
  set u : ℝ := d / s with hu
  have hu_pos : 0 < u := by rw [hu]; exact div_pos hd hs
  have hu_le : u ≤ 1 := by rw [hu]; exact (div_le_one hs).mpr hds
  have hd_eq : d = u * s := by rw [hu, div_mul_cancel₀ d hs.ne']
  have hkey : 1024 * u ^ (2 : ℝ) + 4 * u ≤ 1028 * u ^ α :=
    rpow_sq_le_exp_small hu_pos hu_le hα hα1
  have hs2pos : (0 : ℝ) < s ^ (-2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hmult : (1024 * u ^ (2 : ℝ) + 4 * u) * s ^ (-2 : ℝ) ≤ 1028 * u ^ α * s ^ (-2 : ℝ) :=
    mul_le_mul_of_nonneg_right hkey hs2pos.le
  have h1 : (u * s) ^ (2 : ℝ) = u ^ (2 : ℝ) * s ^ (2 : ℝ) := Real.mul_rpow hu_pos.le hs.le
  have h2 : (u * s) ^ α = u ^ α * s ^ α := Real.mul_rpow hu_pos.le hs.le (z := α)
  have hs2 : s ^ (2 : ℝ) * s ^ (-4 : ℝ) = s ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hs (2 : ℝ) (-4)]
    norm_num
  have hs3 : s * s ^ (-3 : ℝ) = s ^ (-2 : ℝ) := by
    calc s * s ^ (-3 : ℝ) = s ^ (1 : ℝ) * s ^ (-3 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ ((1 : ℝ) + (-3)) := (Real.rpow_add hs 1 (-3)).symm
      _ = s ^ (-2 : ℝ) := by rw [show (1 : ℝ) + (-3) = -2 by norm_num]
  have hs4 : s ^ α * s ^ (-2 - α) = s ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hs α (-2 - α), show α + (-2 - α) = (-2 : ℝ) by ring]
  have hL : 1024 * (u ^ (2 : ℝ) * s ^ (2 : ℝ)) * s ^ (-4 : ℝ) + 4 * (u * s) * s ^ (-3 : ℝ)
      = (1024 * u ^ (2 : ℝ) + 4 * u) * s ^ (-2 : ℝ) := by
    rw [show (1024 : ℝ) * (u ^ (2 : ℝ) * s ^ (2 : ℝ)) * s ^ (-4 : ℝ)
          = 1024 * u ^ (2 : ℝ) * (s ^ (2 : ℝ) * s ^ (-4 : ℝ)) by ring,
        show (4 : ℝ) * (u * s) * s ^ (-3 : ℝ) = 4 * u * (s * s ^ (-3 : ℝ)) by ring,
        hs2, hs3]
    ring
  have hR : 1028 * u ^ α * s ^ (-2 : ℝ) = 1028 * (u ^ α * s ^ α) * s ^ (-2 - α) := by
    rw [← hs4]
    ring
  rw [hd_eq, h1, h2, hL, ← hR]
  exact hmult

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.Cyl.Frame =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# Basic facts about the cylindrical frame on ℝ³

Elementary API for the coordinate functions and the frame `e_r, e_θ, e₃` of
`Work.Cyl.Coords`, plus the coordinate expressions of the components of a field.
-/

noncomputable section

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

variable {x : R3}

/-! ## The radial coordinate -/

lemma radSq_nonneg (x : R3) : 0 ≤ radSq x := by simp only [radSq]; positivity

lemma radial_nonneg (x : R3) : 0 ≤ radial x := Real.sqrt_nonneg _

lemma radial_sq (x : R3) : radial x ^ 2 = radSq x := Real.sq_sqrt (radSq_nonneg x)

lemma radSq_eq_zero_iff (x : R3) : radSq x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  rw [radSq]
  constructor
  · intro h
    have h0 : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h1 : x 1 ^ 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    exact ⟨(pow_eq_zero_iff (n := 2) (by norm_num)).mp h0,
      (pow_eq_zero_iff (n := 2) (by norm_num)).mp h1⟩
  · rintro ⟨h0, h1⟩; simp [h0, h1]

lemma radial_eq_zero_iff (x : R3) : radial x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  rw [radial, Real.sqrt_eq_zero']
  exact ⟨fun h => (radSq_eq_zero_iff x).mp (le_antisymm h (radSq_nonneg x)),
    fun h => le_of_eq ((radSq_eq_zero_iff x).mpr h)⟩

lemma radial_pos_iff (x : R3) : 0 < radial x ↔ x 0 ≠ 0 ∨ x 1 ≠ 0 := by
  rw [radial, Real.sqrt_pos, radSq]
  constructor
  · intro h; by_contra hc
    simp only [not_or, not_not] at hc
    rw [hc.1, hc.2] at h; norm_num at h
  · rintro (h | h)
    · nlinarith [sq_pos_iff.mpr h, sq_nonneg (x 1)]
    · nlinarith [sq_pos_iff.mpr h, sq_nonneg (x 0)]


/-! ## Coordinates and inner products -/

@[simp] lemma axial_eq (x : R3) : axial x = x 2 := rfl

@[simp] lemma radialVec_apply_zero (x : R3) : (radialVec x) 0 = x 0 := by simp [radialVec]
@[simp] lemma radialVec_apply_one (x : R3) : (radialVec x) 1 = x 1 := by simp [radialVec]
@[simp] lemma radialVec_apply_two (x : R3) : (radialVec x) 2 = 0 := by simp [radialVec]
@[simp] lemma angularVec_apply_zero (x : R3) : (angularVec x) 0 = -x 1 := by simp [angularVec]
@[simp] lemma angularVec_apply_one (x : R3) : (angularVec x) 1 = x 0 := by simp [angularVec]
@[simp] lemma angularVec_apply_two (x : R3) : (angularVec x) 2 = 0 := by simp [angularVec]
@[simp] lemma eZ_apply_zero : (eZ : R3) 0 = 0 := by simp [eZ, FiniteTimeSingularity.e]
@[simp] lemma eZ_apply_one : (eZ : R3) 1 = 0 := by simp [eZ, FiniteTimeSingularity.e]
@[simp] lemma eZ_apply_two : (eZ : R3) 2 = 1 := by simp [eZ, FiniteTimeSingularity.e]

@[simp] lemma eR_apply_zero (x : R3) : (eR x) 0 = x 0 / radial x := by
  simp [eR, div_eq_inv_mul]
@[simp] lemma eR_apply_one (x : R3) : (eR x) 1 = x 1 / radial x := by
  simp [eR, div_eq_inv_mul]
@[simp] lemma eR_apply_two (x : R3) : (eR x) 2 = 0 := by simp [eR]
@[simp] lemma eTheta_apply_zero (x : R3) : (eTheta x) 0 = -x 1 / radial x := by
  simp [eTheta, div_eq_inv_mul]
@[simp] lemma eTheta_apply_one (x : R3) : (eTheta x) 1 = x 0 / radial x := by
  simp [eTheta, div_eq_inv_mul]
@[simp] lemma eTheta_apply_two (x : R3) : (eTheta x) 2 = 0 := by simp [eTheta]

/-- The inner product in coordinates. -/
lemma inner_eq (a b : R3) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_three]
  ring

/-- Extensionality by coordinates. -/
lemma ext_coord {a b : R3} (h0 : a 0 = b 0) (h1 : a 1 = b 1) (h2 : a 2 = b 2) : a = b := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;> assumption

lemma inner_radialVec_self (x : R3) : inner ℝ (radialVec x) (radialVec x) = radSq x := by
  rw [inner_eq]; simp [radSq]; ring

lemma inner_angularVec_self (x : R3) : inner ℝ (angularVec x) (angularVec x) = radSq x := by
  rw [inner_eq]; simp [radSq]; ring




/-! ## The frame `e_r, e_θ, e₃` off the axis -/

lemma inner_eR_eR (x : R3) (hr : radial x ≠ 0) : inner ℝ (eR x) (eR x) = 1 := by
  rw [eR, real_inner_smul_left, real_inner_smul_right, inner_radialVec_self]
  field_simp
  exact (radial_sq x).symm

lemma inner_eTheta_eTheta (x : R3) (hr : radial x ≠ 0) : inner ℝ (eTheta x) (eTheta x) = 1 := by
  rw [eTheta, real_inner_smul_left, real_inner_smul_right, inner_angularVec_self]
  field_simp
  exact (radial_sq x).symm




lemma norm_eR (x : R3) (hr : radial x ≠ 0) : ‖eR x‖ = 1 := by
  have h : ‖eR x‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, inner_eR_eR x hr]
  nlinarith [norm_nonneg (eR x)]

lemma norm_eTheta (x : R3) (hr : radial x ≠ 0) : ‖eTheta x‖ = 1 := by
  have h : ‖eTheta x‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, inner_eTheta_eTheta x hr]
  nlinarith [norm_nonneg (eTheta x)]

/-! ## Components of a field -/

lemma compR_eq (u : R3 → R3) (x : R3) :
    compR u x = (u x 0 * x 0 + u x 1 * x 1) / radial x := by
  rw [compR, inner_eq]; simp; ring

lemma compT_eq (u : R3 → R3) (x : R3) :
    compT u x = (u x 1 * x 0 - u x 0 * x 1) / radial x := by
  rw [compT, inner_eq]; simp; ring

lemma compZ_eq (u : R3 → R3) (x : R3) : compZ u x = u x 2 := by
  rw [compZ, inner_eq]; simp

/-- Off the axis, `e_r, e_θ, e₃` is an orthonormal frame: the orthogonal decomposition of any
vector field in cylindrical components. -/
lemma decomposition (u : R3 → R3) (x : R3) (hr : radial x ≠ 0) :
    u x = compR u x • eR x + compT u x • eTheta x + compZ u x • eZ := by
  have hr2 : radial x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := radial_sq x
  refine ext_coord ?_ ?_ ?_
  · simp only [compR_eq, compT_eq, compZ_eq, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, eR_apply_zero, eR_apply_one, eR_apply_two, eTheta_apply_zero,
      eTheta_apply_one, eTheta_apply_two, eZ_apply_zero, eZ_apply_one, eZ_apply_two, mul_zero,
      add_zero]
    field_simp
    linear_combination (u x 0) * hr2
  · simp only [compR_eq, compT_eq, compZ_eq, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, eR_apply_zero, eR_apply_one, eR_apply_two, eTheta_apply_zero,
      eTheta_apply_one, eTheta_apply_two, eZ_apply_zero, eZ_apply_one, eZ_apply_two, mul_zero,
      add_zero]
    field_simp
    linear_combination (u x 1) * hr2
  · simp only [compR_eq, compT_eq, compZ_eq, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, eR_apply_two, eTheta_apply_two, eZ_apply_zero, eZ_apply_one,
      eZ_apply_two, mul_zero, add_zero, mul_one, zero_add]

/-! ## Components of `cylField` -/

@[simp] lemma cylField_zero (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    (cylField ur uz x) 0 = ur (radial x) (axial x) * x 0 / radial x := by
  simp only [cylField, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, radialVec_apply_zero, radialVec_apply_two, eZ_apply_zero, eZ_apply_two,
    mul_zero, mul_one, add_zero]
  ring

@[simp] lemma cylField_one (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    (cylField ur uz x) 1 = ur (radial x) (axial x) * x 1 / radial x := by
  simp only [cylField, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, radialVec_apply_one, radialVec_apply_two, eZ_apply_one, eZ_apply_two,
    mul_zero, mul_one, add_zero]
  ring

@[simp] lemma cylField_two (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    (cylField ur uz x) 2 = uz (radial x) (axial x) := by
  simp [cylField]






/-! ## The three dimensional radius and angle -/

lemma rho_nonneg (x : R3) : 0 ≤ rho x := Real.sqrt_nonneg _

lemma rho_sq (x : R3) : rho x ^ 2 = radSq x + axial x ^ 2 :=
  Real.sq_sqrt (add_nonneg (radSq_nonneg x) (sq_nonneg _))

lemma rho_eq_norm (x : R3) : rho x = ‖x‖ := by
  have h : rho x ^ 2 = ‖x‖ ^ 2 := by
    rw [rho_sq, ← real_inner_self_eq_norm_sq, inner_eq]
    simp [radSq]; ring
  rw [← abs_of_nonneg (rho_nonneg x), ← abs_of_nonneg (norm_nonneg x)]
  exact (sq_eq_sq_iff_abs_eq_abs _ _).mp h

lemma rho_pos_iff (x : R3) : 0 < rho x ↔ x ≠ 0 := by
  rw [rho_eq_norm, norm_pos_iff]

lemma radSq_le_rho_sq (x : R3) : radSq x ≤ rho x ^ 2 := by
  rw [rho_sq]; nlinarith [sq_nonneg (axial x)]

lemma axial_sq_le_rho_sq (x : R3) : axial x ^ 2 ≤ rho x ^ 2 := by
  rw [rho_sq]; nlinarith [radSq_nonneg x]

lemma abs_axial_le_rho (x : R3) : |axial x| ≤ rho x := by
  have h := axial_sq_le_rho_sq x
  have h2 : (|axial x| : ℝ) ^ 2 ≤ rho x ^ 2 := by rwa [sq_abs]
  nlinarith [abs_nonneg (axial x), rho_nonneg x]

lemma radial_le_rho (x : R3) : radial x ≤ rho x := by
  have h := radSq_le_rho_sq x
  have h2 : radial x ^ 2 ≤ rho x ^ 2 := by rwa [radial_sq]
  nlinarith [radial_nonneg x, rho_nonneg x]

/-! ## The polar coordinates `(ρ, θ)` on the `(r, x₃)` half plane -/

lemma rhoP_nonneg (r z : ℝ) : 0 ≤ rhoP r z := Real.sqrt_nonneg _

lemma rhoP_pos {r : ℝ} (hr : 0 < r) (z : ℝ) : 0 < rhoP r z :=
  Real.sqrt_pos.mpr (by positivity)

lemma rhoP_sq (r z : ℝ) : rhoP r z ^ 2 = r ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)

lemma rhoP_ne_zero {r : ℝ} (hr : 0 < r) (z : ℝ) : rhoP r z ≠ 0 := ne_of_gt (rhoP_pos hr z)

/-- `sin θ = z/ρ`. -/
lemma sin_thetaP {r : ℝ} (hr : 0 < r) (z : ℝ) : Real.sin (thetaP r z) = z / rhoP r z := by
  have h1 : (1:ℝ) + (z / r) ^ 2 = (r ^ 2 + z ^ 2) / r ^ 2 := by field_simp
  have h2 : Real.sqrt ((r ^ 2 + z ^ 2) / r ^ 2) = Real.sqrt (r ^ 2 + z ^ 2) / r := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hr.le]
  rw [thetaP, Real.sin_arctan, h1, h2, rhoP]
  field_simp

/-- `cos θ = r/ρ`; in particular `cos θ > 0` for `r > 0`. -/
lemma cos_thetaP {r : ℝ} (hr : 0 < r) (z : ℝ) : Real.cos (thetaP r z) = r / rhoP r z := by
  have h1 : (1:ℝ) + (z / r) ^ 2 = (r ^ 2 + z ^ 2) / r ^ 2 := by field_simp
  have h2 : Real.sqrt ((r ^ 2 + z ^ 2) / r ^ 2) = Real.sqrt (r ^ 2 + z ^ 2) / r := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hr.le]
  rw [thetaP, Real.cos_arctan, h1, h2, rhoP]
  field_simp

lemma cos_thetaP_pos {r : ℝ} (hr : 0 < r) (z : ℝ) : 0 < Real.cos (thetaP r z) := by
  rw [cos_thetaP hr z]; exact div_pos hr (rhoP_pos hr z)

lemma thetaP_neg (r z : ℝ) : thetaP r (-z) = -thetaP r z := by
  rw [thetaP, thetaP, neg_div, Real.arctan_neg]

lemma rhoP_neg (r z : ℝ) : rhoP r (-z) = rhoP r z := by rw [rhoP, rhoP, neg_sq]

end Work.Cyl
end
end
-- ===== merged: Submission.Work.Elliptic.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The angular data -/

/-- The angular profile `sin θ cos²θ` of the solvability condition. -/
def sinCos2 (θ : ℝ) : ℝ := Real.sin θ * Real.cos θ ^ 2

/-- `K(θ) = 3 sin θ cos²θ`, the angular weight of `L₁₂` (paper §Notation). -/
def Ktheta (θ : ℝ) : ℝ := 3 * Real.sin θ * Real.cos θ ^ 2

/-- `Ktheta` is the angular weight used by the fundamental model. -/
lemma Ktheta_eq_Kpaper : Ktheta = Work.FM.Kpaper := by
  funext θ; simp only [Ktheta, Work.FM.Kpaper]

/-- `Ktheta` is the angular weight `Work.Spaces.K`. -/
lemma Ktheta_eq_K : Ktheta = Work.Spaces.K := by
  funext θ; simp only [Ktheta, Work.Spaces.K]

/-! ## The elliptic operator `L` of (PolarBSL) -/

/-- The `α = 0` part of the elliptic operator:
`L₀(Ψ) = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`.  Its kernel contains `sin 2θ` and the kernel of its
adjoint contains `sin θ cos²θ` (`Lzero_sin_two`, `LzeroAdj_sinCos2`). -/
def Lzero (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.pthIter 2 Ψ z θ)
    + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ

/-- The second derivative of a one-variable function. -/
def d2 (f : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv (fun θ' => deriv f θ') θ


/-- The elliptic operator `L` of (PolarBSL), i.e. the axi-symmetric Biot--Savart operator in
the self-similar variables `R = ρ^α`, `θ` with `ψ = ρ²Ψ(R,θ)`:
`L(Ψ) = -α²R²∂_RRΨ - α(5+α)R∂_RΨ - ∂_θθΨ + ∂_θ(tan θ Ψ) - 6Ψ`. -/
def bslOp (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
    - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ + Lzero Ψ z θ

@[simp] lemma bslOp_apply (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    bslOp α Ψ z θ = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
      - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ + Lzero Ψ z θ := rfl

/-! ## The angular moment `F_*` and the orthogonality condition -/

/-- The angular moment `F_*(z) = ∫_0^{π/2} F(z,θ) sin θ cos²θ dθ` of the paper. -/
def Fstar (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, F z θ * sinCos2 θ

/-- The solvability condition of Proposition `prop:L2`: `F_* ≡ 0`. -/
def OrthCond (F : ℝ → ℝ → ℝ) : Prop := ∀ z, Fstar F z = 0

/-- The `L₁₂` density `∫_0^{π/2} K(θ) F(s,θ) dθ / s` of the paper. -/
def L12dens (F : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, Ktheta θ * F s θ / s

/-- The integral operator `L₁₂(F)(z) = ∫_z^∞ ∫_0^{π/2} F(r,θ) K(θ)/r dθ dr` of the paper
(this is `Work.FM.L12 Work.FM.Kpaper`). -/
def L12 (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ r in Set.Ioi z, L12dens F r

/-- `L12` is the fundamental-model operator `L₁₂^K` with the paper's `K`. -/
lemma L12_eq_FM (F : ℝ → ℝ → ℝ) (z : ℝ) :
    L12 F z = Work.FM.L12 Work.FM.Kpaper F z := by
  rw [L12, Work.FM.L12]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [L12dens, Work.FM.L12dens]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by simp only [Ktheta, Work.FM.Kpaper])

/-- The radial integral `∫_z^∞ F_*(r)/r dr` in terms of which the whole singular term can be
written: `L₁₂(F)(z) = 3 ∫_z^∞ F_*(r)/r dr`. -/
def L12rad (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ r in Set.Ioi z, Fstar F r / r

/-! ## The singular term `G` of §'The singular term' -/

/-- `G_* = -(1/(4α)) L₁₂(F)`: the main term of the singular part. -/
def Gstar (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => -(1 / (4 * α)) * L12 F z

/-- The remainder `Ḡ = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(s) ds` of the singular part
(paper `\bar G`, line 1023, with the exponent corrected to `5/α`). -/
def Gbar (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => -(3 / (4 * α)) * z ^ (-(5 / α)) * ∫ s in (0 : ℝ)..z, s ^ ((5 - α) / α) * Fstar F s

/-- `G = G_* + Ḡ`, the function of §'The singular term' solving
`α²z²G'' + α(5+α)zG' = (15/4)F_*`. -/
def Gsing (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => Gstar α F z + Gbar α F z

/-- `F ↦ F - (15/4) sin 2θ · F_*(z)`: the source left after adding `G sin 2θ` to a solution;
it is orthogonal to `sin θ cos²θ` (`Fstar_residual`). -/
def orthSource (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => F z θ - (15 / 4) * Real.sin (2 * θ) * Fstar F z

/-- The residual `Ψ - (1/(4α)) sin 2θ · L₁₂(F)` of Theorem `RemovingL12`. -/
def EllResid (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ - (1 / (4 * α)) * Real.sin (2 * θ) * L12 F z

/-! ## The class of solutions the estimates are stated for -/

/-- `Ψ` solves the elliptic problem (PolarBSL) with source `F` on the open quadrant, with the
Dirichlet conditions `Ψ(z,0) = Ψ(z,π/2) = 0` and with `Ψ(z,θ) → 0` as `z → ∞`. -/
def IsBslSol (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π/2 → bslOp α Ψ z θ = F z θ) ∧
    (∀ z, Ψ z 0 = 0) ∧ (∀ z, Ψ z (π / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.DivSinDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The angular operator `D_θ = sin(2θ) ∂_θ` acting on functions of `θ` alone. -/
def Dth1 (f : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv f θ

/-- The `n`-th iterate of `Dth1`. -/
def Dth1Iter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Dth1 (Dth1Iter n f)

/-- The angular quotient `h ↦ h / sin(2θ)`. -/
def SinQ (h : ℝ → ℝ) : ℝ → ℝ := fun θ => h θ / Real.sin (2 * θ)

/-- `h` is smooth on an open neighbourhood of the closed interval `Iθ = [0, π/2]`;
this is exactly what the `θ`-slice of a `SmoothNbhd` function satisfies. -/
def SmoothSlice (h : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ h (Set.Ioo (-1) (Real.pi / 2 + 1))

@[simp] theorem Dth1Iter_zero (f : ℝ → ℝ) : Dth1Iter 0 f = f := rfl
@[simp] theorem Dth1Iter_succ (n : ℕ) (f : ℝ → ℝ) :
    Dth1Iter (n + 1) f = Dth1 (Dth1Iter n f) := rfl

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.Gbar_hardy_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted `L²` Hardy inequality behind the elliptic estimate `\bar G`

This module proves `Work.Elliptic.Gbar_hardy_lintegral`, the `L²` Hardy estimate used for the
`\bar G` piece of the singular term (Elgindi, Annals 194(3) 2021, §'The singular term').  The
argument is the classical weighted Hardy / Cauchy--Schwarz bound, carried out in two steps:

* `hardy_op_L2_pointwise`: a weighted Cauchy--Schwarz estimate at a single `z`;
* `hardy_op_L2_tonelli`: the Tonelli computation producing the constant `2/(3β-2)`.

The pointwise step is reproduced here verbatim from `hardy_operator_L2.lean` so that this module
does not depend on a module containing a `sorry`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- **Pointwise (weighted Cauchy–Schwarz) step of the Hardy inequality.**

For `β > 1`, `z > 0` and `f` with `f²` integrable on `(0,∞)`,
`(∫_0^z s^{β-1} f(s) ds)² ≤ (2 z^{β/2}/β) · ∫_0^z s^{(3β-2)/2} f(s)² ds`. -/
theorem hardy_op_L2_pointwise (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    (∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
      ≤ 2 * z ^ (β / 2) / β *
        (∫⁻ s in Set.Ioc 0 z,
          ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
  have hz0 : (0 : ℝ) ≤ z := hz.le
  have hb1 : -1 < (β - 2) / 2 := by linarith
  have hb2 : (0 : ℝ) ≤ (3 * β - 2) / 2 := by linarith
  have hb3 : (0 : ℝ) ≤ (3 * β - 2) / 4 := by linarith
  have hfz : IntegrableOn (fun s : ℝ => f s ^ 2) (Set.Ioc 0 z) :=
    hf.mono_set (fun s hs => hs.1)
  -- Step 1: the interval integral of the norm.
  have h1 : ‖∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s‖
      ≤ ∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖ :=
    intervalIntegral.norm_integral_le_integral_norm hz0
  -- Step 2: rewrite the norm integrand as a product.
  have h2 : ∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖
      = ∫ s in Set.Ioc 0 z,
          s ^ ((β - 2) / 4) * (s ^ ((3 * β - 2) / 4) * |f s|) := by
    rw [intervalIntegral.integral_of_le hz0]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s := hs.1
    have hsum : (β - 2) / 4 + (3 * β - 2) / 4 = β - 1 := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    rw [← mul_assoc, ← Real.rpow_add hs0, hsum]
  -- Step 3: `L²` Cauchy–Schwarz on `(0,z]`.
  have hAESu : AEStronglyMeasurable (fun s : ℝ => s ^ ((β - 2) / 4))
      (volume.restrict (Set.Ioc 0 z)) := by
    refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioc
    exact (Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs.1))).continuousWithinAt
  have hu_mem : MemLp (fun s : ℝ => s ^ ((β - 2) / 4)) 2 (volume.restrict (Set.Ioc 0 z)) := by
    rw [memLp_two_iff_integrable_sq hAESu]
    refine IntegrableOn.congr_fun (f := fun s : ℝ => s ^ ((β - 2) / 2)) ?_ ?_ measurableSet_Ioc
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hz0).mp
        (intervalIntegral.intervalIntegrable_rpow' hb1)
    · intro s hs
      change s ^ ((β - 2) / 2) = (s ^ ((β - 2) / 4)) ^ 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]
      congr 1
      ring
  have hAESv : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 4) * |f s|)
      (volume.restrict (Set.Ioc 0 z)) := by
    have hs1 : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 4))
        (volume.restrict (Set.Ioc 0 z)) :=
      (Real.continuous_rpow_const hb3).aestronglyMeasurable
    have hs2 : AEStronglyMeasurable (fun s : ℝ => |f s|) (volume.restrict (Set.Ioc 0 z)) := by
      have h0 : AEMeasurable (fun s : ℝ => Real.sqrt (f s ^ 2))
          (volume.restrict (Set.Ioc 0 z)) := hfz.aestronglyMeasurable.aemeasurable.sqrt
      refine h0.aestronglyMeasurable.congr ?_
      exact Filter.Eventually.of_forall (fun s => Real.sqrt_sq_eq_abs (f s))
    exact hs1.mul hs2
  have hv_mem : MemLp (fun s : ℝ => s ^ ((3 * β - 2) / 4) * |f s|) 2
      (volume.restrict (Set.Ioc 0 z)) := by
    rw [memLp_two_iff_integrable_sq hAESv]
    refine IntegrableOn.congr_fun
      (f := fun s : ℝ => s ^ ((3 * β - 2) / 2) * f s ^ 2) ?_ ?_ measurableSet_Ioc
    · refine Integrable.mono' (hfz.const_mul (z ^ ((3 * β - 2) / 2))) ?_ ?_
      · have hs1 : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 2))
            (volume.restrict (Set.Ioc 0 z)) :=
          (Real.continuous_rpow_const hb2).aestronglyMeasurable
        exact hs1.mul hfz.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hs0 : 0 < s := hs.1
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) (sq_nonneg _))]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact Real.rpow_le_rpow hs0.le hs.2 hb2
    · intro s hs
      change s ^ ((3 * β - 2) / 2) * f s ^ 2 = (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
      have hB : (s ^ ((3 * β - 2) / 4)) ^ 2 = s ^ ((3 * β - 2) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]
        congr 1
        ring
      rw [mul_pow, sq_abs, hB]
  have hcs := Work.Spaces.cs_integral hu_mem hv_mem
  -- Step 4: the two integrals.
  have hu2 : ∫ s in Set.Ioc 0 z, (s ^ ((β - 2) / 4)) ^ 2 = 2 * z ^ (β / 2) / β := by
    have hB : ∀ s : ℝ, 0 < s → (s ^ ((β - 2) / 4)) ^ 2 = s ^ ((β - 2) / 2) := by
      intro s hs
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      congr 1
      ring
    have hcongr : ∫ s in Set.Ioc 0 z, (s ^ ((β - 2) / 4)) ^ 2
        = ∫ s in (0 : ℝ)..z, s ^ ((β - 2) / 2) := by
      rw [intervalIntegral.integral_of_le hz0]
      exact setIntegral_congr_fun measurableSet_Ioc (fun s hs => hB s hs.1)
    rw [hcongr, integral_rpow (Or.inl hb1)]
    rw [show (β - 2) / 2 + 1 = β / 2 by ring]
    rw [Real.zero_rpow (by positivity : (β / 2) ≠ 0)]
    have hb0 : β ≠ 0 := by linarith
    field_simp
    ring_nf
  have hv2 : ∫ s in Set.Ioc 0 z, (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
      = (∫⁻ s in Set.Ioc 0 z,
          ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
    have hB : ∀ s : ℝ, 0 < s → (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
        = s ^ ((3 * β - 2) / 2) * f s ^ 2 := by
      intro s hs
      have hB' : (s ^ ((3 * β - 2) / 4)) ^ 2 = s ^ ((3 * β - 2) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
        congr 1
        ring
      rw [mul_pow, sq_abs, hB']
    have hcongr : ∫ s in Set.Ioc 0 z, (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
        = ∫ s in Set.Ioc 0 z, s ^ ((3 * β - 2) / 2) * f s ^ 2 :=
      setIntegral_congr_fun measurableSet_Ioc (fun s hs => hB s hs.1)
    rw [hcongr]
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 z)]
        (fun s : ℝ => s ^ ((3 * β - 2) / 2) * f s ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_nonneg (Real.rpow_nonneg hs.1.le _) (sq_nonneg _)
    have hAES : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 2) * f s ^ 2)
        (volume.restrict (Set.Ioc 0 z)) := by
      have hs1 : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 2))
          (volume.restrict (Set.Ioc 0 z)) :=
        (Real.continuous_rpow_const hb2).aestronglyMeasurable
      exact hs1.mul hfz.aestronglyMeasurable
    exact integral_eq_lintegral_of_nonneg_ae hnn hAES
  -- Assemble.
  have hI0 : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖ :=
    intervalIntegral.integral_nonneg hz0 (fun s _ => norm_nonneg _)
  have hsq : (‖∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s‖) ^ 2
      ≤ (∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc (∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
      = ‖∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
    _ ≤ (∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖) ^ 2 := hsq
    _ = (∫ s in Set.Ioc 0 z,
          s ^ ((β - 2) / 4) * (s ^ ((3 * β - 2) / 4) * |f s|)) ^ 2 := by rw [h2]
    _ ≤ (∫ s in Set.Ioc 0 z, (s ^ ((β - 2) / 4)) ^ 2)
          * (∫ s in Set.Ioc 0 z, (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2) := hcs
    _ = 2 * z ^ (β / 2) / β *
          (∫⁻ s in Set.Ioc 0 z,
            ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by rw [hu2, hv2]



/-! ## The Tonelli step -/

/-- The iterated integral `∫₀^∞ z^{-3β/2} ∫₀^z s^{(3β-2)/2} f(s)² ds dz` evaluated by Tonelli. -/
theorem hardy_op_L2_tonelli (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)))
      = ENNReal.ofReal (2 / (3 * β - 2) * ∫ z in Set.Ioi (0 : ℝ), f z ^ 2) := by
  have hβ2 : (0:ℝ) < 3 * β - 2 := by linarith
  have ha1 : (1:ℝ) < 3 * β / 2 := by linarith
  have hc1 : (0:ℝ) < 3 * β / 2 - 1 := by linarith
  have hAmeas : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ (-(3 * β / 2)))) := by fun_prop
  have hHae : AEMeasurable (fun s : ℝ => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply AEMeasurable.ennreal_ofReal
    exact ((by fun_prop : Measurable (fun s : ℝ => s ^ ((3 * β - 2) / 2))).aemeasurable).mul
      hf.aestronglyMeasurable.aemeasurable
  have hres : ∀ z, (volume.restrict (Set.Ioi (0:ℝ))).restrict (Set.Ioc 0 z)
      = volume.restrict (Set.Ioc 0 z) := by
    intro z
    rw [Measure.restrict_restrict measurableSet_Ioc]
    congr 1
    exact Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self
  have hA : (∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)))
      = ∫⁻ z in Set.Ioi (0:ℝ), ∫⁻ s in Set.Ioi (0:ℝ),
          ENNReal.ofReal (z ^ (-(3 * β / 2))) *
            (Set.Ioc 0 z).indicator (fun s => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) s := by
    refine lintegral_congr fun z => ?_
    have h1 : ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)
        = ∫⁻ s, (Set.Ioc 0 z).indicator
            (fun s => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) s
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
      rw [lintegral_indicator measurableSet_Ioc, hres]
    rw [h1]
    exact (lintegral_const_mul'' _ (hHae.indicator measurableSet_Ioc)).symm
  rw [hA]
  have hUnc : AEMeasurable (Function.uncurry (fun z s => ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s))
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    have hfst : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(3 * β / 2)))) :=
      hAmeas.comp measurable_fst
    have hsnd : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ ((3 * β - 2) / 2) * f p.2 ^ 2))
        ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) :=
      hHae.comp_snd
    have hS : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1} := by
      have h1 : MeasurableSet {p : ℝ × ℝ | (0:ℝ) < p.2} := measurableSet_Ioi.preimage measurable_snd
      have h2 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := by
        rw [show {p : ℝ × ℝ | p.2 ≤ p.1} = (fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' Set.Ici (0:ℝ) from by
          ext p; simp [sub_nonneg]]
        exact measurableSet_Ici.preimage (measurable_fst.sub measurable_snd)
      have he : {p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1} = {p | (0:ℝ) < p.2} ∩ {p | p.2 ≤ p.1} := by
        ext p; simp [Set.mem_Ioc]
      rw [he]; exact h1.inter h2
    have h2' : AEMeasurable (fun p : ℝ × ℝ => Set.indicator {q : ℝ × ℝ | q.2 ∈ Set.Ioc 0 q.1}
        (fun q => ENNReal.ofReal (q.2 ^ ((3 * β - 2) / 2) * f q.2 ^ 2)) p)
        ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) :=
      hsnd.indicator hS
    refine (hfst.aemeasurable.mul h2').congr ?_
    filter_upwards with p
    rfl
  rw [lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (ν := volume.restrict (Set.Ioi (0:ℝ)))
      (f := fun z s => ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s) hUnc]
  have hC : ∀ s, (∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s)
      = (Set.Ioi (0:ℝ)).indicator (fun s => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2) *
          (∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-(3 * β / 2))))) s := by
    intro s
    by_cases hs : s ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem hs]
      have hs0 : 0 < s := hs
      have hind : ∀ z, (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s
          = (Set.Ici s).indicator (fun _ => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) z := by
        intro z
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases h : s ≤ z
        · rw [if_pos (Set.mem_Ioc.mpr ⟨hs0, h⟩), if_pos (Set.mem_Ici.mpr h)]
        · rw [if_neg (fun hc => h (Set.mem_Ioc.mp hc).2), if_neg (fun hc => h (Set.mem_Ici.mp hc))]
      have hind2 : ∀ z, ENNReal.ofReal (z ^ (-(3 * β / 2))) *
            (Set.Ici s).indicator (fun _ => ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) z
          = (Set.Ici s).indicator (fun z => ENNReal.ofReal (z ^ (-(3 * β / 2))) *
                ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) z := by
        intro z
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases h : z ∈ Set.Ici s
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, mul_zero]
      have e1 : (∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
            (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s)
          = ∫⁻ z in Set.Ioi (0:ℝ), (Set.Ici s).indicator (fun z => ENNReal.ofReal (z ^ (-(3 * β / 2))) *
              ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) z := by
        rw [lintegral_congr (fun z => by rw [hind z, hind2 z])]
      rw [e1, ← lintegral_indicator measurableSet_Ioi]
      have hst2 : (∫⁻ z, (Set.Ioi (0:ℝ)).indicator ((Set.Ici s).indicator
              (fun z => ENNReal.ofReal (z ^ (-(3 * β / 2))) * ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) z)
          = ∫⁻ z, (Set.Ici s).indicator
              (fun z => ENNReal.ofReal (z ^ (-(3 * β / 2))) * ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)) z := by
        refine lintegral_congr (fun z => ?_)
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases hz : z ∈ Set.Ioi (0:ℝ)
        · rw [if_pos hz]
        · rw [if_neg hz, if_neg (fun hc => hz (hs0.trans_le (Set.mem_Ici.mp hc)))]
      rw [hst2, lintegral_indicator measurableSet_Ici]
      rw [lintegral_mul_const'' _ hAmeas.aemeasurable, mul_comm]
    · rw [Set.indicator_of_notMem hs]
      have hind : ∀ z, (Set.Ioc 0 z).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) s = 0 := by
        intro z
        rw [Set.indicator_of_notMem]
        intro hc; exact hs (Set.mem_Ioc.mp hc).1
      rw [lintegral_congr (fun z => by rw [hind z, mul_zero])]
      simp
  have hE : ∀ s ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2) * ENNReal.ofReal (s ^ (1 - 3 * β / 2) / (3 * β / 2 - 1))
        = ENNReal.ofReal (1 / (3 * β / 2 - 1)) * ENNReal.ofReal (f s ^ 2) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hp : (0:ℝ) ≤ s ^ ((3 * β - 2) / 2) * f s ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hs0.le _) (sq_nonneg _)
    rw [← ENNReal.ofReal_mul hp]
    have hkey : s ^ ((3 * β - 2) / 2) * s ^ (1 - 3 * β / 2) = 1 := by
      rw [← Real.rpow_add hs0, show (3 * β - 2) / 2 + (1 - 3 * β / 2) = 0 by ring, Real.rpow_zero]
    have harg : s ^ ((3 * β - 2) / 2) * f s ^ 2 * (s ^ (1 - 3 * β / 2) / (3 * β / 2 - 1))
        = 1 / (3 * β / 2 - 1) * f s ^ 2 := by
      calc s ^ ((3 * β - 2) / 2) * f s ^ 2 * (s ^ (1 - 3 * β / 2) / (3 * β / 2 - 1))
          = (s ^ ((3 * β - 2) / 2) * s ^ (1 - 3 * β / 2)) * (f s ^ 2 / (3 * β / 2 - 1)) := by ring
        _ = 1 * (f s ^ 2 / (3 * β / 2 - 1)) := by rw [hkey]
        _ = 1 / (3 * β / 2 - 1) * f s ^ 2 := by ring
    rw [harg, ENNReal.ofReal_mul (le_of_lt (div_pos one_pos hc1))]
  calc ∫⁻ y in Set.Ioi (0:ℝ), ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (x ^ (-(3 * β / 2))) *
        (Set.Ioc 0 x).indicator (fun t => ENNReal.ofReal (t ^ ((3 * β - 2) / 2) * f t ^ 2)) y
      = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2) *
          (∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-(3 * β / 2)))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
        rw [hC s, Set.indicator_of_mem hs]
    _ = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2) *
          ENNReal.ofReal (s ^ (1 - 3 * β / 2) / (3 * β / 2 - 1)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
        rw [lintegral_Ici_ofReal_rpow ha1 hs]
    _ = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (1 / (3 * β / 2 - 1)) * ENNReal.ofReal (f s ^ 2) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => hE s hs)
    _ = ENNReal.ofReal (1 / (3 * β / 2 - 1)) * ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (f s ^ 2) := by
        rw [lintegral_const_mul'' _ (hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    _ = ENNReal.ofReal (1 / (3 * β / 2 - 1)) * ENNReal.ofReal (∫ s in Set.Ioi (0:ℝ), f s ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall (fun s => sq_nonneg (f s)))]
    _ = ENNReal.ofReal (1 / (3 * β / 2 - 1) * ∫ s in Set.Ioi (0:ℝ), f s ^ 2) := by
        rw [ENNReal.ofReal_mul (le_of_lt (div_pos one_pos hc1))]
    _ = ENNReal.ofReal (2 / (3 * β - 2) * ∫ s in Set.Ioi (0:ℝ), f s ^ 2) := by
        congr 1
        rw [show 1 / (3 * β / 2 - 1) = 2 / (3 * β - 2) by
          rw [div_eq_div_iff (by linarith) (by linarith)]; ring]

/-! ## The target estimate -/


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.HardyRightNoCont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Two private auxiliary lemmas -/

/-- **Weighted Hardy bound on a right tail.**  For `U` differentiable on `(1,∞)`, vanishing at
`+∞`, with `(t U'(t))²` integrable there, and every `z > 1`,
`U(z)² ≤ 2 z^{-1/2} ∫_z^∞ (t U'(t))² t^{-1/2} dt`.

This is the sharp weighted Hardy inequality on a tail: the proof is
`U(z) = -∫_z^∞ U'` (fundamental theorem of calculus on the half line) followed by
Cauchy–Schwarz applied to `U'(t) = (t U'(t) · t^{-1/4}) · t^{-3/4}` together with
`∫_z^∞ t^{-3/2} dt = 2 z^{-1/2}`. -/
private theorem hardy_right_tail_pw (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (1:ℝ), HasDerivAt U (U' z) z)
    (htend : Filter.Tendsto U Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (z * U' z) ^ 2) (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (1:ℝ),
      MeasureTheory.IntegrableOn U' (Set.Ioi z) ∧
      (U z) ^ 2 ≤ 2 * z ^ (-(1/2:ℝ)) *
        ∫ t in Set.Ioi z, (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) := by
  intro z hz
  have hz1 : (1:ℝ) < z := hz
  have hzpos : (0:ℝ) < z := lt_trans one_pos hz1
  -- The weighted square `(t U' t)² t^{-1/2}` is integrable on `(1,∞)`: on `(1,∞)` the extra
  -- weight `t^{-1/2}` is at most `1`, so it is dominated by the integrable `(t U' t)²`.
  have hG1 : IntegrableOn (fun t : ℝ => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ))) (Set.Ioi 1) := by
    have hAESM : AEStronglyMeasurable (fun t : ℝ => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)))
        (volume.restrict (Set.Ioi (1:ℝ))) := by
      have h1 : AEStronglyMeasurable (fun t : ℝ => (t * U' t) ^ 2)
          (volume.restrict (Set.Ioi (1:ℝ))) := hint.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-(1/2:ℝ)))
          (volume.restrict (Set.Ioi (1:ℝ))) :=
        (continuousOn_id.rpow_const
          (fun t ht => Or.inl (ne_of_gt (lt_trans one_pos (mem_Ioi.mp ht))))).aestronglyMeasurable
          measurableSet_Ioi
      exact h1.mul h2
    refine hint.mono' hAESM ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : (0:ℝ) < t := lt_trans one_pos (mem_Ioi.mp ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg htp.le _))]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt (mem_Ioi.mp ht))
      (show (-(1/2:ℝ)) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  have hGz : IntegrableOn (fun t : ℝ => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ))) (Set.Ioi z) :=
    hG1.mono_set (Ioi_subset_Ioi hz1.le)
  -- `U'` agrees with `deriv U` on `(z,∞)`, hence is a.e. strongly measurable there.
  have hU'meas : AEStronglyMeasurable U' (volume.restrict (Set.Ioi z)) := by
    have hd : AEStronglyMeasurable (deriv U) (volume.restrict (Set.Ioi z)) :=
      (measurable_deriv U).aestronglyMeasurable
    refine hd.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hderiv t (mem_Ioi.mpr (lt_trans hz1 (mem_Ioi.mp ht)))).deriv
  have hU'int : IntegrableOn U' (Set.Ioi z) :=
    integrableOn_tail_of_weighted z hzpos U' hU'meas hGz
  refine ⟨hU'int, ?_⟩
  -- Splitting `U'(t) = (t U'(t) · t^{-1/4}) · t^{-3/4}`.
  set u : ℝ → ℝ := fun t => (t * U' t) * t ^ (-(1/4:ℝ)) with hu
  set v : ℝ → ℝ := fun t => t ^ (-(3/4:ℝ)) with hv
  have hzmem : ∀ t ∈ Set.Ioi z, (0:ℝ) < t := fun t ht => lt_trans hzpos ht
  have hu_sq : ∀ t ∈ Set.Ioi z, u t ^ 2 = (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) := by
    intro t ht
    have htpos := hzmem t ht
    have hb : (t ^ (-(1/4:ℝ))) ^ 2 = t ^ (-(1/2:ℝ)) := by
      rw [pow_two, ← Real.rpow_add htpos]; norm_num
    simp only [hu, mul_pow, hb]
  have hv_sq : ∀ t ∈ Set.Ioi z, v t ^ 2 = t ^ (-(3/2:ℝ)) := by
    intro t ht
    have htpos := hzmem t ht
    simp only [hv]
    rw [pow_two, ← Real.rpow_add htpos]
    norm_num
  have huv : ∀ t ∈ Set.Ioi z, u t * v t = U' t := by
    intro t ht
    have htpos := hzmem t ht
    have hb : t ^ (-(1/4:ℝ)) * t ^ (-(3/4:ℝ)) = t⁻¹ := by
      rw [← Real.rpow_add htpos]; norm_num; rw [Real.rpow_neg_one]
    have htne : t ≠ 0 := ne_of_gt htpos
    simp only [hu, hv]
    rw [mul_assoc, hb]
    field_simp
  have hu_aesm : AEStronglyMeasurable u (volume.restrict (Set.Ioi z)) := by
    rw [hu]
    exact ((measurable_id.aestronglyMeasurable).mul hU'meas).mul
      ((continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (hzmem t ht)))).aestronglyMeasurable measurableSet_Ioi)
  have hu_mem : MemLp u 2 (volume.restrict (Set.Ioi z)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hu_aesm]
    refine hGz.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hu_sq t ht).symm
  have hv_aesm : AEStronglyMeasurable v (volume.restrict (Set.Ioi z)) := by
    rw [hv]
    exact (continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (hzmem t ht)))).aestronglyMeasurable measurableSet_Ioi
  have hv_mem : MemLp v 2 (volume.restrict (Set.Ioi z)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hv_aesm]
    have hbase : Integrable (fun t : ℝ => t ^ (-(3/2:ℝ))) (volume.restrict (Set.Ioi z)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ)) < -1) hzpos
    refine hbase.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hv_sq t ht).symm
  have hcs := Work.Spaces.cs_integral hu_mem hv_mem
  rw [setIntegral_congr_fun measurableSet_Ioi huv,
      setIntegral_congr_fun measurableSet_Ioi hu_sq,
      setIntegral_congr_fun measurableSet_Ioi hv_sq,
      integral_Ioi_rpow_neg_three_halves z hzpos] at hcs
  -- The fundamental theorem of calculus on `(z,∞)`: `∫_z^∞ U' = 0 - U z`.
  have hFTC : ∫ t in Set.Ioi z, U' t = - U z := by
    have hcont : ContinuousWithinAt U (Set.Ici z) z :=
      (hderiv z hz).continuousAt.continuousWithinAt
    have hd : ∀ x ∈ Set.Ioi z, HasDerivAt U (U' x) x :=
      fun x hx => hderiv x (mem_Ioi.mpr (lt_trans hz1 (mem_Ioi.mp hx)))
    have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hU'int htend
    simpa using key
  calc (U z) ^ 2 = (∫ t in Set.Ioi z, U' t) ^ 2 := by rw [hFTC]; ring
    _ ≤ (∫ t in Set.Ioi z, (t * U' t) ^ 2 * t ^ (-(1/2:ℝ))) * (2 * z ^ (-(1/2:ℝ))) := hcs
    _ = 2 * z ^ (-(1/2:ℝ)) * ∫ t in Set.Ioi z, (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) := by ring

/-- **Lintegral bound for `ofReal` gives Bochner integrability.**  If `f ≥ 0` a.e. is
a.e. strongly measurable on `(1,∞)` and `∫⁻ ofReal (f z) ≤ ofReal c` with `c ≥ 0`, then
`f` is integrable on `(1,∞)` and `∫ f ≤ c`. -/
private theorem integrable_of_lintegral_ofReal_le (f : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hmeas : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi (1:ℝ))))
    (hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1:ℝ))] f)
    (h : ∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (f z) ≤ ENNReal.ofReal c) :
    MeasureTheory.IntegrableOn f (Set.Ioi (1:ℝ)) ∧
      ∫ z in Set.Ioi (1:ℝ), f z ≤ c := by
  have hne : (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (f z)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hint : IntegrableOn f (Set.Ioi (1:ℝ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnn).mp hne
  refine ⟨hint, ?_⟩
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  calc (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (f z)).toReal
      ≤ (ENNReal.ofReal c).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = c := ENNReal.toReal_ofReal hc

/-! ## The Hardy inequality on the right half-line -/

theorem HardyRightNoCont (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (1 : ℝ), HasDerivAt U (U' z) z)
    (htend : Filter.Tendsto U Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (z * U' z) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => U z ^ 2) (Set.Ioi 1) ∧
      ∫ z in Set.Ioi (1 : ℝ), U z ^ 2 ≤ 6 * ∫ z in Set.Ioi (1 : ℝ), (z * U' z) ^ 2 := by
  -- Abbreviations.
  set phi : ℝ → ℝ := fun t => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) with hphi
  set G : ℝ → ℝ := fun z => (z * U' z) ^ 2 with hG
  set gg : ℝ → ℝ := fun t => (t * deriv U t) ^ 2 * (Real.sqrt t)⁻¹ with hgg
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal (gg t) with hf
  -- `U'` coincides with `deriv U` on `(1,∞)`.
  have hU'eq : ∀ t ∈ Set.Ioi (1:ℝ), U' t = deriv U t :=
    fun t ht => (hderiv t ht).deriv.symm
  -- Measurability of `gg` and `f`.
  have hgg_meas : Measurable gg := by
    rw [hgg]
    exact ((measurable_id.mul (measurable_deriv U)).pow_const 2).mul
      (Real.continuous_sqrt.measurable.inv)
  have hf_meas : Measurable f := by
    rw [hf]; exact ENNReal.continuous_ofReal.measurable.comp hgg_meas
  -- `phi` and `gg` agree on `(1,∞)`.
  have hphigg : ∀ t ∈ Set.Ioi (1:ℝ), phi t = gg t := by
    intro t ht
    have htpos : 0 < t := lt_trans one_pos ht
    simp only [hphi, hgg]
    rw [hU'eq t ht]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_neg htpos.le]
  have htail := hardy_right_tail_pw U U' hderiv htend hint
  -- Per-`z` bound in `ℝ≥0∞`.
  have hpt : ∀ z ∈ Set.Ioi (1:ℝ),
      ENNReal.ofReal (U z ^ 2)
        ≤ ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * (∫⁻ t in Set.Ioi z, f t) := by
    intro z hz
    have hz1 : (1:ℝ) < z := mem_Ioi.mp hz
    have hzpos : (0:ℝ) < z := lt_trans one_pos hz1
    obtain ⟨_hU'int, hbound⟩ := htail z hz
    have hbound' : (U z) ^ 2 ≤ 2 * z ^ (-(1/2:ℝ)) * ∫ t in Set.Ioi z, phi t := hbound
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi z)] phi := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans hzpos (mem_Ioi.mp ht)
      rw [hphi]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg htpos.le _)
    have hmeas : AEStronglyMeasurable phi (volume.restrict (Set.Ioi z)) := by
      have hcongr : gg =ᵐ[volume.restrict (Set.Ioi z)] phi := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hphigg t (lt_trans hz1 (mem_Ioi.mp ht))).symm
      exact hgg_meas.aestronglyMeasurable.congr hcongr
    have hint_eq : (∫ t in Set.Ioi z, phi t) = (∫⁻ t in Set.Ioi z, f t).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
      congr 1
      refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [hf]
      congr 1
      exact hphigg t (lt_trans hz1 (mem_Ioi.mp ht))
    have hc : 0 ≤ 2 * z ^ (-(1/2:ℝ)) := by positivity
    calc ENNReal.ofReal (U z ^ 2)
        ≤ ENNReal.ofReal (2 * z ^ (-(1/2:ℝ)) * ∫ t in Set.Ioi z, phi t) :=
          ENNReal.ofReal_le_ofReal hbound'
      _ = ENNReal.ofReal (2 * z ^ (-(1/2:ℝ)) * (∫⁻ t in Set.Ioi z, f t).toReal) := by
          rw [hint_eq]
      _ = ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) *
            ENNReal.ofReal ((∫⁻ t in Set.Ioi z, f t).toReal) :=
          ENNReal.ofReal_mul hc
      _ ≤ ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * (∫⁻ t in Set.Ioi z, f t) :=
          mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le bot_le
  have hstep1 : (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (U z ^ 2))
      ≤ ∫⁻ z in Set.Ioi (1:ℝ),
          ENNReal.ofReal (2 * z ^ (-(1/2:ℝ))) * (∫⁻ t in Set.Ioi z, f t) :=
    setLIntegral_mono' measurableSet_Ioi hpt
  have hstep2 := HardyRightTonelliSwap f hf_meas
  have hGint : IntegrableOn G (Set.Ioi (1:ℝ)) := by rw [hG]; exact hint
  have hpt2 : ∀ t ∈ Set.Ioi (1:ℝ), f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1))
      ≤ ENNReal.ofReal (4 * G t) := by
    intro t ht
    have ht1 : (1:ℝ) < t := mem_Ioi.mp ht
    have htpos : (0:ℝ) < t := lt_trans one_pos ht1
    have hggnn : 0 ≤ gg t := by
      rw [hgg]
      exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg t))
    rw [hf, ← ENNReal.ofReal_mul hggnn]
    apply ENNReal.ofReal_le_ofReal
    simp only [hgg, hG]
    rw [hU'eq t ht, Real.sqrt_eq_rpow]
    have h1 : (0:ℝ) ≤ t ^ (1/2:ℝ) := Real.rpow_nonneg htpos.le _
    have hpos : 0 < t ^ (1/2:ℝ) := Real.rpow_pos_of_pos htpos _
    have hkey : (t ^ (1/2:ℝ))⁻¹ * (t ^ (1/2:ℝ) - 1) = 1 - (t ^ (1/2:ℝ))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hpos.ne', mul_one]
    have hle1 : 1 - (t ^ (1/2:ℝ))⁻¹ ≤ 1 := sub_le_self _ (inv_nonneg.mpr h1)
    have heq : (t * deriv U t) ^ 2 * (t ^ (1/2:ℝ))⁻¹ * (4 * (t ^ (1/2:ℝ) - 1))
        = 4 * (t * deriv U t) ^ 2 * (1 - (t ^ (1/2:ℝ))⁻¹) := by
      rw [← hkey]; ring
    rw [heq]
    calc 4 * (t * deriv U t) ^ 2 * (1 - (t ^ (1/2:ℝ))⁻¹)
        ≤ 4 * (t * deriv U t) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hle1 (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = 4 * (t * deriv U t) ^ 2 := by ring
  have hstep3 : (∫⁻ t in Set.Ioi (1:ℝ), f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1)))
      ≤ ENNReal.ofReal (4 * ∫ z in Set.Ioi (1:ℝ), G z) := by
    have h4Gnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] (fun t => 4 * G t) :=
      Filter.Eventually.of_forall (fun t => mul_nonneg (by norm_num) (by rw [hG]; exact sq_nonneg _))
    calc (∫⁻ t in Set.Ioi (1:ℝ), f t * ENNReal.ofReal (4 * (t ^ ((1/2:ℝ)) - 1)))
        ≤ ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (4 * G t) :=
          setLIntegral_mono' measurableSet_Ioi hpt2
      _ = ENNReal.ofReal (∫ t in Set.Ioi (1:ℝ), 4 * G t) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hGint.const_mul (4:ℝ)) h4Gnn).symm
      _ = ENNReal.ofReal (4 * ∫ z in Set.Ioi (1:ℝ), G z) := by
          rw [MeasureTheory.integral_const_mul]
  have hmain : (∫⁻ z in Set.Ioi (1:ℝ), ENNReal.ofReal (U z ^ 2))
      ≤ ENNReal.ofReal (4 * ∫ z in Set.Ioi (1:ℝ), G z) :=
    le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
  have hUon : ContinuousOn U (Set.Ioi (1:ℝ)) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hU2_aesm : AEStronglyMeasurable (fun z => U z ^ 2) (volume.restrict (Set.Ioi (1:ℝ))) :=
    (hUon.pow 2).aestronglyMeasurable measurableSet_Ioi
  have hU2_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] (fun z => U z ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg _)
  have hGnn : 0 ≤ ∫ z in Set.Ioi (1:ℝ), G z :=
    integral_nonneg (fun z => by rw [hG]; exact sq_nonneg _)
  have hc4 : 0 ≤ 4 * ∫ z in Set.Ioi (1:ℝ), G z := by linarith
  obtain ⟨hintU2, hle4⟩ :=
    integrable_of_lintegral_ofReal_le (fun z => U z ^ 2) (4 * ∫ z in Set.Ioi (1:ℝ), G z) hc4
      hU2_aesm hU2_nn hmain
  refine ⟨hintU2, ?_⟩
  have hGeq : (∫ z in Set.Ioi (1:ℝ), G z) = ∫ z in Set.Ioi (1:ℝ), (z * U' z) ^ 2 := by
    simp only [hG]
  rw [hGeq] at hle4
  have hX : 0 ≤ ∫ z in Set.Ioi (1:ℝ), (z * U' z) ^ 2 :=
    integral_nonneg (fun z => sq_nonneg _)
  linarith

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.HardyRightTail =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.IntegrableSqMulW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set Filter
open scoped Real Topology

/-- On `(1,∞)` the weight `w(z) = (1+z)²/z²` is at least `1`. -/
private lemma one_le_w_of_one_lt_prv {z : ℝ} (hz : 1 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  rw [one_le_div (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [sq_nonneg (1 + z), sq_nonneg z]

/-- If `f² w²` is integrable on `(1,∞)`, so is `f²`, with no larger integral. -/
theorem IntegrableSqMulW {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (f z) ^ 2) (Set.Ioi 1) ∧
      ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2
        ≤ ∫ z in Set.Ioi (1 : ℝ), (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  have hw_meas : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
    have h : Measurable (fun z : ℝ => Work.Spaces.w z) := by
      simp only [Work.Spaces.w]
      fun_prop
    exact h.pow_const 2
  -- pointwise bound on `(1,∞)`: `f² ≤ f² · w²`
  have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      (f z) ^ 2 ≤ (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ (one_le_w_of_one_lt_prv hz))
  -- on `(1,∞)`, `f² = (f² w²)/w²`
  have heq : (fun z : ℝ => (f z) ^ 2 * (Work.Spaces.w z) ^ 2 / (Work.Spaces.w z) ^ 2)
      =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] (fun z : ℝ => (f z) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have := one_le_w_of_one_lt_prv hz
      positivity
    exact mul_div_cancel_right₀ _ hw
  have hf2_meas : AEStronglyMeasurable (fun z : ℝ => (f z) ^ 2)
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (hint.aestronglyMeasurable.div₀ hw_meas.aestronglyMeasurable).congr heq
  have hf2 : Integrable (fun z : ℝ => (f z) ^ 2) (volume.restrict (Set.Ioi (1 : ℝ))) :=
    hint.mono' hf2_meas (hpt.mono fun z hz => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hz)
  refine ⟨hf2, ?_⟩
  exact integral_mono_ae hf2 hint hpt

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.WtoWAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedVariables false










end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.WtoW_Dth_mul_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic


end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.WtoW_f_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false


end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.WtoW_g_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The bounded angular function `X = ∂_θ(sin 2·) = 2 cos 2θ`. -/
def WtoW_X : ℝ → ℝ := fun θ => 2 * Real.cos (2 * θ)

/-- The integer coefficients `(A_{q,j}, B_{q,j})` of the expansion
`c_{q,j} = A_{q,j} + B_{q,j} X`: `A_{q+1,j} = A_{q,j-1} - 4B_{q,j}`,
`B_{q+1,j} = B_{q,j-1} - A_{q,j}`, `(A_{0,0},B_{0,0}) = (1,0)`. -/
def WtoW_AB : ℕ → ℕ → ℤ × ℤ
  | 0, j => if j = 0 then (1, 0) else (0, 0)
  | (q + 1), j =>
      let a : ℤ := if j = 0 then 0 else (WtoW_AB q (j - 1)).1
      let b : ℤ := if j = 0 then 0 else (WtoW_AB q (j - 1)).2
      (a - 4 * (WtoW_AB q j).2, b - (WtoW_AB q j).1)

/-- The real part of the coefficient `c_{q,j}`. -/
def WtoW_cA (q j : ℕ) : ℝ := ((WtoW_AB q j).1 : ℝ)

/-- The coefficient of `X` in the coefficient `c_{q,j}`. -/
def WtoW_cB (q j : ℕ) : ℝ := ((WtoW_AB q j).2 : ℝ)

/-- The angular coefficient `c_{q,j}(θ) = A_{q,j} + B_{q,j}·2cos(2θ)`. -/
def WtoW_ccoeff (q j : ℕ) : ℝ → ℝ := fun θ => WtoW_cA q j + WtoW_cB q j * WtoW_X θ

@[simp] theorem WtoW_cA_zero_zero : WtoW_cA 0 0 = 1 := by
  simp [WtoW_cA, WtoW_AB]
@[simp] theorem WtoW_cB_zero_zero : WtoW_cB 0 0 = 0 := by
  simp [WtoW_cB, WtoW_AB]



@[simp] theorem WtoW_ccoeff_zero_zero : WtoW_ccoeff 0 0 = fun _ => 1 := by
  funext θ
  simp [WtoW_ccoeff]

end Work.Elliptic
end
end
-- ===== merged: Submission.Work.Elliptic.contDiffOn_one_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- A `C¹` function on `[0, π/2]` vanishing at both endpoints satisfies a bound of the
form `|f θ| ≤ C * min θ (π/2 - θ)` with the same constant `C` bounding the derivative.
The constant is the maximum of `‖derivWithin f [0, π/2]‖`, which is finite because the
one-sided derivative is continuous on the compact interval. -/
theorem contDiffOn_one_bounds {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0)
    (hpi : f (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ θ ∈ Set.Icc 0 (Real.pi / 2), |f θ| ≤ C * min θ (Real.pi / 2 - θ)) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖deriv f θ‖ ≤ C) := by
  have hpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hUniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (Real.pi / 2)) := uniqueDiffOn_Icc hpos
  have hcont : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) (Real.pi / 2)))
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := hf.continuousOn_derivWithin hUniq le_rfl
  obtain ⟨x₀, hx₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hpos.le⟩⟩ hcont.norm
  let M : ℝ := ‖derivWithin f (Set.Icc (0 : ℝ) (Real.pi / 2)) x₀‖
  have hMnonneg : 0 ≤ M := norm_nonneg _
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt f (derivWithin f (Set.Icc (0 : ℝ) (Real.pi / 2)) x)
        (Set.Icc (0 : ℝ) (Real.pi / 2)) x := by
    intro x hx
    exact ((hf.contDiffWithinAt hx).differentiableWithinAt one_ne_zero).hasDerivWithinAt
  have hsub : ∀ {a b : ℝ}, a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      Set.Icc a b ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro a b ha hb
    exact Set.Icc_subset_Icc ha.1 hb.2
  have key : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → ∀ θ ∈ Set.Icc a b,
      ‖f θ - f a‖ ≤ M * (θ - a) := by
    intro a b ha hb θ hθ
    have hsub' := hsub ha hb
    refine norm_image_sub_le_of_norm_deriv_le_segment'
      (f := f) (f' := fun x => derivWithin f (Set.Icc (0 : ℝ) (Real.pi / 2)) x)
      (a := a) (b := b) (C := M) ?_ ?_ θ hθ
    · intro x hx
      exact (hderiv x (hsub' hx)).mono hsub'
    · intro x hx
      exact hmax (hsub' (Set.Ico_subset_Icc_self hx))
  refine ⟨M, hMnonneg, ?_, ?_⟩
  · intro θ hθ
    rcases le_total θ (Real.pi / 2 - θ) with hle | hle
    · rw [min_eq_left hle]
      have h := key 0 θ ⟨le_rfl, hpos.le⟩ hθ θ ⟨hθ.1, le_rfl⟩
      simpa [h0] using h
    · rw [min_eq_right hle]
      have h := key θ (Real.pi / 2) hθ ⟨hpos.le, le_rfl⟩ (Real.pi / 2) ⟨hθ.2, le_rfl⟩
      simpa [hpi] using h
  · intro θ hθ
    have hnhds : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ nhds θ := Icc_mem_nhds hθ.1 hθ.2
    rw [← derivWithin_of_mem_nhds hnhds]
    exact hmax ⟨hθ.1.le, hθ.2.le⟩

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.power_hardy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option maxHeartbeats 1000000

/-! ## Auxiliary estimates -/

/-- `t ↦ f t ^ 2 * t ^ (-(1 + η)) → 0` as `t → 0⁺`, given `|f t| ≤ C t`. -/
private lemma power_hardy_tendsto_zero {a η C : ℝ} (ha : 0 < a) (hη1 : η < 1) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hbf : ∀ t ∈ Set.Ioo 0 a, |f t| ≤ C * t) :
    Tendsto (fun t : ℝ => f t ^ 2 * t ^ (-(1 + η))) (𝓝[>] 0) (𝓝 0) := by
  have hmem : Set.Ioo 0 a ∈ 𝓝[>] 0 := by
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [Iio_mem_nhds ha] with t ht h0t
    exact ⟨h0t, ht⟩
  have hpoly : Tendsto (fun t : ℝ => t ^ (1 - η)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ (1 - η)) 0 :=
      Real.continuousAt_rpow_const 0 (1 - η) (Or.inr (by linarith))
    have h2 := hc.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    rwa [Real.zero_rpow (by linarith : (1 - η) ≠ 0)] at h2
  have hg : Tendsto (fun t : ℝ => C ^ 2 * t ^ (1 - η)) (𝓝[>] 0) (𝓝 0) := by
    have h2 := (tendsto_const_nhds (x := C ^ 2) (f := 𝓝[>] (0 : ℝ))).mul hpoly
    simpa using h2
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [hmem] with t ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _)
  · filter_upwards [hmem] with t ht
    have h1 : f t ^ 2 ≤ (C * t) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC ht.1.le)]
      exact hbf t ht
    have hid : t ^ 2 * t ^ (-(1 + η)) = t ^ (1 - η) := by
      rw [← Real.rpow_two t, ← Real.rpow_add ht.1]
      congr 1; ring
    calc f t ^ 2 * t ^ (-(1 + η)) ≤ (C * t) ^ 2 * t ^ (-(1 + η)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le _)
      _ = C ^ 2 * t ^ (1 - η) := by
          rw [mul_pow, ← hid]; ring

/-- `t ↦ f t ^ 2 * t ^ (-(1 + η)) → f a ^ 2 * a ^ (-(1 + η))` as `t → a⁻`. -/
private lemma power_hardy_tendsto_a {a η : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 a)) :
    Tendsto (fun t : ℝ => f t ^ 2 * t ^ (-(1 + η))) (𝓝[<] a)
      (𝓝 (f a ^ 2 * a ^ (-(1 + η)))) := by
  have hle : 𝓝[<] a ≤ 𝓝[Set.Icc 0 a] a := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin_iff_eventually]
    filter_upwards [Ioi_mem_nhds (show a / 2 < a by linarith)] with t ht hlt
    simp only [Set.mem_Ioi, Set.mem_Iio, Set.mem_Icc] at ht hlt ⊢
    exact ⟨by linarith, le_of_lt hlt⟩
  have hfa : Tendsto f (𝓝[<] a) (𝓝 (f a)) :=
    (hf.continuousOn.continuousWithinAt ⟨ha.le, le_refl a⟩).mono_left hle
  have hft : Tendsto (fun t : ℝ => f t ^ 2) (𝓝[<] a) (𝓝 (f a ^ 2)) := hfa.pow 2
  have hrp : Tendsto (fun t : ℝ => t ^ (-(1 + η))) (𝓝[<] a) (𝓝 (a ^ (-(1 + η)))) :=
    (Real.continuousAt_rpow_const a (-(1 + η)) (Or.inl ha.ne')).tendsto.mono_left
      (nhdsWithin_le_nhds (a := a) (s := Set.Iio a))
  exact hft.mul hrp

/-- Derivative of `t ↦ f t ^ 2 * t ^ (-(1 + η))` on the interior. -/
private lemma power_hardy_hasDerivAt {a η : ℝ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 a)) {t : ℝ} (ht : t ∈ Set.Ioo 0 a) :
    HasDerivAt (fun s : ℝ => f s ^ 2 * s ^ (-(1 + η)))
      (2 * (f t * deriv f t * t ^ (-(1 + η))) - (1 + η) * (f t ^ 2 * t ^ (-(2 + η)))) t := by
  have hnhds : Set.Icc 0 a ∈ 𝓝 t :=
    mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
  have hd : HasDerivAt f (deriv f t) t :=
    (hf.contDiffAt hnhds).differentiableAt_one.hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => f s ^ 2) (2 * f t ^ 1 * deriv f t) t := hd.pow 2
  have h2 : HasDerivAt (fun s : ℝ => s ^ (-(1 + η))) (-(1 + η) * t ^ (-(1 + η) - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.1.ne')
  have h3 := h1.mul h2
  rw [show -(1 + η) - 1 = -(2 + η) by ring] at h3
  refine h3.congr_deriv ?_
  ring

/-- Interval integrability of the three weighted integrands appearing in `power_hardy`. -/
private lemma power_hardy_integrable {a η C : ℝ} (ha : 0 < a) (hη1 : η < 1) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 a))
    (hbf : ∀ t ∈ Set.Ioo 0 a, |f t| ≤ C * t)
    (hbd : ∀ t ∈ Set.Ioo 0 a, |deriv f t| ≤ C) :
    IntervalIntegrable (fun t : ℝ => f t ^ 2 * t ^ (-(2 + η))) volume 0 a ∧
    IntervalIntegrable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (-η)) volume 0 a ∧
    IntervalIntegrable (fun t : ℝ => f t * deriv f t * t ^ (-(1 + η))) volume 0 a := by
  have hfcont : ContinuousOn f (Set.Ioo 0 a) := hf.continuousOn.mono Set.Ioo_subset_Icc_self
  have hdcont : ContinuousOn (deriv f) (Set.Ioo 0 a) := by
    have h1 : ContinuousOn (fun t => derivWithin f (Set.Icc 0 a) t) (Set.Ioo 0 a) :=
      (hf.continuousOn_derivWithin (uniqueDiffOn_Icc ha) le_rfl).mono Set.Ioo_subset_Icc_self
    refine h1.congr (fun t ht => ?_)
    exact (derivWithin_of_mem_nhds
      (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)).symm
  have hrpow2 : ContinuousOn (fun t : ℝ => t ^ (-(2 + η))) (Set.Ioo 0 a) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne')
  have hrpow1 : ContinuousOn (fun t : ℝ => t ^ (-(1 + η))) (Set.Ioo 0 a) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne')
  have hrpow0 : ContinuousOn (fun t : ℝ => t ^ (-η)) (Set.Ioo 0 a) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne')
  have hid1 : ∀ t ∈ Set.Ioo 0 a, t ^ 2 * t ^ (-(2 + η)) = t ^ (-η) := by
    intro t ht
    rw [← Real.rpow_two t, ← Real.rpow_add ht.1]; congr 1; ring
  have hid2 : ∀ t ∈ Set.Ioo 0 a, t * t ^ (-(1 + η)) = t ^ (-η) := by
    intro t ht
    have h := Real.rpow_add ht.1 (1 : ℝ) (-(1 + η))
    rw [show (1 : ℝ) + (-(1 + η)) = -η by ring] at h
    rw [Real.rpow_one] at h
    exact h.symm
  have key : ∀ {G : ℝ → ℝ}, ContinuousOn G (Set.Ioo 0 a) →
      (∀ t ∈ Set.Ioo 0 a, |G t| ≤ C ^ 2 * t ^ (-η)) → IntervalIntegrable G volume 0 a := by
    intro G hcont hbound
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le, integrableOn_Ioc_iff_integrableOn_Ioo]
    have hg : IntegrableOn (fun t => C ^ 2 * t ^ (-η)) (Set.Ioo 0 a) volume := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1
        ((intervalIntegral.intervalIntegrable_rpow' (show -1 < -η by linarith)).const_mul (C ^ 2))
    refine Integrable.mono' hg (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hbound)]
      with t ht
    simpa only [Real.norm_eq_abs] using ht
  refine ⟨key (hfcont.pow 2 |>.mul hrpow2) ?_, key (hdcont.pow 2 |>.mul hrpow0) ?_,
    key ((hfcont.mul hdcont).mul hrpow1) ?_⟩
  · intro t ht
    have h1 : f t ^ 2 ≤ (C * t) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hC ht.1.le)]; exact hbf t ht
    calc |f t ^ 2 * t ^ (-(2 + η))| = f t ^ 2 * t ^ (-(2 + η)) := by
          rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _))]
      _ ≤ (C * t) ^ 2 * t ^ (-(2 + η)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le _)
      _ = C ^ 2 * t ^ (-η) := by rw [mul_pow, ← hid1 t ht]; ring
  · intro t ht
    have h1 : (deriv f t) ^ 2 ≤ C ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hC]; exact hbd t ht
    calc |(deriv f t) ^ 2 * t ^ (-η)| = (deriv f t) ^ 2 * t ^ (-η) := by
          rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _))]
      _ ≤ C ^ 2 * t ^ (-η) := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.1.le _)
  · intro t ht
    have hab : |f t| * |deriv f t| ≤ C ^ 2 * t := by
      have hb1 := hbf t ht; have hb2 := hbd t ht
      calc |f t| * |deriv f t| ≤ (C * t) * C :=
            mul_le_mul hb1 hb2 (abs_nonneg _) (mul_nonneg hC ht.1.le)
        _ = C ^ 2 * t := by ring
    calc |f t * deriv f t * t ^ (-(1 + η))|
        = |f t| * |deriv f t| * t ^ (-(1 + η)) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      _ ≤ (C ^ 2 * t) * t ^ (-(1 + η)) :=
          mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg ht.1.le _)
      _ = C ^ 2 * t ^ (-η) := by rw [mul_assoc, hid2 t ht]

/-! ## The target theorem -/

theorem power_hardy {a η : ℝ} (ha : 0 < a) (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 a)) (h0 : f 0 = 0) :
    (∫ t in (0 : ℝ)..a, f t ^ 2 * t ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η) := by
  obtain ⟨C, hC, hbf, hbd⟩ := power_hardy_bounds ha hf h0
  obtain ⟨hI1, hI2, hI3⟩ := power_hardy_integrable ha hη1 hC hf hbf hbd
  set φ : ℝ → ℝ :=
    fun t => 2 * (f t * deriv f t * t ^ (-(1 + η))) - (1 + η) * (f t ^ 2 * t ^ (-(2 + η)))
    with hφdef
  have hIφ : IntervalIntegrable φ volume 0 a := by
    simp only [hφdef]
    exact (hI3.const_mul 2).sub (hI1.const_mul (1 + η))
  have hderiv : ∀ x ∈ Set.Ioo 0 a, HasDerivAt (fun s : ℝ => f s ^ 2 * s ^ (-(1 + η))) (φ x) x := by
    intro x hx
    simp only [hφdef]
    exact power_hardy_hasDerivAt hf hx
  have hFTC : ∫ t in (0 : ℝ)..a, φ t = f a ^ 2 * a ^ (-(1 + η)) - 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ha hderiv hIφ
      (power_hardy_tendsto_zero ha hη1 hC hbf) (power_hardy_tendsto_a ha hf)
  have hpt : ∀ t ∈ Set.Ioo 0 a, (1 + η) ^ 2 / 4 * (f t ^ 2 * t ^ (-(2 + η)))
      ≤ (deriv f t) ^ 2 * t ^ (-η) + (-(1 + η) / 2) * φ t := by
    intro t ht
    simp only [hφdef]
    have hid1 : t ^ 2 * t ^ (-(2 + η)) = t ^ (-η) := by
      rw [← Real.rpow_two t, ← Real.rpow_add ht.1]; congr 1; ring
    have hid2 : t * t ^ (-(1 + η)) = t ^ (-η) := by
      have h := Real.rpow_add ht.1 (1 : ℝ) (-(1 + η))
      rw [show (1 : ℝ) + (-(1 + η)) = -η by ring] at h
      rw [Real.rpow_one] at h
      exact h.symm
    have h2 : (f t / t) ^ 2 * t ^ 2 = f t ^ 2 := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 ht.1.ne')]
    have hx1 : f t ^ 2 * t ^ (-(2 + η)) = (f t / t) ^ 2 * t ^ (-η) := by
      calc f t ^ 2 * t ^ (-(2 + η)) = ((f t / t) ^ 2 * t ^ 2) * t ^ (-(2 + η)) := by rw [h2]
        _ = (f t / t) ^ 2 * (t ^ 2 * t ^ (-(2 + η))) := by ring
        _ = (f t / t) ^ 2 * t ^ (-η) := by rw [hid1]
    have hx2 : f t * deriv f t * t ^ (-(1 + η)) = (f t / t) * deriv f t * t ^ (-η) := by
      have h3 : (f t / t) * t = f t := div_mul_cancel₀ (f t) ht.1.ne'
      calc f t * deriv f t * t ^ (-(1 + η))
          = ((f t / t) * t) * deriv f t * t ^ (-(1 + η)) := by rw [h3]
        _ = (f t / t) * deriv f t * (t * t ^ (-(1 + η))) := by ring
        _ = (f t / t) * deriv f t * t ^ (-η) := by rw [hid2]
    rw [hx1, hx2]
    nlinarith [mul_nonneg (Real.rpow_nonneg ht.1.le (-η))
      (sq_nonneg (deriv f t - (1 + η) / 2 * (f t / t)))]
  have hmono : ∫ t in (0 : ℝ)..a, (1 + η) ^ 2 / 4 * (f t ^ 2 * t ^ (-(2 + η)))
      ≤ ∫ t in (0 : ℝ)..a, ((deriv f t) ^ 2 * t ^ (-η) + (-(1 + η) / 2) * φ t) :=
    intervalIntegral.integral_mono_on_of_le_Ioo ha.le
      (hI1.const_mul _) (hI2.add (hIφ.const_mul _)) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [intervalIntegral.integral_add hI2 (hIφ.const_mul _),
    intervalIntegral.integral_const_mul] at hmono
  rw [hFTC, sub_zero] at hmono
  have hle : (-(1 + η) / 2) * (f a ^ 2 * a ^ (-(1 + η))) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ha.le _))
  have hkey : (1 + η) ^ 2 / 4 * (∫ t in (0 : ℝ)..a, f t ^ 2 * t ^ (-(2 + η)))
      ≤ ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η) := by
    linarith [hmono, hle]
  have hsq : (0 : ℝ) < (1 + η) ^ 2 := pow_pos (by linarith) 2
  rw [div_mul_eq_mul_div, le_div_iff₀ hsq]
  nlinarith [hkey, hsq]

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.pth_tan_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

theorem pth_tan_mul (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (h : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
      = Ψ z θ / Real.cos θ ^ 2 + Real.tan θ * Work.Spaces.pth Ψ z θ := by
  unfold Work.Spaces.pth
  change deriv (fun θ' => Real.tan θ' * Ψ z θ') θ
    = Ψ z θ / Real.cos θ ^ 2 + Real.tan θ * deriv (fun θ' => Ψ z θ') θ
  rw [show (fun θ' => Real.tan θ' * Ψ z θ') = Real.tan * (fun θ' => Ψ z θ') from rfl]
  rw [deriv_mul ((Real.differentiableAt_tan).mpr hcos) h, Real.deriv_tan]
  ring

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.radial_arith =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The elementary estimate `z^n ≤ (1+z)^n` for `z ≥ 0`. -/
private lemma z_pow_le_one_add {z : ℝ} (hz : 0 < z) (n : ℕ) : z ^ n ≤ (1 + z) ^ n :=
  pow_le_pow_left₀ (le_of_lt hz) (by linarith) n

/-- The single bound that the hypothesis `hA` provides, in the form in which it is used:
`|(1+z)^3 z^j A_j| ≤ 6000 Λ` for every `j ≤ m`.  Indeed `z ≤ 1+z` gives
`(1+z)^3 z^j ≤ (1+z)^{j+3}`. -/
private lemma term_bound {m : ℕ} {z Λ : ℝ} (hz : 0 < z) (A : ℕ → ℝ)
    (hA : ∀ j ≤ m, |(1 + z) ^ (j + 3) * A j| ≤ 6000 * Λ) {j : ℕ} (hj : j ≤ m) :
    |(1 + z) ^ 3 * z ^ j * A j| ≤ 6000 * Λ := by
  have hz3 : (0 : ℝ) ≤ (1 + z) ^ 3 := by positivity
  have hle : (1 + z) ^ 3 * z ^ j ≤ (1 + z) ^ (j + 3) := by
    calc (1 + z) ^ 3 * z ^ j ≤ (1 + z) ^ 3 * (1 + z) ^ j :=
          mul_le_mul_of_nonneg_left (z_pow_le_one_add hz j) hz3
      _ = (1 + z) ^ (j + 3) := by rw [← pow_add, Nat.add_comm]
  calc |(1 + z) ^ 3 * z ^ j * A j|
      = (1 + z) ^ 3 * z ^ j * |A j| := by
        rw [abs_mul, abs_mul]
        rw [abs_of_nonneg hz3, abs_of_nonneg (pow_nonneg (le_of_lt hz) j)]
    _ ≤ (1 + z) ^ (j + 3) * |A j| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ = |(1 + z) ^ (j + 3) * A j| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) ^ (j + 3))]
    _ ≤ 6000 * Λ := hA j hj

/-- Since `w z = (1+z)²/z²`, the factor `(1+z) · w z · z^m` is `(1+z)³ z^{m-2}` for `m ≥ 2`;
together with the bracket `z² A_m + 2m z A_{m-1} + m(m-1) A_{m-2}` this produces a sum of the
three monomials `(1+z)³ z^j A_j` with `j = m, m-1, m-2`, each of which is bounded by `6000 Λ`.
For `m ≤ 1` the coefficients of the two lower terms vanish, so only the `j = m` term survives.
In all cases `m ≤ 4` the sum of the coefficients is at most `21`, giving the constant `200000`. -/
theorem radial_arith {m : ℕ} (hm : m ≤ 4) {z Λ : ℝ} (hz : 0 < z) (hΛ : 0 ≤ Λ)
    (A : ℕ → ℝ) (hA : ∀ j ≤ m, |(1 + z) ^ (j + 3) * A j| ≤ 6000 * Λ) :
    |(1 + z) * Work.Spaces.w z * z ^ m * (z ^ 2 * A m + (2 * (m : ℝ)) * z * A (m - 1)
        + ((m : ℝ) * ((m : ℝ) - 1)) * A (m - 2))| ≤ 200000 * Λ := by
  interval_cases m
  · -- m = 0 : only the top term survives, `(1+z) w z · z² A₀ = (1+z)³ A₀`
    have hfac : (1 + z) * Work.Spaces.w z * z ^ 0 * (z ^ 2 * A 0 + 2 * (((0:ℕ):ℝ)) * z * A (0 - 1)
        + (((0:ℕ):ℝ)) * ((((0:ℕ):ℝ)) - 1) * A (0 - 2)) = (1 + z) ^ 3 * A 0 := by
      rw [Work.Spaces.w]; norm_num; field_simp <;> ring
    rw [hfac]
    have h := term_bound hz A hA (j := 0) (by norm_num)
    simp only [pow_zero, mul_one] at h
    linarith
  · -- m = 1 : `(1+z)³ (z A₁ + 2 A₀)`
    have hfac : (1 + z) * Work.Spaces.w z * z ^ 1 * (z ^ 2 * A 1 + 2 * (((1:ℕ):ℝ)) * z * A (1 - 1)
        + (((1:ℕ):ℝ)) * ((((1:ℕ):ℝ)) - 1) * A (1 - 2))
        = (1 + z) ^ 3 * z * A 1 + 2 * ((1 + z) ^ 3 * A 0) := by
      rw [Work.Spaces.w]; norm_num; field_simp <;> ring
    rw [hfac]
    have hX : |(1 + z) ^ 3 * z * A 1| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 1) (by norm_num)
      simpa [pow_one] using h
    have hY : |2 * ((1 + z) ^ 3 * A 0)| ≤ 12000 * Λ := by
      have h0 : |(1 + z) ^ 3 * A 0| ≤ 6000 * Λ := by
        have h := term_bound hz A hA (j := 0) (by norm_num)
        simpa using h
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    calc |(1 + z) ^ 3 * z * A 1 + 2 * ((1 + z) ^ 3 * A 0)|
        ≤ |(1 + z) ^ 3 * z * A 1| + |2 * ((1 + z) ^ 3 * A 0)| := abs_add_le _ _
      _ ≤ 6000 * Λ + 12000 * Λ := add_le_add hX hY
      _ ≤ 200000 * Λ := by linarith
  · -- m = 2 : `(1+z)³ (z² A₂ + 4 z A₁ + 2 A₀)`
    have hfac : (1 + z) * Work.Spaces.w z * z ^ 2 * (z ^ 2 * A 2 + 2 * (((2:ℕ):ℝ)) * z * A (2 - 1)
        + (((2:ℕ):ℝ)) * ((((2:ℕ):ℝ)) - 1) * A (2 - 2)) =
        (1 + z) ^ 3 * z ^ 2 * A 2 + 4 * ((1 + z) ^ 3 * z * A 1)
          + 2 * ((1 + z) ^ 3 * A 0) := by
      rw [Work.Spaces.w]; norm_num; field_simp <;> ring
    rw [hfac]
    have h2 : |(1 + z) ^ 3 * z ^ 2 * A 2| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 2) (by norm_num); simpa using h
    have h1 : |(1 + z) ^ 3 * z * A 1| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 1) (by norm_num); simpa [pow_one] using h
    have h0 : |(1 + z) ^ 3 * A 0| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 0) (by norm_num); simpa using h
    have h4 : |4 * ((1 + z) ^ 3 * z * A 1)| ≤ 24000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]; linarith
    have h2' : |2 * ((1 + z) ^ 3 * A 0)| ≤ 12000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith
    calc |(1 + z) ^ 3 * z ^ 2 * A 2 + 4 * ((1 + z) ^ 3 * z * A 1) + 2 * ((1 + z) ^ 3 * A 0)|
        ≤ |(1 + z) ^ 3 * z ^ 2 * A 2| + |4 * ((1 + z) ^ 3 * z * A 1)|
            + |2 * ((1 + z) ^ 3 * A 0)| := abs_add_three _ _ _
      _ ≤ 6000 * Λ + 24000 * Λ + 12000 * Λ := add_le_add (add_le_add h2 h4) h2'
      _ ≤ 200000 * Λ := by linarith
  · -- m = 3 : `(1+z)³ z (z² A₃ + 6 z A₂ + 6 A₁)`
    have hfac : (1 + z) * Work.Spaces.w z * z ^ 3 * (z ^ 2 * A 3 + 2 * (((3:ℕ):ℝ)) * z * A (3 - 1)
        + (((3:ℕ):ℝ)) * ((((3:ℕ):ℝ)) - 1) * A (3 - 2)) =
        (1 + z) ^ 3 * z ^ 3 * A 3 + 6 * ((1 + z) ^ 3 * z ^ 2 * A 2)
          + 6 * ((1 + z) ^ 3 * z * A 1) := by
      rw [Work.Spaces.w]; norm_num; field_simp <;> ring
    rw [hfac]
    have h3 : |(1 + z) ^ 3 * z ^ 3 * A 3| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 3) (by norm_num); simpa using h
    have h2 : |(1 + z) ^ 3 * z ^ 2 * A 2| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 2) (by norm_num); simpa using h
    have h1 : |(1 + z) ^ 3 * z * A 1| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 1) (by norm_num); simpa [pow_one] using h
    have h6a : |6 * ((1 + z) ^ 3 * z ^ 2 * A 2)| ≤ 36000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]; linarith
    have h6b : |6 * ((1 + z) ^ 3 * z * A 1)| ≤ 36000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]; linarith
    calc |(1 + z) ^ 3 * z ^ 3 * A 3 + 6 * ((1 + z) ^ 3 * z ^ 2 * A 2)
            + 6 * ((1 + z) ^ 3 * z * A 1)|
        ≤ |(1 + z) ^ 3 * z ^ 3 * A 3| + |6 * ((1 + z) ^ 3 * z ^ 2 * A 2)|
            + |6 * ((1 + z) ^ 3 * z * A 1)| := abs_add_three _ _ _
      _ ≤ 6000 * Λ + 36000 * Λ + 36000 * Λ := add_le_add (add_le_add h3 h6a) h6b
      _ ≤ 200000 * Λ := by linarith
  · -- m = 4 : `(1+z)³ z² (z² A₄ + 8 z A₃ + 12 A₂)`
    have hfac : (1 + z) * Work.Spaces.w z * z ^ 4 * (z ^ 2 * A 4 + 2 * (((4:ℕ):ℝ)) * z * A (4 - 1)
        + (((4:ℕ):ℝ)) * ((((4:ℕ):ℝ)) - 1) * A (4 - 2)) =
        (1 + z) ^ 3 * z ^ 4 * A 4 + 8 * ((1 + z) ^ 3 * z ^ 3 * A 3)
          + 12 * ((1 + z) ^ 3 * z ^ 2 * A 2) := by
      rw [Work.Spaces.w]; norm_num; field_simp <;> ring
    rw [hfac]
    have h4 : |(1 + z) ^ 3 * z ^ 4 * A 4| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 4) (by norm_num); simpa using h
    have h3 : |(1 + z) ^ 3 * z ^ 3 * A 3| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 3) (by norm_num); simpa using h
    have h2 : |(1 + z) ^ 3 * z ^ 2 * A 2| ≤ 6000 * Λ := by
      have h := term_bound hz A hA (j := 2) (by norm_num); simpa using h
    have h8 : |8 * ((1 + z) ^ 3 * z ^ 3 * A 3)| ≤ 48000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]; linarith
    have h12 : |12 * ((1 + z) ^ 3 * z ^ 2 * A 2)| ≤ 72000 * Λ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)]; linarith
    calc |(1 + z) ^ 3 * z ^ 4 * A 4 + 8 * ((1 + z) ^ 3 * z ^ 3 * A 3)
            + 12 * ((1 + z) ^ 3 * z ^ 2 * A 2)|
        ≤ |(1 + z) ^ 3 * z ^ 4 * A 4| + |8 * ((1 + z) ^ 3 * z ^ 3 * A 3)|
            + |12 * ((1 + z) ^ 3 * z ^ 2 * A 2)| := abs_add_three _ _ _
      _ ≤ 6000 * Λ + 48000 * Λ + 72000 * Λ := add_le_add (add_le_add h4 h8) h12
      _ ≤ 200000 * Λ := by linarith

end Work.Elliptic
end
-- ===== merged: Submission.Work.Elliptic.rigidity_ode =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open Set Filter
open scoped Topology


end Work.Elliptic
end
-- ===== merged: Submission.Work.EllipticEst.Core.hardyBoundaryPower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Weighted Hardy inequality with a boundary term (`hardyBoundaryPower`)

For `λ > -1` and `0 < a < b`, and `f` of class `C¹` on `(0,∞)`:

```
(1+λ)²/4 ∫_a^b x^{-(2+λ)} f(x)² dx
    ≤ ∫_a^b x^{-λ} f'(x)² dx
      - (1+λ)/2 ( b^{-(1+λ)} f(b)² - a^{-(1+λ)} f(a)² ).
```

This is the sharp weighted Hardy inequality *with* the boundary term kept
(the case `a = 0`, `f(0) = 0` reduces to the classical
`(1+λ)²/4 ∫ x^{-(2+λ)}f² ≤ ∫ x^{-λ}f'²`).

The proof is the standard completion of squares.  Writing
`X := (1+λ)/2`, `I₁ := ∫_a^b x^{-λ}f'²`, `I₂ := ∫_a^b x^{-(2+λ)}f²` and
`D := b^{-(1+λ)}f(b)² - a^{-(1+λ)}f(a)²`:

* (FTC) `d/dx (x^{-(1+λ)} f(x)²) = -(1+λ) x^{-(2+λ)} f² + 2 x^{-(1+λ)} f f'`,
  hence `∫_a^b x^{-(1+λ)} f f' = D/2 + X I₂`;
* pointwise, `x^{-λ}(f' - X f/x)² = x^{-λ}f'² - X (d/dx (x^{-(1+λ)}f²)) - X² x^{-(2+λ)}f²`.

Integrating the last identity over `[a,b]` and inserting the FTC identity yields

`0 ≤ ∫_a^b x^{-λ}(f' - X f/x)² = I₁ - X D - X² I₂`,

i.e. `X² I₂ ≤ I₁ - X D`, which is the claim since `X² = (1+λ)²/4`.
-/

open MeasureTheory

namespace Work.EllipticEst.Core







end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.etaTBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

open scoped Topology
open Filter Set MeasureTheory

set_option autoImplicit false

theorem etaT_hasDerivAt (t x : ℝ) :
    HasDerivAt (Work.EllipticEst.Core.i0Aux.etaT t)
      (Work.EllipticEst.Core.i0Aux.etaT' t x) x := by
  have h := (hasDerivAt_id x).mul (((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      ((hasDerivAt_id x).div_const t)).pow 3)
  have hder : 1 * (1 - x / t) ^ 3 + x * (3 * (1 - x / t) ^ (3 - 1) * (0 - 1 / t))
      = Work.EllipticEst.Core.i0Aux.etaT' t x := by
    unfold Work.EllipticEst.Core.i0Aux.etaT'
    ring_nf
  have h' : HasDerivAt (fun y : ℝ => y * (1 - y / t) ^ 3)
      (1 * (1 - x / t) ^ 3 + x * (3 * (1 - x / t) ^ (3 - 1) * (0 - 1 / t))) x := h
  rw [hder] at h'
  exact h'

theorem etaT'_hasDerivAt (t x : ℝ) :
    HasDerivAt (Work.EllipticEst.Core.i0Aux.etaT' t)
      (Work.EllipticEst.Core.i0Aux.etaT'' t x) x := by
  have h1 := ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
    ((hasDerivAt_id x).div_const t)).pow 2
  have h3 := (hasDerivAt_id x).const_mul (4 : ℝ) |>.div_const t
  have h2 := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub h3
  have h := h1.mul h2
  unfold Work.EllipticEst.Core.i0Aux.etaT' Work.EllipticEst.Core.i0Aux.etaT''
  convert h using 1
  · funext y
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
    try ring_nf
  · simp only [Pi.pow_apply, Pi.sub_apply, id_eq]
    try ring_nf

theorem continuous_etaT (t : ℝ) : Continuous (Work.EllipticEst.Core.i0Aux.etaT t) :=
  continuous_iff_continuousAt.mpr fun x => (etaT_hasDerivAt t x).continuousAt

theorem continuous_etaT' (t : ℝ) : Continuous (Work.EllipticEst.Core.i0Aux.etaT' t) :=
  continuous_iff_continuousAt.mpr fun x => (etaT'_hasDerivAt t x).continuousAt

theorem continuous_etaT'' (t : ℝ) : Continuous (Work.EllipticEst.Core.i0Aux.etaT'' t) := by
  rw [show Work.EllipticEst.Core.i0Aux.etaT'' t
      = fun x => (6 / t) * (1 - x / t) * (2 * x / t - 1) from rfl]
  fun_prop

theorem etaT_zero (t : ℝ) : Work.EllipticEst.Core.i0Aux.etaT t 0 = 0 := by
  simp [Work.EllipticEst.Core.i0Aux.etaT]

theorem etaT'_zero (t : ℝ) : Work.EllipticEst.Core.i0Aux.etaT' t 0 = 1 := by
  simp [Work.EllipticEst.Core.i0Aux.etaT']

theorem etaT_at_t (t : ℝ) (ht : t ≠ 0) : Work.EllipticEst.Core.i0Aux.etaT t t = 0 := by
  have h : 1 - t / t = 0 := by rw [div_self ht]; ring
  rw [Work.EllipticEst.Core.i0Aux.etaT, h]
  ring

theorem etaT'_at_t (t : ℝ) (ht : t ≠ 0) : Work.EllipticEst.Core.i0Aux.etaT' t t = 0 := by
  have h : 1 - t / t = 0 := by rw [div_self ht]; ring
  rw [Work.EllipticEst.Core.i0Aux.etaT', h]
  ring



end Work.EllipticEst.Core.i0Aux.EndpointValues
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.etaTFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

open MeasureTheory Set Filter


end Work.EllipticEst.Core.i0Aux.EndpointValues
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.reflectFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Reflection facts on `(0, π/2)`

The map `θ ↦ π/2 - θ` is an involutive, measure preserving bijection of `Ioo 0 (π/2)` onto
itself.  This file records the six consequences used by the endpoint analysis of the `i0`
chapter: invariance of the Lebesgue integral, transfer of integrability, transfer of `C²`,
the first and second chain rules for the global `deriv`, and the transfer of the one-sided
limit at `π/2⁻` for `f` into the one-sided limit at `0⁺` for the reflected function.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

set_option autoImplicit false

/-- The reflection `θ ↦ π/2 - θ` maps the interval `Ioo 0 (π/2)` onto itself. -/
private lemma reflect_preimage_Ioo :
    (fun θ : ℝ => Real.pi / 2 - θ) ⁻¹' Set.Ioo 0 (Real.pi / 2) = Set.Ioo 0 (Real.pi / 2) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The Lebesgue integral on `Ioo 0 (π/2)` is invariant under `θ ↦ π/2 - θ`. -/
private lemma reflect_integral (F : ℝ → ℝ) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), F (Real.pi / 2 - θ))
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), F θ := by
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := _root_.Work.EllipticEst.Core.i0Aux.setIntegral_Ioo_comp_sub F (Real.pi / 2) hab
  simpa only [sub_self, sub_zero] using h

/-- Integrability on `Ioo 0 (π/2)` is preserved by `θ ↦ π/2 - θ`. -/
private lemma reflect_integrableOn (F : ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn F (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => F (Real.pi / 2 - θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hmp : MeasureTheory.MeasurePreserving (fun θ : ℝ => Real.pi / 2 - θ) volume volume :=
    _root_.MeasureTheory.Measure.measurePreserving_sub_left volume (Real.pi / 2)
  have hemb : MeasurableEmbedding (fun θ : ℝ => Real.pi / 2 - θ) :=
    measurableEmbedding_subLeft (Real.pi / 2)
  have h := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage hmp hemb
    (f := F) (s := Set.Ioo 0 (Real.pi / 2))
  rw [reflect_preimage_Ioo] at h
  exact h.mpr hF

/-- `C²` on `Ioo 0 (π/2)` is preserved by `θ ↦ π/2 - θ`. -/
private lemma reflect_contDiffOn (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (fun θ : ℝ => f (Real.pi / 2 - θ)) (Set.Ioo 0 (Real.pi / 2)) := by
  have hg : ContDiffOn ℝ 2 (fun θ : ℝ => Real.pi / 2 - θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h : ContDiff ℝ 2 (fun θ : ℝ => Real.pi / 2 - θ) :=
      (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => Real.pi / 2)).sub contDiff_id
    exact h.contDiffOn
  have hmap : MapsTo (fun θ : ℝ => Real.pi / 2 - θ) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  exact hf.comp hg hmap

/-- The chain rule for the first derivative. -/
private lemma reflect_deriv (f : ℝ → ℝ) (_hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (_hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' : ℝ => f (Real.pi / 2 - θ')) θ = -deriv f (Real.pi / 2 - θ) :=
  deriv_comp_const_sub f (Real.pi / 2) θ

/-- The chain rule for the second derivative (`deriv (deriv ·)`, not `iteratedDeriv`). -/
private lemma reflect_deriv2 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (fun θ' : ℝ => f (Real.pi / 2 - θ'))) θ
      = deriv (deriv f) (Real.pi / 2 - θ) := by
  have hso : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hm : Real.pi / 2 - θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have heq : deriv (fun θ' : ℝ => f (Real.pi / 2 - θ'))
      = fun y : ℝ => -deriv f (Real.pi / 2 - y) :=
    funext fun y => deriv_comp_const_sub f (Real.pi / 2) y
  rw [heq]
  have h2 : HasDerivAt (deriv f) (deriv (deriv f) (Real.pi / 2 - θ)) (Real.pi / 2 - θ) :=
    (((hf.contDiffAt (hso.mem_nhds hm)).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have h3 : HasDerivAt (fun y : ℝ => deriv f (Real.pi / 2 - y))
      (-(deriv (deriv f) (Real.pi / 2 - θ))) θ :=
    HasDerivAt.comp_const_sub (Real.pi / 2) θ h2
  have h4 : deriv (fun y : ℝ => -deriv f (Real.pi / 2 - y)) θ
      = -(-(deriv (deriv f) (Real.pi / 2 - θ))) := by
    simpa only [Pi.neg_def] using h3.neg.deriv
  rw [h4]
  ring

/-- A one-sided limit at `π/2⁻` becomes a one-sided limit at `0⁺` after reflection. -/
private lemma reflect_tendsto (f : ℝ → ℝ) (F : ℝ)
    (hf : Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F)) :
    Tendsto (fun θ : ℝ => f (Real.pi / 2 - θ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F) := by
  have hcont : Continuous fun y : ℝ => Real.pi / 2 - y := continuous_const.sub continuous_id
  have htend : Tendsto (fun y : ℝ => Real.pi / 2 - y) (nhds (0 : ℝ)) (nhds (Real.pi / 2)) :=
    hcont.tendsto' 0 (Real.pi / 2) (by simp)
  have hmem : ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Real.pi / 2 - y ∈ Set.Iio (Real.pi / 2) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_Ioi] at hy
    simp only [Set.mem_Iio]
    linarith
  have hin : Tendsto (fun y : ℝ => Real.pi / 2 - y) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend.mono_left nhdsWithin_le_nhds, hmem⟩
  exact hf.comp hin

theorem reflectFacts :
    (∀ F : ℝ → ℝ, (∫ θ in Set.Ioo 0 (Real.pi / 2), F (Real.pi / 2 - θ))
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), F θ) ∧
    (∀ F : ℝ → ℝ, MeasureTheory.IntegrableOn F (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => F (Real.pi / 2 - θ))
        (Set.Ioo 0 (Real.pi / 2))) ∧
    (∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ContDiffOn ℝ 2 (fun θ : ℝ => f (Real.pi / 2 - θ)) (Set.Ioo 0 (Real.pi / 2))) ∧
    (∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' : ℝ => f (Real.pi / 2 - θ')) θ = -deriv f (Real.pi / 2 - θ)) ∧
    (∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (fun θ' : ℝ => f (Real.pi / 2 - θ'))) θ
        = deriv (deriv f) (Real.pi / 2 - θ)) ∧
    (∀ (f : ℝ → ℝ) (F : ℝ),
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F) →
      Filter.Tendsto (fun θ : ℝ => f (Real.pi / 2 - θ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds F)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact reflect_integral
  · intro F hF
    exact reflect_integrableOn F hF
  · intro f hf
    exact reflect_contDiffOn f hf
  · intro f hf θ hθ
    exact reflect_deriv f hf hθ
  · intro f hf θ hθ
    exact reflect_deriv2 f hf hθ
  · intro f F hf
    exact reflect_tendsto f F hf

end Work.EllipticEst.Core.i0Aux.EndpointValues
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.radialPairIBP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

set_option autoImplicit false
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Three elementary one-dimensional lemmas -/

/-- A function which vanishes on a neighbourhood of `x` has vanishing derivative there. -/
lemma deriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] 0) :
    deriv f x = 0 := by
  have h' := h.deriv_eq
  simpa using h'




/-! ## The main lemma -/


end

end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.EllipticEst.Core.weightedCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

theorem weightedCS {s : Set ℝ} (hs : MeasurableSet s) {w g : ℝ → ℝ}
    (hw : ∀ t ∈ s, 0 < w t) (hwc : ContinuousOn w s) (hgc : ContinuousOn g s)
    (hg2 : MeasureTheory.IntegrableOn (fun t => (g t) ^ 2 * w t) s)
    (hwi : MeasureTheory.IntegrableOn (fun t => (w t)⁻¹) s) :
    (MeasureTheory.integral (MeasureTheory.volume.restrict s) (fun t => g t)) ^ 2
      ≤ (MeasureTheory.integral (MeasureTheory.volume.restrict s) (fun t => (g t) ^ 2 * w t))
        * (MeasureTheory.integral (MeasureTheory.volume.restrict s) (fun t => (w t)⁻¹)) := by
  have hsw : ContinuousOn (fun t => Real.sqrt (w t)) s :=
    Real.continuous_sqrt.comp_continuousOn hwc
  have hpos : ∀ t ∈ s, 0 < Real.sqrt (w t) := fun t ht => Real.sqrt_pos.2 (hw t ht)
  have hne : ∀ t ∈ s, Real.sqrt (w t) ≠ 0 := fun t ht => ne_of_gt (hpos t ht)
  have hwge : ∀ t ∈ s, 0 ≤ w t := fun t ht => (hw t ht).le
  have hu_aesm : MeasureTheory.AEStronglyMeasurable (fun t => g t * Real.sqrt (w t))
      (MeasureTheory.volume.restrict s) :=
    (hgc.mul hsw).aestronglyMeasurable hs
  have hu_mem : MeasureTheory.MemLp (fun t => g t * Real.sqrt (w t)) 2
      (MeasureTheory.volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hu_aesm]
    refine hg2.congr_fun ?_ hs
    intro t ht
    change g t ^ 2 * w t = (g t * Real.sqrt (w t)) ^ 2
    rw [mul_pow, Real.sq_sqrt (hwge t ht)]
  have hv_aesm : MeasureTheory.AEStronglyMeasurable (fun t => (Real.sqrt (w t))⁻¹)
      (MeasureTheory.volume.restrict s) :=
    (hsw.inv₀ hne).aestronglyMeasurable hs
  have hv_mem : MeasureTheory.MemLp (fun t => (Real.sqrt (w t))⁻¹) 2
      (MeasureTheory.volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hv_aesm]
    refine hwi.congr_fun ?_ hs
    intro t ht
    change (w t)⁻¹ = ((Real.sqrt (w t))⁻¹) ^ 2
    rw [inv_pow, Real.sq_sqrt (hwge t ht)]
  have h_uv : (∫ t in s, (g t * Real.sqrt (w t)) * (Real.sqrt (w t))⁻¹) = ∫ t in s, g t :=
    MeasureTheory.setIntegral_congr_fun hs (fun t ht => by
      rw [mul_assoc, mul_inv_cancel₀ (hne t ht), mul_one])
  have h_u2 : (∫ t in s, (g t * Real.sqrt (w t)) ^ 2) = ∫ t in s, g t ^ 2 * w t :=
    MeasureTheory.setIntegral_congr_fun hs (fun t ht => by
      rw [mul_pow, Real.sq_sqrt (hwge t ht)])
  have h_v2 : (∫ t in s, ((Real.sqrt (w t))⁻¹) ^ 2) = ∫ t in s, (w t)⁻¹ :=
    MeasureTheory.setIntegral_congr_fun hs (fun t ht => by
      rw [inv_pow, Real.sq_sqrt (hwge t ht)])
  have key := Work.Spaces.cs_integral hu_mem hv_mem
  rw [h_uv, h_u2, h_v2] at key
  exact key

end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.conv_l2_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory ENNReal

/-- The `L²`-estimate behind Young's convolution inequality `L¹ * L² → L²`, stated purely in
terms of lower Lebesgue integrals and with no measurability hypothesis on the convolution:

`∫⁻ x, (∫⁻ y, F (x - y) u y)² ≤ (∫ F) * ((∫ F) * ∫ u²)`

for `F ≥ 0` integrable and `u ≥ 0` square integrable.  The proof is the completion-of-squares
(weighted Cauchy–Schwarz) inequality in `y` with weight `√(F (x - y))`, followed by Tonelli and
the translation invariance of the Lebesgue measure. -/
theorem conv_l2_lintegral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F u : E → ℝ} (hF : ∀ x, 0 ≤ F x) (hu : ∀ x, 0 ≤ u x)
    (hFi : MeasureTheory.Integrable F MeasureTheory.volume)
    (huM : MeasureTheory.MemLp u 2 MeasureTheory.volume) :
    (∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ) ∂MeasureTheory.volume)
      ≤ (∫⁻ z, ENNReal.ofReal (F z)) * ((∫⁻ z, ENNReal.ofReal (F z))
          * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
  have hFm : AEMeasurable F (volume : Measure E) := hFi.aemeasurable
  have hum : AEMeasurable u (volume : Measure E) := huM.aemeasurable
  -- `∫⁻` of `ofReal F` is `ofReal` of the integral
  have hAeq : ENNReal.ofReal (∫ z, F z) = ∫⁻ z, ENNReal.ofReal (F z) :=
    ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF)
  have hAlt : (∫⁻ z, ENNReal.ofReal (F z)) ≠ ∞ := by
    rw [← hAeq]; exact ENNReal.ofReal_ne_top
  -- Cauchy–Schwarz in `y` with weight `√(F (x - y))`, for each `x`
  have hcs : ∀ x : E, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ)
      ≤ (∫⁻ y, ENNReal.ofReal (F (x - y)))
        * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) := by
    intro x
    have hFmeas : AEMeasurable (fun y : E => F (x - y)) (volume : Measure E) :=
      hFm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
    set phi : E → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.sqrt (F (x - y))) with hphidef
    set psi : E → ℝ≥0∞ := fun y => phi y * ENNReal.ofReal (u y) with hsidef
    have hphim : AEMeasurable phi (volume : Measure E) := by
      rw [hphidef]
      exact ((ENNReal.measurable_ofReal.comp Real.continuous_sqrt.measurable).comp_aemeasurable
        hFmeas)
    have humeas : AEMeasurable (fun y : E => ENNReal.ofReal (u y)) (volume : Measure E) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hum
    have hpsim : AEMeasurable psi (volume : Measure E) := by
      rw [hsidef]; exact hphim.mul humeas
    have hphiphi : ∀ y, phi y * phi y = ENNReal.ofReal (F (x - y)) := by
      intro y
      rw [hphidef]; simp only
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt (hF _)]
    have hpsipsi : ∀ y, psi y * psi y = ENNReal.ofReal (F (x - y) * u y ^ 2) := by
      intro y
      have h1 : psi y = phi y * ENNReal.ofReal (u y) := rfl
      calc psi y * psi y
          = (phi y * phi y) * (ENNReal.ofReal (u y) * ENNReal.ofReal (u y)) := by
            rw [h1]; ring
        _ = ENNReal.ofReal (F (x - y)) * (ENNReal.ofReal (u y) * ENNReal.ofReal (u y)) := by
            rw [hphiphi y]
        _ = ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2) := by
            rw [← pow_two, ← ENNReal.ofReal_pow (hu y) 2]
        _ = ENNReal.ofReal (F (x - y) * u y ^ 2) := by rw [← ENNReal.ofReal_mul (hF _)]
    have hphis : ∀ y, phi y * psi y = ENNReal.ofReal (F (x - y) * u y) := by
      intro y
      have h1 : psi y = phi y * ENNReal.ofReal (u y) := rfl
      calc phi y * psi y = (phi y * phi y) * ENNReal.ofReal (u y) := by rw [h1]; ring
        _ = ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y) := by rw [hphiphi y]
        _ = ENNReal.ofReal (F (x - y) * u y) := by rw [← ENNReal.ofReal_mul (hF _)]
    have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure E) (p := 2) (q := 2)
      (⟨by norm_num, by norm_num, by norm_num⟩ : (2:ℝ).HolderConjugate 2) hphim hpsim
    have hH : (∫⁻ y, ENNReal.ofReal (F (x - y) * u y))
        ≤ (∫⁻ y, ENNReal.ofReal (F (x - y))) ^ ((1:ℝ)/2)
          * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) ^ ((1:ℝ)/2) := by
      have h1 : (∫⁻ y, phi y * psi y) = ∫⁻ y, ENNReal.ofReal (F (x - y) * u y) :=
        lintegral_congr (fun y => hphis y)
      have h2 : (∫⁻ y, phi y ^ (2:ℝ)) = ∫⁻ y, ENNReal.ofReal (F (x - y)) :=
        lintegral_congr (fun y => by rw [ENNReal.rpow_two, pow_two, hphiphi y])
      have h3 : (∫⁻ y, psi y ^ (2:ℝ)) = ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2) :=
        lintegral_congr (fun y => by rw [ENNReal.rpow_two, pow_two, hpsipsi y])
      rw [show (∫⁻ a : E, (phi * psi) a) = ∫⁻ y, phi y * psi y from rfl, h1, h2, h3] at hHold
      exact hHold
    have hH2 := ENNReal.rpow_le_rpow hH (by norm_num : (0:ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)] at hH2
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hH2
    norm_num at hH2
    simpa using hH2
  -- translation invariance in `x`
  have htrans : ∀ x : E, (∫⁻ y, ENNReal.ofReal (F (x - y))) = ∫⁻ z, ENNReal.ofReal (F z) := by
    intro x
    exact lintegral_sub_left_eq_self (μ := (volume : Measure E))
      (fun z : E => ENNReal.ofReal (F z)) x
  -- Tonelli + translation invariance, computing the double integral of the `u ^ 2`-term
  have hK : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2))
      = (∫⁻ z, ENNReal.ofReal (F z)) * (∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
    have hFm' : AEMeasurable (fun z : E => ENNReal.ofReal (F z)) (volume : Measure E) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hFm
    have hMm : AEMeasurable (fun y : E => ENNReal.ofReal (u y ^ 2)) (volume : Measure E) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hum.pow_const 2)
    have h1 : AEMeasurable (fun w : E × E => ENNReal.ofReal (F w.1))
        ((volume : Measure E).prod volume) := hFm'.comp_fst
    have h2 : AEMeasurable (fun w : E × E => ENNReal.ofReal (u w.2 ^ 2))
        ((volume : Measure E).prod volume) := hMm.comp_snd
    have h3 : AEMeasurable
        (fun w : E × E => ENNReal.ofReal (F w.1) * ENNReal.ofReal (u w.2 ^ 2))
        ((volume : Measure E).prod volume) := h1.mul h2
    -- the shear `(x,y) ↦ (x-y,y)` is measure preserving, which gives the joint measurability
    have hS : Measure.QuasiMeasurePreserving (fun z : E × E => (z.1 - z.2, z.2))
        ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) :=
      (measurePreserving_sub_prod (volume : Measure E) volume).quasiMeasurePreserving
    have hjoint : AEMeasurable
        (fun p : E × E => ENNReal.ofReal (F (p.1 - p.2)) * ENNReal.ofReal (u p.2 ^ 2))
        ((volume : Measure E).prod volume) := by
      have hcomp : (fun p : E × E =>
            ENNReal.ofReal (F (p.1 - p.2)) * ENNReal.ofReal (u p.2 ^ 2))
          = (fun w : E × E => ENNReal.ofReal (F w.1) * ENNReal.ofReal (u w.2 ^ 2))
            ∘ (fun z : E × E => (z.1 - z.2, z.2)) := by
        funext p; simp
      rw [hcomp]; exact h3.comp_quasiMeasurePreserving hS
    rw [show (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2))
        = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2) from
          lintegral_congr (fun x => lintegral_congr (fun y => ENNReal.ofReal_mul (hF _)))]
    have hjoint' : AEMeasurable (Function.uncurry fun x y : E =>
        ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
        ((volume : Measure E).prod volume) := hjoint
    rw [lintegral_lintegral_swap (μ := (volume : Measure E)) (ν := (volume : Measure E))
      (f := fun x y : E => ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2)) hjoint']
    have hinner : ∀ y : E, (∫⁻ x, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
        = (∫⁻ z, ENNReal.ofReal (F z)) * ENNReal.ofReal (u y ^ 2) := by
      intro y
      calc (∫⁻ x, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
          = ∫⁻ x, (fun z => ENNReal.ofReal (F z) * ENNReal.ofReal (u y ^ 2)) (x - y) := rfl
        _ = ∫⁻ x, ENNReal.ofReal (F x) * ENNReal.ofReal (u y ^ 2) :=
              lintegral_sub_right_eq_self (μ := (volume : Measure E))
                (fun z : E => ENNReal.ofReal (F z) * ENNReal.ofReal (u y ^ 2)) y
        _ = (∫⁻ z, ENNReal.ofReal (F z)) * ENNReal.ofReal (u y ^ 2) :=
              lintegral_mul_const'' _ hFm'
    rw [show (∫⁻ y, ∫⁻ x, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
        = ∫⁻ y, (∫⁻ z, ENNReal.ofReal (F z)) * ENNReal.ofReal (u y ^ 2) from
          lintegral_congr hinner]
    exact lintegral_const_mul'' _ hMm
  -- assemble
  calc (∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ))
      ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y)))
            * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) :=
        lintegral_mono (fun x => hcs x)
    _ = ∫⁻ x, (∫⁻ z, ENNReal.ofReal (F z))
            * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) := by
        refine lintegral_congr (fun x => ?_)
        rw [htrans x]
    _ = (∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2) :=
        lintegral_const_mul' _ _ hAlt
    _ = (∫⁻ z, ENNReal.ofReal (F z))
          * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
        rw [hK]

end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.exists_contDiffOn_of_memSobolev =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.EllipticEst.InteriorRegularity

open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap BesselPotentialSpace ENNReal ContDiff

/-- **Fourier-side Sobolev representation.**

If `u ∈ H^m(E)` with `m > dim E / 2 + k`, then there is an `L²` function `F` whose moments up to
order `k` are integrable and which represents `𝓕 u`:

`𝓕 u = F`, `F ∈ L¹`, and `ξ ↦ ‖ξ‖^n ‖F ξ‖ ∈ L¹` for every `n ≤ k`.

Indeed `MemSobolev` gives `(1+‖ξ‖²)^{m/2} 𝓕u = f ∈ L²`; dividing by the weight produces the `L²`
function `F` with `‖F ξ‖ = (1+‖ξ‖²)^{-m/2} ‖f ξ‖`, and the moment claim is Cauchy–Schwarz against
`ξ ↦ ‖ξ‖^n (1+‖ξ‖²)^{-m/2} ∈ L²`, which holds exactly when `dim E < 2 (m - n)`. -/
theorem fourier_rep_of_memSobolev {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : 𝓢'(E, ℂ)} {k m : ℕ} (hm : (Module.finrank ℝ E : ℝ) / 2 + (k:ℝ) < (m:ℝ))
    (h : TemperedDistribution.MemSobolev (m:ℝ) 2 u) :
    ∃ G : Lp ℂ 2 (volume : Measure E),
      𝓕 u = (G : 𝓢'(E, ℂ)) ∧ Integrable (G : E → ℂ) (volume : Measure E) ∧
      (∀ n : ℕ, n ≤ k → Integrable (fun ξ : E => ‖ξ‖^n * ‖(G : E → ℂ) ξ‖) (volume : Measure E)) := by
  obtain ⟨f, hf⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp h
  have hgt : (jbC (E:=E) m).HasTemperateGrowth := jbC_temperate m
  have hgit : (jbCinv (E:=E) m).HasTemperateGrowth := jbCinv_temperate m
  let G : Lp ℂ 2 (volume : Measure E) :=
    MemLp.toLp (jbCinv (E:=E) m) (jbCinv_memLp (E:=E) m) • f
  have hG : G = MemLp.toLp (jbCinv (E:=E) m) (jbCinv_memLp (E:=E) m) • f := rfl
  have hfm : smulLeftCLM ℂ (jbC (E:=E) m) (𝓕 u) = (f : 𝓢'(E, ℂ)) := hf
  have hsm : smulLeftCLM ℂ (jbCinv (E:=E) m) (f : 𝓢'(E, ℂ)) = 𝓕 u := by
    rw [← hfm, smulLeftCLM_smulLeftCLM_apply hgt hgit, jbC_mul_jbCinv, smulLeftCLM_const,
      one_smul]
  have hFG : 𝓕 u = (G : 𝓢'(E, ℂ)) := by
    rw [← hsm, hG, Lp.toTemperedDistribution_smul_eq hgit (jbCinv_memLp (E:=E) m) f]
  have hcoe : (G : E → ℂ) =ᵐ[volume] fun ξ : E => jbCinv (E:=E) m ξ * (f : E → ℂ) ξ := by
    rw [hG]
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
        (MemLp.toLp (jbCinv (E:=E) m) (jbCinv_memLp (E:=E) m)) f,
      MemLp.coeFn_toLp (jbCinv_memLp (E:=E) m)] with ξ h1 h2
    rw [h1]
    simp only [Pi.mul_apply, smul_eq_mul]
    rw [h2]
  have hnorm : ∀ ξ : E, ‖jbCinv (E:=E) m ξ‖ = (1 + ‖ξ‖^2) ^ (-(m:ℝ)/2) := by
    intro ξ
    rw [jbCinv_eq m, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hmom : ∀ n : ℕ, n ≤ k → Integrable (fun ξ : E => ‖ξ‖^n * ‖(G : E → ℂ) ξ‖)
      (volume : Measure E) := by
    intro n hn
    have hn' : (Module.finrank ℝ E : ℝ) < 2 * ((m : ℝ) - (n : ℝ)) := by
      have h1 : ((n:ℝ) ≤ (k:ℝ)) := by exact_mod_cast hn
      have h2 : (Module.finrank ℝ E : ℝ) < 2 * ((m:ℝ) - (k:ℝ)) := by linarith [hm]
      linarith
    have hB : MemLp (fun ξ : E => ‖ξ‖^n * (1 + ‖ξ‖^2) ^ (-(m:ℝ)/2)) 2 (volume : Measure E) :=
      memLp_moment_weight (E := E) (n := n) (m := m) hn'
    have hC : MemLp (fun ξ : E => ‖(f : E → ℂ) ξ‖) 2 (volume : Measure E) :=
      (Lp.memLp f).norm
    have hBC : MemLp ((fun ξ : E => ‖ξ‖^n * (1 + ‖ξ‖^2) ^ (-(m:ℝ)/2)) *
        (fun ξ : E => ‖(f : E → ℂ) ξ‖)) 1 (volume : Measure E) := hB.mul hC
    refine (memLp_one_iff_integrable.mp hBC).congr ?_
    filter_upwards [hcoe] with ξ hξ
    rw [hξ, norm_mul, hnorm ξ]
    simp only [Pi.mul_apply]
    ring
  have hGint : Integrable (G : E → ℂ) (volume : Measure E) :=
    (hmom 0 (Nat.zero_le k)).mono' (Lp.memLp G).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by simp)
  exact ⟨G, hFG, hGint, hmom⟩

/-- **Local Sobolev embedding `H^m ⊆ C^k`.**

If `u ∈ H^m(E)` (Mathlib's Bessel potential space `TemperedDistribution.MemSobolev m 2`) with
`m > dim E / 2 + k`, then `u` is a `C^k` function locally: for every point `x` there is a radius
`r > 0` and a function `Φ`, of class `C^k` on `Metric.ball x r`, representing `u` on test
functions supported in that ball.

The proof is the standard Fourier-analytic one.  Write `𝓕 u = F` with
`(1+‖ξ‖²)^{m/2} F ∈ L²` (this is `MemSobolev`); then `F` is integrable and, for `n ≤ k`, the
weighted moment `ξ ↦ ‖ξ‖^n ‖F ξ‖` is integrable, because `‖ξ‖^n (1+‖ξ‖²)^{-m/2}` is square
integrable exactly when `dim E < 2 (m - n)`, which is what the hypothesis gives
(`fourier_rep_of_memSobolev`).  Hence `Φ := 𝓕⁻ F` is of class `C^k` by `Real.contDiff_fourier`,
and the distributional identity `u ψ = ∫ ψ • Φ` follows from the Fourier self-adjointness
identity by Fubini. -/
theorem exists_contDiffOn_of_memSobolev {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : 𝓢'(E, ℂ)} {k m : ℕ} (hm : (Module.finrank ℝ E : ℝ) / 2 + k < m)
    (h : TemperedDistribution.MemSobolev (m : ℝ) 2 u) (x : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : E → ℂ, ContDiffOn ℝ k Φ (Metric.ball x r) ∧
      (∀ ψ : 𝓢(E, ℂ), (∀ y, ψ y ≠ 0 → y ∈ Metric.ball x r) →
        u ψ = ∫ y, ψ y • Φ y) := by
  obtain ⟨F, hF, hFint, hFmom⟩ := fourier_rep_of_memSobolev hm h
  have hc : ContDiff ℝ (k : ℕ∞ω) (𝓕 (F : E → ℂ)) := by
    refine Real.contDiff_fourier (N := (k : ℕ∞)) ?_
    intro n hn
    exact hFmom n (by exact_mod_cast hn)
  refine ⟨1, one_pos, fun y => 𝓕⁻ (F : E → ℂ) y, ?_, ?_⟩
  · have h1 : ContDiff ℝ (k : ℕ∞ω) (fun y : E => 𝓕 (F : E → ℂ) (-y)) := hc.comp contDiff_neg
    have h2 : (fun y : E => 𝓕⁻ (F : E → ℂ) y) = fun y : E => 𝓕 (F : E → ℂ) (-y) :=
      funext fun y => Real.fourierInv_eq_fourier_neg (F : E → ℂ) y
    rw [h2]
    exact h1.contDiffOn
  · intro ψ _
    calc u ψ = (𝓕⁻ (𝓕 u)) ψ := by rw [fourierInv_fourier_eq]
      _ = (𝓕 u) (𝓕⁻ ψ) := by rw [TemperedDistribution.fourierInv_apply]
      _ = ((F : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) (𝓕⁻ ψ) := by rw [hF]
      _ = ∫ ξ, 𝓕⁻ (ψ : E → ℂ) ξ • (F : E → ℂ) ξ := by
            rw [Lp.toTemperedDistribution_apply, SchwartzMap.fourierInv_coe]
      _ = ∫ ξ, (F : E → ℂ) ξ • 𝓕⁻ (ψ : E → ℂ) ξ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
            simp only [smul_eq_mul]
            ring
      _ = ∫ y, 𝓕⁻ (F : E → ℂ) y • (ψ : E → ℂ) y :=
            (integral_fourierInv_smul_eq_of_integrable hFint (SchwartzMap.integrable ψ)).symm
      _ = ∫ y, ψ y • 𝓕⁻ (F : E → ℂ) y := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only [smul_eq_mul]
            ring

end Work.EllipticEst.InteriorRegularity
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.young_l1_l2_eLpNorm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity

open MeasureTheory ENNReal


end Work.EllipticEst.InteriorRegularity
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.EFP.integral_mul_finset_sum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.EFP

theorem integral_mul_finset_sum (s : Finset ℕ) (c : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hint : ∀ m ∈ s, MeasureTheory.IntegrableOn
      (fun θ => f θ * e m θ * Real.cos θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, f θ * (∑ m ∈ s, c m * e m θ) * Real.cos θ)
      = ∑ m ∈ s, c m * (∫ θ in Work.Spaces.Iθ, f θ * e m θ * Real.cos θ) := by
  -- pointwise, the integrand is the finite sum of the individual integrands
  have hpt : ∀ θ, f θ * (∑ m ∈ s, c m * e m θ) * Real.cos θ
      = ∑ m ∈ s, c m * (f θ * e m θ * Real.cos θ) := by
    intro θ
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  simp only [hpt]
  -- linearity of the Bochner integral over a finite sum, then pull out the scalars
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl (fun m _ => by rw [MeasureTheory.integral_const_mul])
  · intro m hm
    exact (hint m hm).const_mul (c m)

end Work.EllipticEst.ModalSolution.EFP
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.EFP.sum_sq_orth_collapse =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.EFP

theorem sum_sq_orth_collapse (s : Finset ℕ) (c : ℕ → ℝ) (e : ℕ → ℝ → ℝ)
    (hcont : ∀ m, Continuous (e m))
    (horth : ∀ m ∈ s, ∀ n ∈ s, m ≠ n →
      (∫ θ in Work.Spaces.Iθ, e m θ * e n θ * Real.cos θ) = 0) :
    (∫ θ in Work.Spaces.Iθ, (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ)
      = ∑ m ∈ s, c m ^ 2 * (∫ θ in Work.Spaces.Iθ, e m θ ^ 2 * Real.cos θ) := by
  classical
  -- integrability of every summand on the compact interval `Iθ`
  have hint : ∀ m ∈ s, ∀ n ∈ s, MeasureTheory.Integrable
      (fun θ : ℝ => c m * c n * (e m θ * e n θ * Real.cos θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro m hm n hn
    have h1 : Continuous (fun θ : ℝ => e m θ * e n θ * Real.cos θ) :=
      ((hcont m).mul (hcont n)).mul Real.continuous_cos
    have hc : Continuous (fun θ : ℝ => c m * c n * (e m θ * e n θ * Real.cos θ)) :=
      continuous_const.mul h1
    exact ContinuousOn.integrableOn_compact isCompact_Icc hc.continuousOn
  -- pointwise expansion of the square into a double sum
  have hpt : ∀ θ : ℝ, (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ
      = ∑ m ∈ s, ∑ n ∈ s, c m * c n * (e m θ * e n θ * Real.cos θ) := by
    intro θ
    have hsq : (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ
        = (∑ m ∈ s, c m * e m θ) * (∑ n ∈ s, c n * e n θ * Real.cos θ) := by
      have hsm : (∑ n ∈ s, c n * e n θ) * Real.cos θ
          = ∑ n ∈ s, c n * e n θ * Real.cos θ :=
        Finset.sum_mul s (fun n => c n * e n θ) (Real.cos θ)
      calc (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ
          = ((∑ m ∈ s, c m * e m θ) * (∑ n ∈ s, c n * e n θ)) * Real.cos θ := by
            rw [sq]
        _ = (∑ m ∈ s, c m * e m θ) * ((∑ n ∈ s, c n * e n θ) * Real.cos θ) := by
            rw [mul_assoc]
        _ = (∑ m ∈ s, c m * e m θ) * (∑ n ∈ s, c n * e n θ * Real.cos θ) := by
            rw [hsm]
    calc (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ
        = (∑ m ∈ s, c m * e m θ) * (∑ n ∈ s, c n * e n θ * Real.cos θ) := hsq
      _ = ∑ m ∈ s, ∑ n ∈ s, c m * c n * (e m θ * e n θ * Real.cos θ) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => by ring))
  -- the inner sum over `n` collapses to the diagonal term `n = m`
  have hfix : ∀ m ∈ s, (∑ n ∈ s, ∫ θ in Work.Spaces.Iθ,
        c m * c n * (e m θ * e n θ * Real.cos θ))
      = c m ^ 2 * (∫ θ in Work.Spaces.Iθ, e m θ ^ 2 * Real.cos θ) := by
    intro m hm
    rw [Finset.sum_eq_single_of_mem m hm]
    · rw [MeasureTheory.integral_const_mul,
        show c m * c m = c m ^ 2 by ring]
      have hi : (∫ θ in Work.Spaces.Iθ, e m θ * e m θ * Real.cos θ)
          = (∫ θ in Work.Spaces.Iθ, e m θ ^ 2 * Real.cos θ) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro θ _
        ring
      rw [hi]
    · intro n hn hnm
      rw [MeasureTheory.integral_const_mul, horth m hm n hn (Ne.symm hnm), mul_zero]
  calc (∫ θ in Work.Spaces.Iθ, (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ,
          ∑ m ∈ s, ∑ n ∈ s, c m * c n * (e m θ * e n θ * Real.cos θ)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro θ _
        exact hpt θ
    _ = (∑ m ∈ s, ∫ θ in Work.Spaces.Iθ,
            ∑ n ∈ s, c m * c n * (e m θ * e n θ * Real.cos θ)) :=
        MeasureTheory.integral_finsetSum (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (s := s)
          (f := fun m θ => ∑ n ∈ s, c m * c n * (e m θ * e n θ * Real.cos θ))
          (fun m hm => MeasureTheory.integrable_finsetSum
            (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) s
            (f := fun n θ => c m * c n * (e m θ * e n θ * Real.cos θ))
            (fun n hn => hint m hm n hn))
    _ = (∑ m ∈ s, c m ^ 2 * (∫ θ in Work.Spaces.Iθ, e m θ ^ 2 * Real.cos θ)) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact (MeasureTheory.integral_finsetSum
            (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) s
            (f := fun n θ => c m * c n * (e m θ * e n θ * Real.cos θ))
            (fun n hn => hint m hm n hn)).trans (hfix m hm)

end Work.EllipticEst.ModalSolution.EFP
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.RGW.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution.RadGreenWeak

set_option autoImplicit false

/-- The growing indicial exponent `s⁺ = 2m/α` of the mode-`m` radial operator. -/
def sP (α : ℝ) (m : ℕ) : ℝ := 2 * (m : ℝ) / α

/-- The decaying indicial exponent `s⁻ = -(2m+5)/α` of the mode-`m` radial operator. -/
def sM (α : ℝ) (m : ℕ) : ℝ := -(2 * (m : ℝ) + 5) / α

/-- The weight exponent `q = (5-α)/α`. -/
def qW (α : ℝ) : ℝ := (5 - α) / α

/-- The weight `w(z) = z^q`, `q = (5-α)/α`. -/
def wgt (α : ℝ) (z : ℝ) : ℝ := z ^ qW α

/-- The radial part of `bslOp`: `(L u)(z) = -(α²z²u''(z) + α(5+α)z u'(z))`. -/
def Lneg (α : ℝ) (u : ℝ → ℝ) (z : ℝ) : ℝ :=
  -(α ^ 2 * z ^ 2 * deriv (deriv u) z + α * (5 + α) * z * deriv u z)

/-- The Lagrange coefficient `p(z) = α² z² w(z) = α² z^{q+2}`. -/
def pwt (α : ℝ) (z : ℝ) : ℝ := α ^ 2 * (z ^ 2 * wgt α z)

/-- The lower source kernel of `radGreen`: `t ↦ c t · t^{-1-s⁻} = c t · t^{(2m+5)/α-1}`. -/
def srcM (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)

/-- The upper source kernel of `radGreen`: `t ↦ c t · t^{-1-s⁺} = c t · t^{-2m/α-1}`. -/
def srcP (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ (-(2 * (m : ℝ) / α) - 1)


/-- `radGreen` in the notation of this development (definitional). -/
lemma radGreen_eq (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = 1 / (α * (4 * (m : ℝ) + 5)) *
          (z ^ sM α m * (∫ t in (0 : ℝ)..z, srcM α m c t)
            + z ^ sP α m * (∫ t in Set.Ioi z, srcP α m c t)) := rfl

end Work.EllipticEst.ModalSolution.RadGreenWeak
end
end
-- ===== merged: Submission.Work.FM.Core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FM

/-! ## The angular density: elementary rewrites -/

/-- Pulling the factor `1/s` out of the angular integral defining `L12dens`. -/
theorem L12dens_eq {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) :
    L12dens K f s = (∫ θ in Icc 0 (Real.pi / 2), K θ * f s θ) / s := by
  rw [L12dens, integral_div]



/-- `L₁₂^K` is additive in the profile. -/
theorem L12_add {K : ℝ → ℝ} {f g : ℝ → ℝ → ℝ} {ρ : ℝ}
    (hf : ∀ s, IntegrableOn (fun θ => K θ * f s θ / s) (Icc 0 (Real.pi / 2)))
    (hg : ∀ s, IntegrableOn (fun θ => K θ * g s θ / s) (Icc 0 (Real.pi / 2)))
    (hF : IntegrableOn (L12dens K f) (Ioi ρ)) (hG : IntegrableOn (L12dens K g) (Ioi ρ)) :
    L12 K (fun s θ => f s θ + g s θ) ρ = L12 K f ρ + L12 K g ρ := by
  rw [L12]
  have hpoint : ∀ s, L12dens K (fun s θ => f s θ + g s θ) s
      = L12dens K f s + L12dens K g s := by
    intro s
    rw [L12dens, L12dens, L12dens, ← integral_add (hf s) (hg s)]
    congr 1 with θ
    ring
  simp only [hpoint]
  exact integral_add hF hG

/-- `L₁₂^K` is homogeneous in the profile (no integrability needed: the Bochner
integral is total). -/
theorem L12_const_mul {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {ρ c : ℝ} :
    L12 K (fun s θ => c * f s θ) ρ = c * L12 K f ρ := by
  rw [L12]
  have hpoint : ∀ s, L12dens K (fun s θ => c * f s θ) s = c * L12dens K f s := by
    intro s
    rw [L12dens, L12dens, ← integral_const_mul]
    congr 1 with θ
    ring
  simp only [hpoint]
  exact integral_const_mul c _

/-! ## Calculus of the profile -/

theorem hasDerivAt_add_const (c z : ℝ) : HasDerivAt (fun t : ℝ => c + t) 1 z := by
  simpa using (hasDerivAt_id' (𝕜 := ℝ) z).const_add c

theorem hasDerivAt_one_add_sq (z : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + z)) z := by
  have h := hasDerivAt_add_const 1 z
  convert h.pow 2 using 1 <;> (first | (funext x; simp) | ring_nf)

theorem hasDerivAt_two_mul (z : ℝ) : HasDerivAt (fun t : ℝ => 2 * t) 2 z := by
  simpa using (hasDerivAt_id' (𝕜 := ℝ) z).const_mul 2

theorem hasDerivAt_inv_add_const (c x : ℝ) (h : c + x ≠ 0) :
    HasDerivAt (fun t : ℝ => (c + t)⁻¹) (-1 / (c + x) ^ 2) x := by
  have h1 := hasDerivAt_add_const c x
  convert h1.inv h using 1 <;> (first | (funext t; simp [Pi.inv_apply]) | ring_nf)

/-- `d/dt (a/(c+t)) = -a/(c+t)²`. -/
theorem hasDerivAt_div_add_const (a c x : ℝ) (h : c + x ≠ 0) :
    HasDerivAt (fun t : ℝ => a / (c + t)) (-a / (c + x) ^ 2) x := by
  have h2 := hasDerivAt_inv_add_const c x h
  convert h2.const_mul a using 1 <;>
    (first | (funext t; simp [Pi.inv_apply, div_eq_mul_inv]) | ring_nf)

theorem hasDerivAt_Fstar (z : ℝ) (hz : -1 < z) :
    HasDerivAt Fstar (2 * (1 - z) / (1 + z) ^ 3) z := by
  have hz1 : (1 + z) ^ 2 ≠ 0 := by
    have h : (0 : ℝ) < 1 + z := by linarith
    positivity
  have h := (hasDerivAt_two_mul z).div (hasDerivAt_one_add_sq z) hz1
  have hfun : ((fun t : ℝ => 2 * t) / fun t => (1 + t) ^ 2) = Fstar := by
    funext t; unfold Fstar; rfl
  rw [hfun] at h
  convert h using 1 <;>
    (first | (funext t; simp [Pi.div_apply]) | (field_simp; ring) | ring_nf)


theorem deriv_Fstar (z : ℝ) (hz : -1 < z) : deriv Fstar z = 2 * (1 - z) / (1 + z) ^ 3 :=
  (hasDerivAt_Fstar z hz).deriv


/-! ## The two improper integrals of the profile -/

theorem integral_Ioi_Fstar_div (z : ℝ) (hz : 0 ≤ z) :
    ∫ s in Ioi z, Fstar s / s = 2 / (1 + z) := by
  have hcongr : EqOn (fun s => Fstar s / s) (fun s => 2 / (1 + s) ^ 2) (Ioi z) := by
    intro s hs
    have hs0 : s ≠ 0 := by have := hs.out; linarith
    unfold Fstar
    first | (field_simp; ring) | (field_simp) | ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  have key := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t)) (g' := fun t : ℝ => 2 / (1 + t) ^ 2) (a := z) (l := 0)
    ?_ ?_ ?_
  · rw [key]
    ring
  · intro x hx
    have hx1 : (1 : ℝ) + x ≠ 0 := by have := hx.out; linarith
    have h := hasDerivAt_div_add_const (-2) 1 x hx1
    convert h using 1 <;> (first | ring | (funext t; simp) | (field_simp; ring))
  · intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by have := hx.out; linarith
    positivity
  · have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
    have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 := h2.const_mul (-2 : ℝ)
    simpa [div_eq_mul_inv] using h3




/-! ## The Riccati solution and the blow-up rate -/



/-! ## The self-similar family -/



end Work.FM
end
end
-- ===== merged: Submission.Work.FTS.BSSwirl.deriv_deriv_fcut_div_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology Filter

namespace Work.FTS.BSSwirl

/-- The radial part of the Laplacian applied to the cutoff potential `fcut(r/ε)/r`:
writing `g(s) = fcut(s/ε) · s⁻¹`, one has `g''(r) + 2 g'(r)/r = fcut''(r/ε)/(ε² r)`.

This is the elementary computation needed when writing
`Δ(fcut(‖z‖/ε)/‖z‖)` in polar coordinates. -/
theorem deriv_deriv_fcut_div_add (ε : ℝ) (hε : 0 < ε) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (fun s : ℝ => Work.FTS.BSSwirl.fcut (s / ε) * s⁻¹)) r
      + 2 * deriv (fun s : ℝ => Work.FTS.BSSwirl.fcut (s / ε) * s⁻¹) r / r
      = deriv (deriv Work.FTS.BSSwirl.fcut) (r / ε) / (ε ^ 2 * r) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hε0 : ε ≠ 0 := ne_of_gt hε
  -- smoothness of `fcut` and of `deriv fcut`
  have hd1 : Differentiable ℝ fcut := (contDiff_fcut 1).differentiable one_ne_zero
  have hd2 : Differentiable ℝ (deriv fcut) := ((contDiff_fcut 2).deriv').differentiable one_ne_zero
  have hfc : ∀ y : ℝ, HasDerivAt fcut (deriv fcut y) y := fun y => (hd1 y).hasDerivAt
  have hdfc : ∀ y : ℝ, HasDerivAt (deriv fcut) (deriv (deriv fcut) y) y := fun y => (hd2 y).hasDerivAt
  -- the derivatives of `s ↦ fcut (s / ε)` and `s ↦ deriv fcut (s / ε)`
  have hu : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fcut (s / ε)) (deriv fcut (s / ε) * (1/ε)) s := by
    intro s
    have h1 : HasDerivAt (fun y : ℝ => y / ε) (1 / ε) s := (hasDerivAt_id s).div_const ε
    have h2 := (hfc (s/ε)).comp s h1
    simpa [Function.comp_def] using h2
  have hdu : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => deriv fcut (s / ε)) (deriv (deriv fcut) (s / ε) * (1/ε)) s := by
    intro s
    have h1 : HasDerivAt (fun y : ℝ => y / ε) (1 / ε) s := (hasDerivAt_id s).div_const ε
    have h2 := (hdfc (s/ε)).comp s h1
    simpa [Function.comp_def] using h2
  -- the first derivative of `g s = fcut (s/ε) * s⁻¹` at `r`
  have hgr : deriv (fun s : ℝ => fcut (s / ε) * s⁻¹) r
      = deriv fcut (r / ε) * (1/ε) * r⁻¹ + fcut (r / ε) * (-(r^2)⁻¹) := by
    have h : HasDerivAt (fun s : ℝ => fcut (s / ε) * s⁻¹)
        (deriv fcut (r / ε) * (1/ε) * r⁻¹ + fcut (r / ε) * (-(r^2)⁻¹)) r :=
      (hu r).mul (hasDerivAt_inv hr0)
    exact h.deriv
  -- the derivative of `s ↦ -(s^2)⁻¹` at `r`
  have hq : HasDerivAt (fun s : ℝ => -(s^2)⁻¹) (2 / r^3) r := by
    have h1 : HasDerivAt (fun s : ℝ => s^2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h2 : HasDerivAt (fun s : ℝ => (s^2)⁻¹) (-(2*r) / (r^2)^2) r := h1.inv (pow_ne_zero 2 hr0)
    have h3 : HasDerivAt (fun s : ℝ => -((s^2)⁻¹)) (-(-(2*r)/(r^2)^2)) r := h2.neg
    have hv : -(-(2*r)/(r^2)^2) = 2/r^3 := by field_simp
    rw [hv] at h3
    exact h3
  -- the two halves of `deriv g` are differentiable, with the derivatives below
  have hF1 : HasDerivAt (fun s : ℝ => deriv fcut (s / ε) * (1/ε) * s⁻¹)
      ((deriv (deriv fcut) (r / ε) * (1/ε)) * (1/ε) * r⁻¹ + (deriv fcut (r / ε) * (1/ε)) * (-(r^2)⁻¹)) r := by
    have ha : HasDerivAt (fun s : ℝ => deriv fcut (s / ε) * (1/ε))
        (deriv (deriv fcut) (r/ε) * (1/ε) * (1/ε)) r := by
      have h : HasDerivAt (fun s : ℝ => deriv fcut (s / ε) * (1/ε))
          ((deriv (deriv fcut) (r/ε) * (1/ε)) * (1/ε)) r :=
        (hdu r).mul_const (1/ε)
      exact h
    have h : HasDerivAt (fun s : ℝ => deriv fcut (s / ε) * (1/ε) * s⁻¹)
        ((deriv (deriv fcut) (r/ε) * (1/ε) * (1/ε)) * r⁻¹ + (deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹)) r :=
      ha.mul (hasDerivAt_inv hr0)
    exact h
  have hF2 : HasDerivAt (fun s : ℝ => fcut (s / ε) * (-(s^2)⁻¹))
      ((deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹) + fcut (r/ε) * (2/r^3)) r := by
    have h : HasDerivAt (fun s : ℝ => fcut (s / ε) * (-(s^2)⁻¹))
        ((deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹) + fcut (r/ε) * (2/r^3)) r :=
      (hu r).mul hq
    exact h
  have hF : HasDerivAt (fun s : ℝ => deriv fcut (s / ε) * (1/ε) * s⁻¹ + fcut (s / ε) * (-(s^2)⁻¹))
      (((deriv (deriv fcut) (r/ε) * (1/ε)) * (1/ε)) * r⁻¹ + (deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹)
        + ((deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹) + fcut (r/ε) * (2/r^3))) r := hF1.add hF2
  -- `deriv g` is, near `r`, the explicit function `F`
  have hev : deriv (fun s : ℝ => fcut (s / ε) * s⁻¹) =ᶠ[𝓝 r]
      (fun s : ℝ => deriv fcut (s / ε) * (1/ε) * s⁻¹ + fcut (s / ε) * (-(s^2)⁻¹)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    have h : HasDerivAt (fun s : ℝ => fcut (s / ε) * s⁻¹)
        (deriv fcut (s / ε) * (1/ε) * s⁻¹ + fcut (s / ε) * (-(s^2)⁻¹)) s :=
      (hu s).mul (hasDerivAt_inv (ne_of_gt hs))
    exact h.deriv
  have hsec : deriv (deriv (fun s : ℝ => fcut (s / ε) * s⁻¹)) r
      = ((deriv (deriv fcut) (r / ε) * (1/ε)) * (1/ε)) * r⁻¹ + (deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹)
        + ((deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹) + fcut (r/ε) * (2/r^3)) := by
    rw [hev.deriv_eq, hF.deriv]
  rw [hsec, hgr]
  field_simp
  ring

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.integral_Ioi_mul_deriv_deriv_fcut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.BSSwirl

/-- `∫_0^∞ y · fcut''(y) dy = -1`.

Integrate by parts on `[0, 3]` (the second derivative of `fcut` is supported in `[1, 2]`, so the
integral over `Ioi 0` is the one over `[0, 3]`):

`∫_0^3 y · fcut''(y) dy = [y · fcut'(y)]_0^3 - ∫_0^3 fcut'(y) dy = 0 - (fcut 3 - fcut 0) = -1`.

This is the `n = 0` instance of the "moment" identity for the smooth cutoff, used when
differentiating the Newtonian potential of a compactly supported field. -/
theorem integral_Ioi_mul_deriv_deriv_fcut :
    ∫ y in Set.Ioi (0 : ℝ), y * deriv (deriv Work.FTS.BSSwirl.fcut) y = -1 := by
  have hd1 : Differentiable ℝ fcut := (contDiff_fcut 1).differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv fcut) := (contDiff_fcut 2).differentiable_deriv_two
  have hc1 : Continuous (deriv fcut) := (contDiff_fcut 2).continuous_deriv (by norm_num)
  have hc2 : Continuous (deriv (deriv fcut)) := by
    have h : ContDiff ℝ 0 (deriv^[2] fcut) :=
      ContDiff.iterate_deriv' (𝕜 := ℝ) 0 2 (contDiff_fcut 2)
    simpa [Function.iterate_succ, Function.comp_def] using h
  -- the integrand vanishes to the right of `2`
  have hzero : ∀ y ∈ Set.Ioi (0:ℝ) \ Set.Ioc (0:ℝ) 3, y * deriv (deriv fcut) y = 0 := by
    intro y hy
    have hy3 : 3 < y := by
      by_contra h
      exact hy.2 ⟨hy.1, le_of_not_gt h⟩
    rw [deriv_deriv_fcut_eq_zero_of_gt_two (by linarith), mul_zero]
  have hset : ∫ y in Set.Ioi (0:ℝ), y * deriv (deriv fcut) y
      = ∫ y in Set.Ioc (0:ℝ) 3, y * deriv (deriv fcut) y :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => hx.1) hzero
  -- integration by parts on `[0, 3]`
  have hibp : ∫ y in (0:ℝ)..3, y * deriv (deriv fcut) y
      = 3 * deriv fcut 3 - 0 * deriv fcut 0 - ∫ y in (0:ℝ)..3, (1:ℝ) * deriv fcut y := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun x : ℝ => x)
      (u' := fun _ => (1:ℝ)) (v := deriv fcut) (v' := deriv (deriv fcut)) ?_ ?_ ?_ ?_
    · intro x _
      exact hasDerivAt_id x
    · intro x _
      exact (hd2 x).hasDerivAt
    · exact intervalIntegrable_const
    · exact hc2.intervalIntegrable 0 3
  have hftc : ∫ y in (0:ℝ)..3, deriv fcut y = fcut 3 - fcut 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hd1 x).hasDerivAt)
      (hc1.intervalIntegrable 0 3)
  rw [hset, (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 3)).symm, hibp]
  have h3 : deriv fcut 3 = (0:ℝ) := deriv_fcut_eq_zero_of_gt_two (by norm_num)
  have h03 : (∫ y in (0:ℝ)..3, (1:ℝ) * deriv fcut y) = 1 := by
    rw [show (∫ y in (0:ℝ)..3, (1:ℝ) * deriv fcut y) = ∫ y in (0:ℝ)..3, deriv fcut y by
      simp only [one_mul]]
    rw [hftc, fcut_three, fcut_zero]
    norm_num
  rw [h3, h03]
  ring

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.ClassC.HonestCut.radGreen_compact_source =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.ClassC.HonestCut

/-! ## Elementary support facts

The source `c` of `radGreen_compact_source` is supported in `[1,2]`, so it vanishes
identically on `(0,1)` and on `(2,∞)`. -/





end Work.FTS.ClassC.HonestCut
end
end
-- ===== merged: Submission.Work.FTS.ClassC.HonestCut.radGreen_hasDerivAt_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.HonestCut


end Work.FTS.ClassC.HonestCut
end
-- ===== merged: Submission.Work.FTS.ClassC.TailDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- The radial tail lintegral of `g` at the angle `θ`:
`zTail g θ = ∫⁻_{s ∈ [0,∞)} ofReal ((D_z g(s,θ))² · w(s)²)`. -/
def zTail (g : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.Dz g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)

/-- The real part of the radial tail lintegral.  It is the honest value of `zTail g θ`
whenever the latter is finite, and `0` otherwise. -/
def zTailR (g : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ := ENNReal.toReal (zTail g θ)

@[simp] theorem zTailR_eq_toReal (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    zTailR g θ = ENNReal.toReal (zTail g θ) := rfl

theorem zTailR_nonneg (g : ℝ → ℝ → ℝ) (θ : ℝ) : 0 ≤ zTailR g θ :=
  ENNReal.toReal_nonneg

/-- The tail lintegral is the `∫⁻` of a nonnegative function, so it vanishes only if the
integrand does; in particular it is monotone in the obvious way. -/
theorem zTail_eq_lintegral (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    zTail g θ = MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
      (fun s => ENNReal.ofReal ((Work.Spaces.Dz g s θ) ^ 2 * (Work.Spaces.w s) ^ 2)) := rfl

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.VopGen.Core.cutoffTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter

namespace Work.FTS.ClassC.VopGen.Core

/-- If `χ N : ℝ → ℝ` are measurable, take values in `[0,1]`, and converge pointwise to `1`
on `(0,∞)`, then for every `g` integrable on `Iz = [0,∞)` the integrals
`∫ z in Iz, (χ N z)^2 * g z` converge to `∫ z in Iz, g z`.

This is the dominated convergence theorem with dominating function `‖g‖`: the pointwise
convergence holds on `(0,∞)`, and the missing point `0` is `volume`-null in
`volume.restrict Iz`. -/
theorem cutoffTendsto {χ : ℕ → ℝ → ℝ}
    (hχm : ∀ N, Measurable (χ N))
    (hχnn : ∀ N z, 0 ≤ χ N z) (hχle : ∀ N z, χ N z ≤ 1)
    (hsat : ∀ z : ℝ, 0 < z → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → χ N z = 1)
    {g : ℝ → ℝ} (hg : MeasureTheory.Integrable g (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    Filter.Tendsto (fun N : ℕ => ∫ z in Work.Spaces.Iz, (χ N z) ^ 2 * g z) Filter.atTop
      (nhds (∫ z in Work.Spaces.Iz, g z)) := by
  -- `Iz` is measurable, hence is a.e. equal to the whole space for `volume.restrict Iz`.
  have hae_mem : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Work.Spaces.Iz :=
    MeasureTheory.ae_restrict_mem measurableSet_Ici
  -- the single point `0` is null for the restricted measure
  have hzero : (MeasureTheory.volume.restrict Work.Spaces.Iz) {0} = 0 := by
    rw [MeasureTheory.Measure.restrict_apply (measurableSet_singleton 0)]
    simp [Work.Spaces.Iz]
  have hae_ne : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have : {a : ℝ | ¬ a ≠ 0} = {0} := by ext z; simp
    rw [this]; exact hzero
  -- pointwise convergence a.e.
  have hlim : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun N : ℕ => (χ N z) ^ 2 * g z) Filter.atTop (nhds (g z)) := by
    filter_upwards [hae_mem, hae_ne] with z hz hz0
    have hpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    obtain ⟨N₀, hN₀⟩ := hsat z hpos
    have heq : (fun N : ℕ => (χ N z) ^ 2 * g z) =ᶠ[Filter.atTop] (fun _ => g z) := by
      filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
      rw [hN₀ N hN]; ring
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  -- measurability of the approximants
  have hFmeas : ∀ N, MeasureTheory.AEStronglyMeasurable (fun z => (χ N z) ^ 2 * g z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    fun N => ((hχm N).pow_const 2).aestronglyMeasurable.mul hg.aestronglyMeasurable
  -- `‖g‖` dominates every approximant pointwise
  have hbound : ∀ N, ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖(χ N z) ^ 2 * g z‖ ≤ ‖g z‖ := by
    intro N
    filter_upwards with z
    have h1 : (χ N z) ^ 2 ≤ 1 := pow_le_one₀ (hχnn N z) (hχle N z)
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg (hχnn N z) 2)]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  exact MeasureTheory.tendsto_integral_of_dominated_convergence (fun z => ‖g z‖)
    hFmeas hg.norm hbound hlim

end Work.FTS.ClassC.VopGen.Core
end
-- ===== merged: Submission.Work.FTS.ClassC.aslotAux.ofReal_HkSq_eq_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.aslotAux

/-- Under the honesty hypothesis `HkMem`, the `lintegral` of the `ofReal`-integrand of `HkSq` is
the `ofReal` of the real iterated integral `HkSq α k f`. -/
theorem ofReal_HkSq_eq_lintegral {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α k f) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      = ENNReal.ofReal (Work.Spaces.HkSq α k f) := by
  -- The angular slice `z ↦ ∫_θ HkIntegrand α k f z θ` is nonnegative.
  have hnn1 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      fun s => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f s σ :=
    Eventually.of_forall fun s =>
      integral_nonneg fun σ => Work.Spaces.HkIntegrand_nonneg α k f s σ
  -- The outer Bochner integral of the nonnegative integrand is the `ofReal`-integral of its
  -- `lintegral`, by `HkMem.2`.
  have hstep : ENNReal.ofReal (Work.Spaces.HkSq α k f)
      = ∫⁻ s in Work.Spaces.Iz,
          ENNReal.ofReal (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f s σ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal h.2 hnn1
  rw [hstep]
  -- On `Iz` the same collapse holds slicewise, by `HkMem.1`.
  refine MeasureTheory.lintegral_congr_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_)
  intro s hs
  have hnn2 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      fun σ => Work.Spaces.HkIntegrand α k f s σ :=
    Eventually.of_forall fun σ => Work.Spaces.HkIntegrand_nonneg α k f s σ
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (h.1 s hs) hnn2).symm

end Work.FTS.ClassC.aslotAux
end
end
-- ===== merged: Submission.Work.FTS.ClassC.euler_ode_unique =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set MeasureTheory

namespace Work.FTS.ClassC

set_option autoImplicit false



end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.euler_weak_gronwall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassC


end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.modeSum_arith =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open MeasureTheory

/-- **Cauchy–Schwarz for a finite family with a pointwise squared domination.**

If `g i ^ 2 ≤ h i` for every `i ∈ S`, then
`(∑ i ∈ S, f i * g i) ^ 2 ≤ (∑ i ∈ S, f i ^ 2) * (∑ i ∈ S, h i)`.

The proof is the classical Cauchy–Schwarz inequality `Finset.sum_mul_sq_le_sq_mul_sq`
followed by monotonicity of the product in the second factor. -/
private lemma cs_mode_sum {ι : Type*} (S : Finset ι) (f g h : ι → ℝ)
    (hgh : ∀ i ∈ S, g i ^ 2 ≤ h i) :
    (∑ i ∈ S, f i * g i) ^ 2 ≤ (∑ i ∈ S, f i ^ 2) * (∑ i ∈ S, h i) := by
  have h1 : (∑ i ∈ S, f i * g i) ^ 2 ≤ (∑ i ∈ S, f i ^ 2) * (∑ i ∈ S, g i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq S f g
  have h2 : (∑ i ∈ S, g i ^ 2) ≤ ∑ i ∈ S, h i := Finset.sum_le_sum hgh
  have h3 : 0 ≤ ∑ i ∈ S, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 h3)

theorem modeSum_arith {N : ℕ} {a c : ℕ → ℝ → ℝ} {μ : ℕ → ℝ}
    (hμ : ∀ m, 0 < μ m)
    (hper : ∀ m, m ≤ N →
      μ m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ Real.sqrt (∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2)) :
    (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
        * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2
      ≤ (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
          * (∑ m ∈ Finset.range (N + 1),
              ∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  classical
  -- Per-mode: `(μ m * √(∫ a² w²)) ^ 2 ≤ ∫ c² w²`.
  have hstep : ∀ m ∈ Finset.range (N + 1),
      (μ m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2
        ≤ ∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hle := hper m (by omega)
    have hT : 0 ≤ ∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      setIntegral_nonneg_of_ae (Filter.Eventually.of_forall fun z =>
        mul_nonneg (sq_nonneg (c m z)) (sq_nonneg (Work.Spaces.w z)))
    have hA : 0 ≤ μ m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
      mul_nonneg (le_of_lt (hμ m)) (Real.sqrt_nonneg _)
    have h2 := mul_self_le_mul_self hA hle
    have hsq : Real.sqrt (∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2)
        = ∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
      rw [← pow_two]
      exact Real.sq_sqrt hT
    rw [hsq] at h2
    rw [pow_two]
    exact h2
  -- Rewrite each summand as `(((m+1)/μ m) * (μ m * √(∫ a² w²)))`.
  have hsum : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
        * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2))
      = ∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m)
          * (μ m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    apply Finset.sum_congr rfl
    intro m _
    have hne : μ m ≠ 0 := ne_of_gt (hμ m)
    field_simp
  rw [hsum]
  exact cs_mode_sum (Finset.range (N + 1))
    (fun m => (((m : ℝ) + 1) / μ m))
    (fun m => μ m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2))
    (fun m => ∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2)
    hstep

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.modeSum_muSeq_sum_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

/-- The explicit form of the mode weight: `λ_m = 2m(2m+5) = 4m² + 10m`. -/
private lemma lamR_eq (m : ℕ) :
    Work.FTS.PhiStar.Radial.lamR m = 4 * (m : ℝ) ^ 2 + 10 * (m : ℝ) := by
  simp only [Work.FTS.PhiStar.Radial.lamR]
  ring

/-- The correction `3α² + 3α(5+α)/2` is at most `69/32` for `0 < α ≤ 1/4`
(the value at `α = 1/4`, where the quadratic `(9/2)α² + (15/2)α` is increasing). -/
private lemma correction_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    3 * α ^ 2 + 3 * α * (5 + α) / 2 ≤ 69 / 32 := by
  have hα_nn : 0 ≤ α := le_of_lt hα
  have hkey : α ^ 2 ≤ α / 4 := by
    nlinarith [mul_nonneg hα_nn (sub_nonneg.mpr hα4)]
  nlinarith [hkey, hα4, hα_nn]

/-- The harmonic tail `∑_{m ≤ N} (if m = 0 then 1 else 1/(4m²)) ≤ 2`.  The `m = 0` term is `1`
and the rest is dominated by `∑_{m ≥ 1} (1/m - 1/(m+1)) ≤ 1`. -/
private lemma harm_tail_le (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), (if m = 0 then (1 : ℝ) else 1 / (4 * (m : ℝ) ^ 2))) ≤ 2 := by
  have key : ∀ n : ℕ,
      (∑ m ∈ Finset.range (n + 1), (if m = 0 then (1 : ℝ) else 1 / (4 * (m : ℝ) ^ 2)))
        ≤ 2 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hf : (if k + 1 = 0 then (1 : ℝ) else 1 / (4 * ((k + 1 : ℕ) : ℝ) ^ 2))
          = 1 / (4 * ((k : ℝ) + 1) ^ 2) := by
        simp
      rw [hf]
      have hstep : (1 : ℝ) / (4 * ((k : ℝ) + 1) ^ 2) ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
        have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have h : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
          rw [div_sub_div _ _ (ne_of_gt hk) (ne_of_gt hk2)]
          ring
        rw [h, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hcast : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      linarith
  have h := key N
  have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  linarith

/-- Per-mode bound: for `m ≥ 1` the denominator `λ_m - 3α² - 3α(5+α)/2` is at least `4m²`, while
the numerator `m+1` is at most `2m`; hence the squared quotient is at most `1/(4m²)`.  For `m = 0`
the quotient is `1`.  (`0 < α ≤ 1/4` makes the denominator bigger than `4m²` since
`3α² + 3α(5+α)/2 ≤ 69/32 < 10m` for `m ≥ 1`.) -/
private lemma mode_term_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) :
    (((m : ℝ) + 1) / (if m = 0 then 1 else
        Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)) ^ 2
      ≤ (if m = 0 then (1 : ℝ) else 1 / (4 * (m : ℝ) ^ 2)) := by
  by_cases hm : m = 0
  · subst hm; norm_num
  · rw [ite_eq_right hm, ite_eq_right hm]
    have hcorr := correction_le α hα hα4
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      exact_mod_cast this
    have hmpos : 0 < (m : ℝ) := by linarith
    have hlam := lamR_eq m
    have hden_ge : 4 * (m : ℝ) ^ 2 ≤
        Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
      rw [hlam]; nlinarith [hcorr, hm1]
    have hden_pos : 0 <
        Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
      have : (0 : ℝ) < 4 * (m : ℝ) ^ 2 := by positivity
      linarith
    have hnum : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
    have hstep : ((m : ℝ) + 1) /
        (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)
          ≤ 1 / (2 * (m : ℝ)) := by
      rw [div_le_div_iff₀ hden_pos (by positivity)]
      nlinarith [hden_ge, hnum, hmpos]
    have h1 : 0 ≤ ((m : ℝ) + 1) /
        (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) := by
      positivity
    calc (((m : ℝ) + 1) /
            (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)) ^ 2
        ≤ (1 / (2 * (m : ℝ))) ^ 2 := pow_le_pow_left₀ h1 hstep 2
      _ = 1 / (4 * (m : ℝ) ^ 2) := by field_simp; ring

theorem modeSum_muSeq_sum_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1),
        (((m : ℝ) + 1) / (if m = 0 then 1 else
          Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)) ^ 2) ≤ 8 := by
  calc (∑ m ∈ Finset.range (N + 1),
        (((m : ℝ) + 1) / (if m = 0 then 1 else
          Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)) ^ 2)
      ≤ ∑ m ∈ Finset.range (N + 1), (if m = 0 then (1 : ℝ) else 1 / (4 * (m : ℝ) ^ 2)) :=
        Finset.sum_le_sum (fun m _ => mode_term_le α hα hα4 m)
    _ ≤ 2 := harm_tail_le N
    _ ≤ 8 := by norm_num

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.weighted_l2_modeSum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- **Minkowski (triangle) inequality in the weighted `L²` space `L²(𝕀_z, w²dz)`**
for a finite weighted sum of modes: with `c m ≥ 0` and each `a m` square-integrable
against `w²` on `𝕀_z`,

`∫_{𝕀_z} w² · (∑_{m≤N} c m |a m|)² ≤ (∑_{m≤N} c m √(∫_{𝕀_z} a m² w²))².`

This is the elementary form of `‖∑_m c m |f_m|‖_{L²(w²)} ≤ ∑_m c m ‖f_m‖_{L²(w²)}`:
the proof runs the abstract `eLpNorm` triangle inequality `eLpNorm_sum_le` on the
`AEStronglyMeasurable` functions `z ↦ √(a m z ² w z ²)` (which agree with
`w · |a m|` on `𝕀_z`) and then converts `eLpNorm · 2` back to the square root of the
Bochner integral via `MemLp.eLpNorm_eq_integral_rpow_norm`. -/
theorem weighted_l2_modeSum {N : ℕ} {a : ℕ → ℝ → ℝ} {c : ℕ → ℝ} (hc : ∀ m, 0 ≤ c m)
    (hint : ∀ m, m ≤ N → MeasureTheory.IntegrableOn
      (fun z => (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∑ m ∈ Finset.range (N + 1), c m * |a m z|) ^ 2)
      ≤ (∑ m ∈ Finset.range (N + 1),
          c m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2 := by
  classical
  -- the `2`-norm is the square root of the integral of the square
  have eLpNorm_two_eq : ∀ (f : ℝ → ℝ) (ν : Measure ℝ), MemLp f 2 ν →
      eLpNorm f 2 ν = ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂ν)) := by
    intro f ν hf
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    congr 1
    rw [show (2 : ENNReal).toReal = 2 by norm_num,
      show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
    simp only [Real.rpow_natCast]
  set S : Finset ℕ := Finset.range (N + 1) with hS
  set μ : Measure ℝ := volume.restrict Work.Spaces.Iz with hμ
  set g : ℕ → ℝ → ℝ := fun m z => Real.sqrt ((a m z) ^ 2 * (Work.Spaces.w z) ^ 2) with hg
  -- `m ∈ S ↔ m ≤ N`
  have hmemS : ∀ m, m ∈ S → m ≤ N := by
    intro m hm
    rw [hS] at hm
    simp only [Finset.mem_range] at hm
    omega
  -- integrability of the `m`-th mode against `w²`, as a measure on `𝕀_z`
  have hInt : ∀ m, m ∈ S → Integrable (fun z => (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) μ := by
    intro m hm
    rw [hμ]
    exact hint m (hmemS m hm)
  -- the algebraic identity `g m z ^ 2 = a m z ^ 2 * w z ^ 2`
  have hg_sq : ∀ m z, (g m z) ^ 2 = (a m z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro m z
    simp only [hg]
    exact Real.sq_sqrt (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hg_meas : ∀ m, m ∈ S → AEStronglyMeasurable (g m) μ := by
    intro m hm
    have h := Real.continuous_sqrt.comp_aestronglyMeasurable
      ((hInt m hm).aestronglyMeasurable)
    simpa only [hg] using h
  have hg_memLp : ∀ m, m ∈ S → MemLp (g m) 2 μ := by
    intro m hm
    refine (memLp_two_iff_integrable_sq (hg_meas m hm)).mpr ?_
    exact (hInt m hm).congr (Filter.Eventually.of_forall fun z => (hg_sq m z).symm)
  -- the function whose `L²` norm is the left-hand side
  set F : ℝ → ℝ := ∑ m ∈ S, (fun z => c m * g m z) with hF
  have hF_memLp : MemLp F 2 μ := by
    have h := memLp_finsetSum' (α := ℝ) (p := 2) (μ := μ) (s := S)
      (f := fun m => fun z => c m * g m z) (fun m hm => ?_)
    · rwa [← hF] at h
    · exact (hg_memLp m hm).const_smul (c m)
  have hF_apply : ∀ z, F z = ∑ m ∈ S, c m * g m z := by
    intro z
    simpa only [hF] using Finset.sum_apply z S (fun m z' => c m * g m z')
  have hF_nonneg : ∀ z, 0 ≤ F z := by
    intro z
    rw [hF_apply z]
    exact Finset.sum_nonneg fun m _ => mul_nonneg (hc m) (Real.sqrt_nonneg _)
  -- the pointwise identity `g m z = |a m z| * |w z|`
  have hg_val : ∀ m z, g m z = Real.sqrt ((a m z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro m z
    rw [hg]
  have hg_abs : ∀ m z, g m z = |a m z| * |Work.Spaces.w z| := by
    intro m z
    rw [hg_val m z]
    rw [show (a m z) ^ 2 * (Work.Spaces.w z) ^ 2
          = (|a m z| * |Work.Spaces.w z|) ^ 2 by rw [mul_pow, sq_abs, sq_abs]]
    rw [Real.sqrt_sq_eq_abs (|a m z| * |Work.Spaces.w z|),
      abs_of_nonneg (mul_nonneg (abs_nonneg (a m z)) (abs_nonneg (Work.Spaces.w z)))]
  -- the `L²` norm of `F` is `√(∫_{𝕀_z} w² (∑ c m |a m|)²)`
  have hnormF : (∫ x, ‖F x‖ ^ 2 ∂μ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (∑ m ∈ S, c m * |a m z|) ^ 2 := by
    rw [hμ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have h1 : (∑ m ∈ S, c m * g m z)
        = (∑ m ∈ S, c m * |a m z|) * |Work.Spaces.w z| := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by rw [hg_abs m z]; ring
    show ‖F z‖ ^ 2 = (Work.Spaces.w z) ^ 2 * (∑ m ∈ S, c m * |a m z|) ^ 2
    rw [hF_apply z, h1,
      Real.norm_of_nonneg (mul_nonneg (Finset.sum_nonneg fun m _ =>
        mul_nonneg (hc m) (abs_nonneg _)) (abs_nonneg _)), mul_pow, sq_abs]
    ring
  -- the `L²` norm of the `m`-th mode against `w²`
  have hnormg : ∀ m, m ∈ S → (∫ x, ‖g m x‖ ^ 2 ∂μ)
      = ∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro m hm
    rw [hμ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ‖g m z‖ ^ 2 = (a m z) ^ 2 * (Work.Spaces.w z) ^ 2
    rw [hg_val m z, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_nonneg (sq_nonneg (a m z)) (sq_nonneg (Work.Spaces.w z)))]
  -- Minkowski in `eLpNorm` form
  have hkey : eLpNorm F 2 μ ≤ ∑ m ∈ S, eLpNorm (fun z => c m * g m z) 2 μ := by
    have h1 := eLpNorm_sum_le (s := S) (f := fun m z => c m * g m z) (p := 2) (μ := μ)
      (by norm_num : (1 : ENNReal) ≤ 2)
    rw [← hF] at h1
    exact h1
  -- identification of the left-hand side
  have hLHS : eLpNorm F 2 μ
      = ENNReal.ofReal (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∑ m ∈ S, c m * |a m z|) ^ 2)) := by
    rw [eLpNorm_two_eq F μ hF_memLp, hnormF]
  -- identification of the right-hand side
  have hsingle : ∀ m ∈ S, eLpNorm (fun z => c m * g m z) 2 μ
      = ENNReal.ofReal (c m
          * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    intro m hm
    have hcs := eLpNorm_const_smul (c m) (g m) (2 : ENNReal) μ
    rw [show (c m • g m) = (fun z => c m * g m z) from by
          funext z; simp only [Pi.smul_apply, smul_eq_mul]] at hcs
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hc m)] at hcs
    rw [hcs, eLpNorm_two_eq (g m) μ (hg_memLp m hm), hnormg m hm,
      ENNReal.ofReal_mul (hc m)]
  have hRHS : (∑ m ∈ S, eLpNorm (fun z => c m * g m z) 2 μ)
      = ENNReal.ofReal (∑ m ∈ S, c m
          * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    rw [Finset.sum_congr rfl (fun m hm => hsingle m hm),
      ENNReal.ofReal_sum_of_nonneg (fun m _ => mul_nonneg (hc m) (Real.sqrt_nonneg _))]
  -- the `ENNReal` inequality
  have hmain : ENNReal.ofReal (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∑ m ∈ S, c m * |a m z|) ^ 2))
      ≤ ENNReal.ofReal (∑ m ∈ S, c m
          * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    rw [← hLHS, ← hRHS]
    exact hkey
  -- pass to the real inequality, square, and unfold `S`
  have hB : 0 ≤ ∑ m ∈ S, c m
      * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    Finset.sum_nonneg fun m _ => mul_nonneg (hc m) (Real.sqrt_nonneg _)
  have hle : Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∑ m ∈ S, c m * |a m z|) ^ 2)
      ≤ ∑ m ∈ S, c m
          * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff hB).mp hmain
  have hA : 0 ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∑ m ∈ S, c m * |a m z|) ^ 2 :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsq : (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∑ m ∈ S, c m * |a m z|) ^ 2)) ^ 2
      ≤ (∑ m ∈ S, c m
          * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2 :=
    sq_le_sq' (by linarith [Real.sqrt_nonneg (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∑ m ∈ S, c m * |a m z|) ^ 2), hB]) hle
  rw [Real.sq_sqrt hA] at hsq
  rw [hS] at hsq
  exact hsq

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.CmpSupp.hkSq_le_of_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.CmpSupp

/-- `∫⁻` of `ofReal` of the `H^k`-integrand, compared with the real-valued iterated
integral `HkSq`: the two agree because the integrand is nonnegative and integrable
(`HkMem`).  Stated on the half-line `Ioi 0` (which differs from `Iz = Ici 0` by the
null set `{0}`). -/
theorem lintegral_HkIntegrand_eq {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k Ψ) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ))
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k Ψ z θ) := by
  have hinner : (fun z => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k Ψ z θ))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        (fun z => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    refine MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hmem.1 z ?_) (Filter.Eventually.of_forall fun θ => ?_)
    · rw [Work.Spaces.Iz]; exact le_of_lt (Set.mem_Ioi.mp hz)
    · exact Work.Spaces.HkIntegrand_nonneg α k Ψ z θ
  have hIoi_eq_Iz : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  have hInt : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k Ψ z θ)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [hIoi_eq_Iz]
    exact hmem.2
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ) :=
    Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k Ψ z θ
  rw [← MeasureTheory.lintegral_congr_ae hinner]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn).symm

theorem hkSq_le_of_lintegral {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmem : Work.Spaces.HkMem α 0 Ψ)
    (hfin : (∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Ψ z θ)) ≤ ENNReal.ofReal C) :
    Work.Spaces.HkSq α 0 Ψ ≤ C := by
  have hEq := lintegral_HkIntegrand_eq (k := 0) hmem
  have hIoi_eq_Iz : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  have h1 : ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 Ψ z θ) ≤ ENNReal.ofReal C := by
    rw [← hEq]
    exact hfin
  have hle : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 Ψ z θ) ≤ C :=
    (ENNReal.ofReal_le_ofReal_iff hC).mp h1
  calc Work.Spaces.HkSq α 0 Ψ
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 Ψ z θ := rfl
    _ = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 Ψ z θ := by rw [← hIoi_eq_Iz]
    _ ≤ C := hle

end Work.FTS.ClassCHon.CmpSupp
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassAux.continuousOn_of_integral_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.SliceMassAux

open MeasureTheory Filter Topology

theorem continuousOn_of_integral_bound {m Φ : ℝ → ℝ}
    (hΦ : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ))) (hnn : ∀ z, 0 ≤ Φ z)
    (h : ∀ z₁ z₂ : ℝ, 0 < z₁ → z₁ ≤ z₂ →
      |m z₂ - m z₁| ≤ ∫ s in z₁..z₂, Φ s) :
    ContinuousOn m (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : 0 < x := hx
  -- The primitive of `Φ` is continuous at `x`.
  have hsub : Set.uIcc (x / 2) (2 * x) ⊆ Set.Ioi 0 := by
    intro y hy
    rw [Set.mem_Ioi]
    rcases Set.mem_uIcc.mp hy with ⟨h1, -⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have hint : IntervalIntegrable Φ volume (x / 2) (2 * x) :=
    MeasureTheory.IntegrableOn.intervalIntegrable (hΦ.mono_set hsub)
  have hcw : ContinuousWithinAt (fun b => ∫ s in x..b, Φ s) (Set.Icc (x / 2) (2 * x)) x := by
    refine intervalIntegral.continuousWithinAt_primitive (μ := volume) (f := Φ)
      (a := x) (b₀ := x) (b₁ := x / 2) (b₂ := 2 * x) ?_ ?_
    · exact Real.volume_singleton
    · rw [min_eq_right (by linarith : x / 2 ≤ x), max_eq_right (by linarith : x ≤ 2 * x)]
      exact hint
  have hcAt : ContinuousAt (fun b => ∫ s in x..b, Φ s) x :=
    hcw.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hcwI : ContinuousWithinAt (fun b => ∫ s in x..b, Φ s) (Set.Ioi 0) x :=
    hcAt.continuousWithinAt
  have htend : Tendsto (fun b => ∫ s in x..b, Φ s) (𝓝[Set.Ioi (0:ℝ)] x) (𝓝 0) := by
    simpa using hcwI.tendsto
  have hlimAbs : Tendsto (fun y => |∫ s in x..y, Φ s|) (𝓝[Set.Ioi (0:ℝ)] x) (𝓝 0) := by
    simpa using htend.abs
  -- The pointwise bound.
  have hbound : ∀ y, 0 < y → |m y - m x| ≤ |∫ s in x..y, Φ s| := by
    intro y hy
    rcases le_or_gt x y with hxy | hyx
    · refine le_trans (h x y hx0 hxy) ?_
      exact le_of_eq (abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall hxy hnn)).symm
    · have h1 : |m y - m x| ≤ ∫ s in y..x, Φ s := by
        have := h y x hy hyx.le
        rwa [abs_sub_comm] at this
      refine le_trans h1 ?_
      rw [intervalIntegral.integral_symm x y]
      exact neg_le_abs _
  have hev : ∀ᶠ y in 𝓝[Set.Ioi (0:ℝ)] x, |m y - m x| ≤ |∫ s in x..y, Φ s| := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hbound y hy
  have hm : Tendsto (fun y => |m y - m x|) (𝓝[Set.Ioi (0:ℝ)] x) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun y => abs_nonneg _)) hev hlimAbs
  show Tendsto m (𝓝[Set.Ioi (0:ℝ)] x) (𝓝 (m x))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using hm

end Work.FTS.ClassCHon.SliceMassAux
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.Ioi_tail_sq_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T.Hardy

open MeasureTheory Set Filter
open scoped Topology
open scoped Interval

/-- **Cauchy–Schwarz for the Bochner integral of real functions.**
`(∫ f g)² ≤ (∫ f²)(∫ g²)`, proved via the (non-negative) quadratic form
`t ↦ ∫ (f + t g)²` and its discriminant. -/
theorem cs_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  set A := ∫ x, f x ^ 2 ∂μ
  set B := ∫ x, f x * g x ∂μ
  set C := ∫ x, g x ^ 2 ∂μ
  have hC0 : 0 ≤ C := integral_nonneg (fun x => sq_nonneg (g x))
  have hquad : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C := by
    intro t
    have hexp : ∫ x, (f x + t * g x) ^ 2 ∂μ = A + 2 * t * B + t ^ 2 * C := by
      have h1 : (fun x => (f x + t * g x) ^ 2)
          = fun x => (f x ^ 2 + 2 * t * (f x * g x)) + t ^ 2 * g x ^ 2 := by
        funext x; ring
      rw [h1]
      rw [integral_add (f := fun x => f x ^ 2 + 2 * t * (f x * g x))
        (g := fun x => t ^ 2 * g x ^ 2) (hf2.add (hfg.const_mul (2 * t)))
        (hg2.const_mul (t ^ 2))]
      rw [integral_add hf2 (hfg.const_mul (2 * t)), integral_const_mul, integral_const_mul]
    have hnn : 0 ≤ ∫ x, (f x + t * g x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    linarith [hnn, hexp]
  rcases eq_or_lt_of_le hC0 with hCeq | hCpos
  · have hB0 : B = 0 := by
      by_contra hBne
      have hbad := hquad (-(A + 1) / (2 * B))
      have key : A + 2 * (-(A + 1) / (2 * B)) * B + (-(A + 1) / (2 * B)) ^ 2 * C = -1 := by
        rw [← hCeq]; field_simp; ring
      linarith [hbad, key]
    rw [hB0, ← hCeq]; norm_num
  · have hbad := hquad (-B / C)
    have key : A + 2 * (-B / C) * B + (-B / C) ^ 2 * C = A - B ^ 2 / C := by
      field_simp; ring
    have hle : B ^ 2 / C ≤ A := by linarith [hbad, key]
    have h2 : B ^ 2 ≤ A * C := by
      rw [div_le_iff₀ hCpos] at hle
      linarith [hle]
    exact h2

/-- The elementary AM–GM step for the tail Hardy inequality: pointwise
`(z · F z) · G z ≤ (1/4) F z² + z² G z²` (with `F z = ∫_{Ioi z} G`), integrated
over `[1,R]`. -/
theorem tail_amgm (G : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (fun s => (G s) ^ 2 * s ^ 2) (Set.Ioi 1))
    (hG : MeasureTheory.IntegrableOn G (Set.Ioi 1)) (R : ℝ) (hR : 1 < R) :
    ∫ z in (1:ℝ)..R, (z * (∫ s in Set.Ioi z, G s)) * G z
      ≤ (1/4) * (∫ z in (1:ℝ)..R, (∫ s in Set.Ioi z, G s) ^ 2)
        + ∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2 := by
  have hcont : ContinuousOn (fun z => ∫ s in Set.Ioi z, G s) (Set.Ici 1) :=
    Pieces.tail_continuous G hG
  have hpoint : ∀ x : ℝ, (x * (∫ s in Set.Ioi x, G s)) * G x
      ≤ (1/4) * (∫ s in Set.Ioi x, G s) ^ 2 + (G x) ^ 2 * x ^ 2 := by
    intro x
    nlinarith [sq_nonneg ((∫ s in Set.Ioi x, G s) / 2 - x * G x)]
  have hGint : IntervalIntegrable G volume (1:ℝ) R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr (hG.mono_set Set.Ioc_subset_Ioi_self)
  have hcontu : ContinuousOn (fun z => ∫ s in Set.Ioi z, G s) (Set.uIcc (1:ℝ) R) :=
    hcont.mono (by rw [Set.uIcc_of_le hR.le]; exact fun x hx => hx.1)
  have hcontA : ContinuousOn (fun z => z * (∫ s in Set.Ioi z, G s)) (Set.uIcc (1:ℝ) R) :=
    continuousOn_id.mul hcontu
  have hf : IntervalIntegrable (fun z => (z * (∫ s in Set.Ioi z, G s)) * G z) volume (1:ℝ) R :=
    hGint.continuousOn_mul hcontA
  have hA : IntervalIntegrable (fun z => (1/4) * (∫ s in Set.Ioi z, G s) ^ 2) volume (1:ℝ) R :=
    (hcontu.pow 2).intervalIntegrable.const_mul (1/4)
  have hB : IntervalIntegrable (fun z => (G z) ^ 2 * z ^ 2) volume (1:ℝ) R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr (hint.mono_set Set.Ioc_subset_Ioi_self)
  have hg : IntervalIntegrable
      (fun z => (1/4) * (∫ s in Set.Ioi z, G s) ^ 2 + (G z) ^ 2 * z ^ 2) volume (1:ℝ) R :=
    hA.add hB
  calc ∫ z in (1:ℝ)..R, (z * (∫ s in Set.Ioi z, G s)) * G z
      ≤ ∫ z in (1:ℝ)..R, ((1/4) * (∫ s in Set.Ioi z, G s) ^ 2 + (G z) ^ 2 * z ^ 2) :=
        intervalIntegral.integral_mono hR.le hf hg hpoint
    _ = (1/4) * (∫ z in (1:ℝ)..R, (∫ s in Set.Ioi z, G s) ^ 2)
        + ∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2 := by
        rw [intervalIntegral.integral_add (f := fun z => (1/4) * (∫ s in Set.Ioi z, G s) ^ 2)
              (g := fun z => (G z) ^ 2 * z ^ 2) hA hB, intervalIntegral.integral_const_mul]

/-- The endpoint decay needed for the sharp Hardy constant:
`R · (∫_{Ioi R} G)² → 0`, from the Cauchy–Schwarz bound `R (∫_{Ioi R} G)² ≤ ∫_{Ioi R} G² s²`. -/
theorem tail_tendsto_zero (G : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (fun s => (G s) ^ 2 * s ^ 2) (Set.Ioi 1))
    (hG : MeasureTheory.IntegrableOn G (Set.Ioi 1)) :
    Filter.Tendsto (fun R : ℝ => R * (∫ s in Set.Ioi R, G s) ^ 2) Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ R : ℝ in atTop,
      R * (∫ s in Set.Ioi R, G s) ^ 2 ≤ ∫ s in Set.Ioi R, (G s) ^ 2 * s ^ 2 := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR1
    have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR1
    have hf2 : IntegrableOn (fun x : ℝ => (G x * x) ^ 2) (Set.Ioi R) := by
      refine (hint.mono_set (Ioi_subset_Ioi hR1)).congr_fun ?_ measurableSet_Ioi
      intro x hx; ring
    have hg2 : IntegrableOn (fun x : ℝ => (x⁻¹) ^ 2) (Set.Ioi R) := by
      refine (integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hR0).congr_fun ?_
        measurableSet_Ioi
      intro x hx
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le hR0 (le_of_lt hx)
      show x ^ (-2:ℝ) = (x⁻¹) ^ 2
      rw [inv_pow, ← Real.rpow_natCast x 2, ← Real.rpow_neg hx0.le]
      simp only [Nat.cast_ofNat]
    have hfg : IntegrableOn (fun x : ℝ => (G x * x) * x⁻¹) (Set.Ioi R) := by
      refine (hG.mono_set (Ioi_subset_Ioi hR1)).congr_fun ?_ measurableSet_Ioi
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hR0 (le_of_lt hx))
      show G x = (G x * x) * x⁻¹
      rw [mul_assoc, mul_inv_cancel₀ hx0, mul_one]
    have hcs := cs_L2 hf2 hg2 hfg
    have h_int_inv : (∫ x : ℝ, (x⁻¹) ^ 2 ∂(volume.restrict (Set.Ioi R))) = R⁻¹ := by
      calc ∫ x : ℝ, (x⁻¹) ^ 2 ∂(volume.restrict (Set.Ioi R))
          = ∫ x in Set.Ioi R, x ^ (-2:ℝ) :=
            setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
              have hx0 : (0:ℝ) < x := lt_of_lt_of_le hR0 (le_of_lt hx)
              show (x⁻¹) ^ 2 = x ^ (-2:ℝ)
              rw [inv_pow, ← Real.rpow_natCast x 2, ← Real.rpow_neg hx0.le]
              simp only [Nat.cast_ofNat])
        _ = R⁻¹ := by
            rw [integral_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hR0]
            norm_num
            rw [Real.rpow_neg_one]
    rw [show (∫ x : ℝ, (G x * x) * x⁻¹ ∂(volume.restrict (Set.Ioi R))) = ∫ x in Set.Ioi R, G x
          from setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
            have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hR0 (le_of_lt hx))
            show (G x * x) * x⁻¹ = G x
            rw [mul_assoc, mul_inv_cancel₀ hx0, mul_one]),
        show (∫ x : ℝ, (G x * x) ^ 2 ∂(volume.restrict (Set.Ioi R)))
            = ∫ x in Set.Ioi R, (G x) ^ 2 * x ^ 2 from
          setIntegral_congr_fun measurableSet_Ioi (fun x hx => by ring),
        h_int_inv] at hcs
    have h2 := mul_le_mul_of_nonneg_left hcs hR0.le
    have heq : R * ((∫ x in Set.Ioi R, (G x) ^ 2 * x ^ 2) * R⁻¹)
        = ∫ x in Set.Ioi R, (G x) ^ 2 * x ^ 2 := by
      rw [← mul_assoc, mul_comm R (∫ x in Set.Ioi R, (G x) ^ 2 * x ^ 2), mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hR0), mul_one]
    linarith [h2, heq]
  have hlim : Tendsto (fun R : ℝ => ∫ s in Set.Ioi R, (G s) ^ 2 * s ^ 2) Filter.atTop (nhds 0) :=
    tendsto_integral_Ioi_zero (b := fun R : ℝ => R) (l := atTop)
      (f := fun s => (G s) ^ 2 * s ^ 2) tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (b := atTop) (a := 0)
    (g := fun _ : ℝ => (0:ℝ)) (h := fun R : ℝ => ∫ s in Set.Ioi R, (G s) ^ 2 * s ^ 2)
    (f := fun R : ℝ => R * (∫ s in Set.Ioi R, G s) ^ 2) tendsto_const_nhds hlim ?_ hbound
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR1
  exact mul_nonneg (by linarith) (sq_nonneg _)

/-- **Hardy inequality for the tail integral, with integrability.**
For `G` integrable on `(1,∞)` with `∫_{1}^{∞} G² s² < ∞`, the function
`z ↦ (∫_{z}^{∞} G)²` is integrable on `(1,∞)` and
`∫_1^∞ (∫_z^∞ G)² ≤ 4 ∫_1^∞ G(z)² z²`. -/
theorem Ioi_tail_sq_integrable (G : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (fun s => (G s) ^ 2 * s ^ 2) (Set.Ioi 1))
    (hG : MeasureTheory.IntegrableOn G (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z => (∫ s in Set.Ioi z, G s) ^ 2) (Set.Ioi 1) ∧
    ∫ z in Set.Ioi 1, (∫ s in Set.Ioi z, G s) ^ 2
      ≤ 4 * ∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2 := by
  set F : ℝ → ℝ := fun z => ∫ s in Set.Ioi z, G s with hFdef
  have hcont : ContinuousOn F (Set.Ici 1) := by
    rw [hFdef]; exact Pieces.tail_continuous G hG
  have hDnn : 0 ≤ ∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2 :=
    integral_nonneg (fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- Uniform bound for the truncated integrals, using IBP + AM–GM + the endpoint decay.
  have hbound_all : ∀ R : ℝ, 1 < R → R * F R ^ 2 ≤ 1 →
      (∫ z in (1:ℝ)..R, F z ^ 2) ≤ 2 + 4 * (∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2) := by
    intro R hR hsmall
    have h1 := tail_ibp G hG R hR
    have h3 := tail_amgm G hint hG R hR
    simp only [hFdef] at h1 h3 hsmall ⊢
    have hDle : (∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2)
        ≤ ∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2 := by
      rw [intervalIntegral.integral_of_le hR.le]
      refine setIntegral_mono_set hint ?_ ?_
      · exact Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      · exact Eventually.of_forall (fun x hx => hx.1)
    have hW : 0 ≤ (∫ s in Set.Ioi 1, G s) ^ 2 := sq_nonneg _
    nlinarith [h1, h3, hDle, hW, hsmall]
  -- Integrability of `F²` on `(1,∞)` via boundedness of the truncated integrals.
  have hintF : IntegrableOn (fun z => F z ^ 2) (Set.Ioi 1) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (2 + 4 * (∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2)) 1
      (b := fun i : ℕ => (i:ℝ) + 2) (l := atTop) ?_ ?_ ?_
    · intro i
      have hi : (1:ℝ) ≤ (i:ℝ) + 2 := by
        have h0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i; linarith
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hi).mp ?_
      exact ((hcont.mono (by rw [Set.uIcc_of_le hi]; exact fun x hx => hx.1)).pow 2).intervalIntegrable
    · exact tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ))
    · have hb : Tendsto (fun i : ℕ => (i:ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ))
      filter_upwards [hb.eventually ((tail_tendsto_zero G hint hG).eventually
        (isOpen_Iio.mem_nhds (by norm_num : (0:ℝ) < 1)))] with i hsmall
      have hR : (1:ℝ) < (i:ℝ) + 2 := by
        have h0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i; linarith
      have hsmall' : ((i:ℝ) + 2) * F ((i:ℝ) + 2) ^ 2 ≤ 1 := by
        simpa only [hFdef] using le_of_lt hsmall
      rw [show (∫ x in (1:ℝ)..((i:ℝ) + 2), ‖F x ^ 2‖) = ∫ x in (1:ℝ)..((i:ℝ) + 2), F x ^ 2
            from intervalIntegral.integral_congr
              (fun x _ => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])]
      exact hbound_all ((i:ℝ) + 2) hR hsmall'
  refine ⟨hintF, ?_⟩
  change ∫ z in Set.Ioi 1, F z ^ 2 ≤ 4 * ∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2
  -- The sharp constant, via IBP + AM–GM + the endpoint decay in the limit `R → ∞`.
  have hmain : ∀ᶠ R : ℝ in atTop,
      (1/2) * (∫ z in (1:ℝ)..R, F z ^ 2)
        ≤ R * F R ^ 2 - F 1 ^ 2 + 2 * (∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2) := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with R hR
    have h1 := tail_ibp G hG R hR
    have h3 := tail_amgm G hint hG R hR
    simp only [hFdef] at h1 h3 ⊢
    linarith
  have hu : Tendsto (fun R : ℝ => (1/2) * (∫ z in (1:ℝ)..R, F z ^ 2)) atTop
      (nhds ((1/2) * ∫ z in Set.Ioi 1, F z ^ 2)) :=
    (intervalIntegral_tendsto_integral_Ioi (1:ℝ) hintF (b := fun R : ℝ => R) (l := atTop)
      tendsto_id).const_mul (1/2)
  have hv : Tendsto
      (fun R : ℝ => R * F R ^ 2 - F 1 ^ 2 + 2 * (∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2)) atTop
      (nhds (0 - F 1 ^ 2 + 2 * (∫ z in Set.Ioi 1, (G z) ^ 2 * z ^ 2))) := by
    have hP2 : Tendsto (fun R : ℝ => R * F R ^ 2) atTop (nhds 0) := by
      simpa only [hFdef] using tail_tendsto_zero G hint hG
    have hI : Tendsto (fun R : ℝ => ∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2) atTop
        (nhds (∫ z in Set.Ioi 1, (G z) ^ 2 * z ^ 2)) :=
      intervalIntegral_tendsto_integral_Ioi (1:ℝ) hint (b := fun R : ℝ => R) (l := atTop) tendsto_id
    exact (hP2.sub tendsto_const_nhds).add (hI.const_mul 2)
  have hle := le_of_tendsto_of_tendsto hu hv hmain
  have hsq : 0 ≤ F 1 ^ 2 := sq_nonneg _
  linarith

end Work.FTS.CoercivityFix.Coer1T.Hardy
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces.pzSqSeta_le_Dz1_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces

open Work.Spaces

/-- The elementary box bound `1 ≤ (b²/(1+a)⁴)·z²·w(z)²` for `z ∈ [a,b]`, `0 < a < b`.
Equivalently `(1+a)² ≤ b·z·w(z) = b(1+z)²/z`, which is immediate from
`(b/z)·(1+a)² ≥ (1+a)²` and `(b/z)·(1+z)² = b(1+z)²/z`. -/
theorem one_le_bSq_div_mul_wSq {a b z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hzb : z ≤ b) :
    1 ≤ b ^ 2 / (1 + a) ^ 4 * (z ^ 2 * w z ^ 2) := by
  have hzpos : 0 < z := lt_of_lt_of_le ha haz
  -- `(1+a)² ≤ b·z·w z`
  have hstep : (1 + a) ^ 2 ≤ b * z * w z := by
    rw [w]
    have h1 : 1 ≤ b / z := (one_le_div hzpos).2 hzb
    have h2 : (1 + a) ^ 2 ≤ (1 + z) ^ 2 := by nlinarith
    have h3 : (1 + z) ^ 2 ≤ (b / z) * (1 + z) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right h1 (sq_nonneg (1 + z))
      simpa using hh
    have h4 : b * z * ((1 + z) ^ 2 / z ^ 2) = (b / z) * (1 + z) ^ 2 := by
      field_simp
    linarith
  -- squaring a nonnegative inequality
  have hsq : ((1 + a) ^ 2) ^ 2 ≤ (b * z * w z) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) hstep 2
  have h1a4 : (0 : ℝ) < (1 + a) ^ 4 := by positivity
  rw [div_mul_eq_mul_div, one_le_div h1a4]
  nlinarith [hsq]

/-- The `θ`-weight identity `(w/s^{η/2})² = w²·s^{-η}` for `s ≥ 0`.  Both sides vanish at
`s = 0`, so no strict positivity is required. -/
theorem div_rpow_sq_eq (c s : ℝ) (hs : 0 ≤ s) :
    (c / s ^ (eta / 2)) ^ 2 = c ^ 2 * s ^ (-(eta)) := by
  have hsq : (s ^ (eta / 2)) ^ 2 = s ^ eta := by
    rw [← Real.rpow_natCast (s ^ (eta / 2)) 2,
        ← Real.rpow_mul hs (eta / 2) ((2 : ℕ) : ℝ)]
    rw [show eta / 2 * ((2 : ℕ) : ℝ) = eta by norm_num]
  rw [div_pow, hsq, div_eq_mul_inv, Real.rpow_neg hs]

theorem pzSqSeta_le_Dz1_mul {f : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.pz f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (b ^ 2 / (1 + a) ^ 4) *
          (Work.Spaces.DzIter 1 f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  intro z hz θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · have := Real.pi_pos; linarith [hθ.2]
  -- `D_z f = z·∂_z f`
  have hDz : DzIter 1 f z θ = z * pz f z θ := by
    simp [DzIter, Dz]
  -- the box factor is `≥ 1` (uses `hab` through `0 < b`)
  have hfac : 1 ≤ b ^ 2 / (1 + a) ^ 4 * (z ^ 2 * w z ^ 2) :=
    one_le_bSq_div_mul_wSq ha hz.1 hz.2
  have _hb : 0 < b := lt_trans ha hab
  -- the `θ`-weight identity
  have hY : (w z / Real.sin (2 * θ) ^ (eta / 2)) ^ 2 = w z ^ 2 * Real.sin (2 * θ) ^ (-(eta)) :=
    div_rpow_sq_eq (w z) (Real.sin (2 * θ)) hsin
  have hpz : 0 ≤ (pz f z θ) ^ 2 := sq_nonneg _
  have hS : 0 ≤ Real.sin (2 * θ) ^ (-(eta)) := Real.rpow_nonneg hsin _
  -- the right-hand side, expanded
  have hRw : (z * pz f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
      = z ^ 2 * (pz f z θ) ^ 2 * w z ^ 2 * Real.sin (2 * θ) ^ (-(eta)) := by
    rw [mul_pow, mul_pow, hY]
    ring
  calc (pz f z θ) ^ 2 * Real.sin (2 * θ) ^ (-(eta))
      = ((pz f z θ) ^ 2 * Real.sin (2 * θ) ^ (-(eta))) * 1 := by rw [mul_one]
    _ ≤ ((pz f z θ) ^ 2 * Real.sin (2 * θ) ^ (-(eta))) *
          (b ^ 2 / (1 + a) ^ 4 * (z ^ 2 * w z ^ 2)) :=
        mul_le_mul_of_nonneg_left hfac (mul_nonneg hpz hS)
    _ = (b ^ 2 / (1 + a) ^ 4) *
          (DzIter 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 := by
        rw [hDz, hRw]; ring

end Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.theta_A2_int_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2norm

set_option autoImplicit false

/-- On the angular interval, `sin(2θ) ≥ 0`. -/
private lemma sin_two_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩






end Work.FTS.CoercivityFix.Transfer.E2norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

/-- The radial profile `φ(z) = z/(1+z)²` of the nonlocal `z`-factor `ampA`. -/
def fA (z : ℝ) : ℝ := z / (1 + z) ^ 2

/-- The radial profile `z²/(1+z)³` of the projector correction's `z`-factor `ampB`. -/
def fB (z : ℝ) : ℝ := z ^ 2 / (1 + z) ^ 3

/-- The explicit `(z ∂_z)`-iterates of `φ(z) = z/(1+z)²`, i.e. `rA j` is
`z·Q_j(z)/(1+z)^{j+2}` for `j ≤ 4` (and the `j = 4` value is repeated beyond `4`). -/
def rA : ℕ → ℝ → ℝ
  | 0 => fun z => z / (1 + z) ^ 2
  | 1 => fun z => z * (1 - z) / (1 + z) ^ 3
  | 2 => fun z => z * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4
  | 3 => fun z => z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5
  | _ => fun z => z * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4) / (1 + z) ^ 6

/-- The explicit `(z ∂_z)`-iterates of `z²/(1+z)³`, i.e. `rB j` is
`z²·N_j(z)/(1+z)^{j+3}` for `j ≤ 4` (and the `j = 4` value is repeated beyond `4`). -/
def rB : ℕ → ℝ → ℝ
  | 0 => fun z => z ^ 2 / (1 + z) ^ 3
  | 1 => fun z => z ^ 2 * (2 - z) / (1 + z) ^ 4
  | 2 => fun z => z ^ 2 * (4 - 7 * z + z ^ 2) / (1 + z) ^ 5
  | 3 => fun z => z ^ 2 * (8 - 33 * z + 18 * z ^ 2 - z ^ 3) / (1 + z) ^ 6
  | _ => fun z => z ^ 2 * (16 - 131 * z + 171 * z ^ 2 - 41 * z ^ 3 + z ^ 4) / (1 + z) ^ 7

@[simp] theorem fA_apply (z : ℝ) : fA z = z / (1 + z) ^ 2 := rfl

@[simp] theorem fB_apply (z : ℝ) : fB z = z ^ 2 / (1 + z) ^ 3 := rfl

@[simp] theorem rA_zero : rA 0 = fun z : ℝ => z / (1 + z) ^ 2 := rfl
@[simp] theorem rA_one : rA 1 = fun z : ℝ => z * (1 - z) / (1 + z) ^ 3 := rfl
@[simp] theorem rA_two : rA 2 = fun z : ℝ => z * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := rfl
@[simp] theorem rA_three :
    rA 3 = fun z : ℝ => z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5 := rfl
@[simp] theorem rA_four :
    rA 4 = fun z : ℝ => z * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4) / (1 + z) ^ 6 := rfl

@[simp] theorem rB_zero : rB 0 = fun z : ℝ => z ^ 2 / (1 + z) ^ 3 := rfl
@[simp] theorem rB_one : rB 1 = fun z : ℝ => z ^ 2 * (2 - z) / (1 + z) ^ 4 := rfl
@[simp] theorem rB_two : rB 2 = fun z : ℝ => z ^ 2 * (4 - 7 * z + z ^ 2) / (1 + z) ^ 5 := rfl
@[simp] theorem rB_three :
    rB 3 = fun z : ℝ => z ^ 2 * (8 - 33 * z + 18 * z ^ 2 - z ^ 3) / (1 + z) ^ 6 := rfl
@[simp] theorem rB_four :
    rB 4 = fun z : ℝ => z ^ 2 * (16 - 131 * z + 171 * z ^ 2 - 41 * z ^ 3 + z ^ 4) / (1 + z) ^ 7 :=
  rfl

end Work.FTS.CoercivityFix.Transfer.E2pkg
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.Pieces.primitive_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty.Pieces

/-- If `f` is integrable on `Ioc 0 z` with `z > 0` and continuous on `(0,∞)`, then it is
integrable on `Ioo 0 1`.  (This is the contradiction step of the `¬ P` branch: the compact
piece `Icc z 1` is harmless.) -/
theorem integrableOn_Ioo_zero_one_of_Ioc {f : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn f (Set.Ioi 0)) (hIoc : MeasureTheory.IntegrableOn f (Set.Ioc 0 z)) :
    MeasureTheory.IntegrableOn f (Set.Ioo 0 1) := by
  rcases lt_or_ge z 1 with hz1 | hz1
  · -- `z < 1`: `Ioo 0 1 ⊆ Ioc 0 z ∪ Ioo z 1`, and `f` is continuous on the compact `Icc z 1`.
    have hB : MeasureTheory.IntegrableOn f (Set.Ioo z 1) :=
      ((hcont.mono (fun x hx => lt_of_lt_of_le hz hx.1)).integrableOn_Icc).mono_set
        Set.Ioo_subset_Icc_self
    refine (hIoc.union hB).mono_set ?_
    intro x hx
    rcases le_or_gt x z with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2⟩
  · -- `1 ≤ z`: `Ioo 0 1 ⊆ Ioc 0 z`.
    exact hIoc.mono_set (fun x hx => ⟨hx.1, le_trans (le_of_lt hx.2) hz1⟩)

/-- **Primitive of a `C^n` function on `(0,∞)` is `C^n` there** (Lean's junk-value convention for the interval integral included).  This is the `0..z` half of the case-split needed by `Work.FTS.EllExist.Honesty.radGreen_contDiffOn`.

ROUTE.  Put `F z = ∫ t in (0:ℝ)..z, f t` and `P := MeasureTheory.IntegrableOn f (Set.Ioo 0 1)`.

* **Case `P`.**  For every `z > 0`, `IntervalIntegrable f volume 0 z`: `f` is continuous on `(0,∞)` and `Ioc 0 z ⊆ Ioo 0 1 ∪ Icc (min z 1) z`, the second piece compact (this is exactly
  `Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo`, import it).  Then
  `intervalIntegral.integral_hasDerivAt_right` gives `HasDerivAt F (f z) z` for every `z ∈ Ioi 0`,
  so `deriv F = f` pointwise there.  With `ContDiffOn.congr` this gives
  `ContDiffOn ℝ n (deriv F) (Ioi 0)`, and `contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi` plus
  `DifferentiableOn` gives `ContDiffOn ℝ (n+1) F (Ioi 0)` (the conjunct
  `↑n = ⊤ → AnalyticOn …` is vacuous since `↑n ≠ ⊤ : ℕ∞ω`); downgrade with `ContDiffOn.of_le`
  (`Nat.le_succ n`).

* **Case `¬ P`.**  Show `¬ MeasureTheory.IntegrableOn f (Set.Ioc 0 z)` for every `z > 0`: if
  `Ioc 0 z` were integrable then so would be `Ioo 0 (min z 1)` (subset) and `Ioo (min z 1) 1`
  (subset of the compact `Icc (min z 1) 1`, on which `f` is continuous since `min z 1 > 0`), and
  `Ioo 0 1 = Ioo 0 (min z 1) ∪ Ioo (min z 1) 1`, so
  `IntegrableOn.union` would give `P`.  Hence `F z = ∫ t in Ioc 0 z, f t = 0` by
  `intervalIntegral.integral_of_le` and `MeasureTheory.integral_undef`, i.e. `F = 0` on `Ioi 0`,
  and `contDiffOn_congr` with the constant `0` finishes.

Do NOT attempt to derive `P` from `hf`: it is false (`f t = t ^ (-30)`). -/
theorem primitive_contDiffOn (n : ℕ) {f : ℝ → ℝ} (hf : ContDiffOn ℝ n f (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun z => ∫ t in (0 : ℝ)..z, f t) (Set.Ioi 0) := by
  by_cases hP : MeasureTheory.IntegrableOn f (Set.Ioo 0 1)
  · -- Case `P`: `F` is a genuine primitive of the continuous `f` on `(0,∞)`.
    have hcont : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
    have hii : ∀ z ∈ Set.Ioi 0, IntervalIntegrable f MeasureTheory.volume 0 z :=
      fun z hz => Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo hz hcont hP
    have hderiv : ∀ z ∈ Set.Ioi 0, HasDerivAt (fun z => ∫ t in (0 : ℝ)..z, f t) (f z) z := by
      intro z hz
      refine intervalIntegral.integral_hasDerivAt_right (hii z hz) ?_
        (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
      exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hcont z hz
    have hderiv_eq : ∀ z ∈ Set.Ioi 0, deriv (fun z => ∫ t in (0 : ℝ)..z, f t) z = f z :=
      fun z hz => (hderiv z hz).deriv
    have hcd : ContDiffOn ℝ n (deriv (fun z => ∫ t in (0 : ℝ)..z, f t)) (Set.Ioi 0) :=
      hf.congr hderiv_eq
    have hdiff : DifferentiableOn ℝ (fun z => ∫ t in (0 : ℝ)..z, f t) (Set.Ioi 0) :=
      fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
    have htop : ¬ ((n : WithTop ℕ∞) = ⊤) := ne_of_lt (WithTop.coe_lt_top (n : ℕ∞))
    have hsucc : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (fun z => ∫ t in (0 : ℝ)..z, f t)
        (Set.Ioi 0) :=
      (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
        (f := fun z => ∫ t in (0 : ℝ)..z, f t) (s := Set.Ioi 0) (n := (n : WithTop ℕ∞))
        isOpen_Ioi).mpr ⟨hdiff, fun h => absurd h htop, hcd⟩
    exact ContDiffOn.of_le hsucc (le_add_of_nonneg_right zero_le_one)
  · -- Case `¬ P`: the interval integral is the junk constant `0` on `(0,∞)`.
    have hnoIoc : ∀ z ∈ Set.Ioi 0, ¬ MeasureTheory.IntegrableOn f (Set.Ioc 0 z) :=
      fun z hz hIoc => hP (integrableOn_Ioo_zero_one_of_Ioc hz hf.continuousOn hIoc)
    have hF0 : ∀ z ∈ Set.Ioi 0, (∫ t in (0 : ℝ)..z, f t) = 0 := by
      intro z hz
      have hni : ¬ MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.Ioc 0 z)) := by
        simpa only [MeasureTheory.IntegrableOn] using hnoIoc z hz
      rw [intervalIntegral.integral_of_le hz.le, MeasureTheory.integral_undef hni]
    exact (contDiffOn_const (c := (0 : ℝ))).congr hF0

end Work.FTS.EllExist.Honesty.Pieces
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.Pieces.tailIntegral_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty.Pieces

open scoped ContDiff

/-- The tail integral `u ↦ ∫ t in (u,∞), f t` of a function continuous and integrable on a
right neighbourhood of `z > 0` is differentiable at `z` with derivative `-f z`. -/
theorem tailIntegral_hasDerivAt {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi 1)) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun u => ∫ t in Set.Ioi u, f t) (-(f z)) z := by
  have hhalf : (0 : ℝ) < z / 2 := by linarith
  have hsub : Set.Ioi (z / 2) ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi] at hx ⊢
    linarith
  exact Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi (by linarith) (hcont.mono hsub)
    (Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo hhalf hcont hint)

/-- The derivative of the tail integral is `-f` on `(0,∞)`. -/
theorem tailIntegral_deriv_eq {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi 1)) {z : ℝ} (hz : 0 < z) :
    deriv (fun u => ∫ t in Set.Ioi u, f t) z = -(f z) :=
  (tailIntegral_hasDerivAt hcont hint hz).deriv

/-- **One step of the induction**: if `f` is `C^m` on `(0,∞)` (with `m` a finite order) and
integrable on `(1,∞)`, then its tail integral is `C^{m+1}` on `(0,∞)`. -/
theorem tailIntegral_contDiffOn_succ {m : ℕ∞ω} (hm : m ≠ ⊤) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ioi 0)) (hint : MeasureTheory.IntegrableOn f (Set.Ioi 1))
    (hd : ContDiffOn ℝ m (fun z => -(f z)) (Set.Ioi 0)) :
    ContDiffOn ℝ (m + 1) (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) := by
  refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
    (f := fun u => ∫ t in Set.Ioi u, f t) (s := Set.Ioi 0) (n := m) isOpen_Ioi).mpr
    ⟨?_, ?_, ?_⟩
  · exact fun z hz =>
      (tailIntegral_hasDerivAt hcont hint hz).differentiableAt.differentiableWithinAt
  · intro h
    exact absurd h hm
  · exact hd.congr fun z hz => tailIntegral_deriv_eq hcont hint hz

/-- **The tail integral of a `C^n` integrable function is `C^n`.**  This is the `Ioi z` half of the case-split needed by `Work.FTS.EllExist.Honesty.radGreen_contDiffOn`.

ROUTE (`hint` makes this unconditional: no junk case can arise).  Fix `z > 0`.  `f` is continuous
on `Ioi (z/2)` (`hf.continuousOn.mono`) and integrable there —
`Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo (z/2) hcont hint` (import it; it splits
`Ioi (z/2)` into `Ioc (z/2) 1` and `Ioi 1`; alternatively reprove: for `z/2 ≤ 1` the piece
`Icc (z/2) 1` is compact and `f` is continuous on it, for `1 ≤ z/2` use `Ioi (z/2) ⊆ Ioi 1`).  So
`Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi (a := z/2) (z := z) (by linarith)` gives
`HasDerivAt (fun w => ∫ t in Set.Ioi w, f t) (-(f z)) z`.  Hence
`deriv (fun w => ∫ t in Set.Ioi w, f t)` agrees on `Ioi 0` with `fun w => -(f w)`, which is `C^n`
(`hf.neg.congr`), so `contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi` gives `C^{n+1}` (the
conjunct `↑n = ⊤ → AnalyticOn …` is vacuous), and `ContDiffOn.of_le` downgrades to `C^n`. -/
theorem tailIntegral_contDiffOn (n : ℕ) {f : ℝ → ℝ} (hf : ContDiffOn ℝ n f (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi 1)) :
    ContDiffOn ℝ n (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) := by
  have hcont : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
  rcases n with _ | m
  · -- `n = 0`: descend from the `C^1` statement given by the induction step at `m = 0`
    have h : ContDiffOn ℝ ((0 : ℕ∞ω) + 1) (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) :=
      tailIntegral_contDiffOn_succ (m := (0 : ℕ∞ω)) (by simp) hcont hint (by simpa using hf.neg)
    exact h.of_le (by simp)
  · have hd : ContDiffOn ℝ ((m : ℕ) : ℕ∞ω) (fun z => -(f z)) (Set.Ioi 0) :=
      hf.neg.of_le (by exact_mod_cast Nat.le_succ m)
    have h : ContDiffOn ℝ (((m : ℕ) : ℕ∞ω) + 1) (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) :=
      tailIntegral_contDiffOn_succ (m := ((m : ℕ) : ℕ∞ω)) (by simp) hcont hint hd
    simpa only [Nat.cast_succ] using h

end Work.FTS.EllExist.Honesty.Pieces
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.RadGreenDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllExist.Honesty

/-- The first (`z^{s⁻}`, `s⁻ = -(2m+5)/α`) Green term of `radGreen`: the integral of `c` from `0`
to `z`.  It is the term that is singular at `z = 0`. -/
def G1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  z ^ (-(2 * (m : ℝ) + 5) / α) * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))

/-- The second (`z^{s⁺}`, `s⁺ = 2m/α`) Green term of `radGreen`: the tail integral of `c`
from `z` to `∞`.  It vanishes at `z = 0` like `z^{s⁺}` provided the tail integral is finite. -/
def G2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  z ^ (2 * (m : ℝ) / α) * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))

/-- The explicit definition of `radGreen`, split into its two Green terms. -/
theorem radGreen_eq_G1_add_G2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = 1 / (α * (4 * (m : ℝ) + 5)) * (G1 α m c z + G2 α m c z) := rfl

/-- `s⁺ = 2m/α ≥ 8` on the standing range `0 < α ≤ 1/4`, `1 ≤ m`. -/
theorem eight_le_two_m_div (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m) :
    8 ≤ 2 * (m : ℝ) / α := by
  have h4 : 4 ≤ 1 / α := by
    rw [le_div_iff₀ hα]
    linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have : 2 * (m : ℝ) / α = 2 * (m : ℝ) * (1 / α) := by ring
  rw [this]
  nlinarith


end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.RadGreenDzuDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllExist.Honesty

set_option autoImplicit false

/-- The univariate operator `Dzu i = (z ∂_z)^i` on functions of the radial variable `z`. -/
def Dzu : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, g => g
  | n + 1, g => fun z => z * deriv (Dzu n g) z

@[simp] theorem Dzu_zero (g : ℝ → ℝ) : Dzu 0 g = g := rfl

@[simp] theorem Dzu_succ (n : ℕ) (g : ℝ → ℝ) :
    Dzu (n + 1) g = fun z => z * deriv (Dzu n g) z := rfl


/-- `Dzu` is the restriction of the curried operator `DzIter` to `z`-only functions. -/
theorem DzIter_zOnly (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z' _ => g z') z θ = Dzu i g z := by
  induction i generalizing z with
  | zero => rfl
  | succ n ih =>
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, Dzu_succ]
      have hfun : (fun z' => Work.Spaces.DzIter n (fun z' _ => g z') z' θ) = Dzu n g :=
        funext fun z' => ih z'
      rw [hfun]



end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.psi_inner_wt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set


end Work.FTS.EllExist.Honesty
end
-- ===== merged: Submission.Work.FTS.EllExist.RadGreenDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

set_option autoImplicit false

/-- The normalising constant `1/(α(4m+5))` of `radGreen`. -/
def rgK (α : ℝ) (m : ℕ) : ℝ := 1 / (α * (4 * (m : ℝ) + 5))

/-- The positively oriented decaying indicial exponent `q = (2m+5)/α` (so `s⁻ = -q`). -/
def rgQ (α : ℝ) (m : ℕ) : ℝ := (2 * (m : ℝ) + 5) / α

/-- The growing indicial exponent `p = 2m/α`. -/
def rgP (α : ℝ) (m : ℕ) : ℝ := 2 * (m : ℝ) / α

/-- The integrand `c t · t^{q-1}` of the forward primitive. -/
def rgF1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun t => c t * t ^ (rgQ α m - 1)

/-- The integrand `c t · t^{-p-1}` of the tail primitive. -/
def rgF2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun t => c t * t ^ (-(rgP α m) - 1)

/-- The forward primitive `z ↦ ∫_0^z c t^{q-1} dt`. -/
def rgA (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, rgF1 α m c t

/-- The tail primitive `z ↦ ∫_{Ioi z} c t^{-p-1} dt`. -/
def rgB (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ t in Set.Ioi z, rgF2 α m c t

/-- The decaying branch `g₁ = z^{-q} rgA`. -/
def rgG1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z => z ^ (-(rgQ α m)) * rgA α m c z

/-- The growing branch `g₂ = z^{p} rgB`. -/
def rgG2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z => z ^ (rgP α m) * rgB α m c z

/-- The explicit first derivative of `radGreen α m c` on `(0,∞)`. -/
def rgD1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z =>
  rgK α m * (-(rgQ α m) * z ^ (-(rgQ α m) - 1) * rgA α m c z
    + rgP α m * z ^ (rgP α m - 1) * rgB α m c z)

/-- The explicit second derivative of `radGreen α m c` on `(0,∞)`. -/
def rgD2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z =>
  rgK α m * (rgQ α m * (rgQ α m + 1) * z ^ (-(rgQ α m) - 2) * rgA α m c z
    + rgP α m * (rgP α m - 1) * z ^ (rgP α m - 2) * rgB α m c z
    - rgQ α m * z ^ (-(rgQ α m) - 1) * rgF1 α m c z
    - rgP α m * z ^ (rgP α m - 1) * rgF2 α m c z)

/-- `radGreen` is definitionally the expression in terms of the named pieces. -/
theorem radGreen_eq (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = rgK α m * (z ^ (-(rgQ α m)) * rgA α m c z + z ^ (rgP α m) * rgB α m c z) := by
  simp only [Work.FTS.PhiStar.Radial.radGreen, rgK, rgQ, rgP, rgA, rgB, rgF1, rgF2, neg_div]


theorem rgK_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < rgK α m := by
  rw [rgK]
  positivity

theorem rgQ_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < rgQ α m := by
  rw [rgQ]
  have h : (0 : ℝ) < 2 * (m : ℝ) + 5 := by positivity
  exact div_pos h hα

theorem rgP_nonneg {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 ≤ rgP α m := by
  rw [rgP]
  positivity

theorem rgP_pos {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) : 0 < rgP α m := by
  rw [rgP]
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  positivity

/-- `q ≥ 28` for `m ≥ 1` and `α ≤ 1/4`. -/
theorem rgQ_ge {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {m : ℕ} (hm : 1 ≤ m) :
    28 ≤ rgQ α m := by
  rw [rgQ, le_div_iff₀ hα]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

/-- `p ≥ 8` for `m ≥ 1` and `α ≤ 1/4`. -/
theorem rgP_ge {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {m : ℕ} (hm : 1 ≤ m) :
    8 ≤ rgP α m := by
  rw [rgP, le_div_iff₀ hα]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith




end Work.FTS.EllExist
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.prod_integrable_of_slice_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory

/-- If `k` vanishes outside `[-1,1]`, then multiplying by `|k (σ - t)|` can only see `Φ` on the
interval `[σ-1, σ+1]`. -/
private lemma abs_k_mul_eq_indicator {k : ℝ → ℝ} {Φ : ℝ → ℝ} {σ : ℝ}
    (hk0 : ∀ x : ℝ, 1 < |x| → k x = 0) (t : ℝ) :
    |k (σ - t)| * Φ t
      = |k (σ - t)| * Set.indicator (Set.Icc (σ - 1) (σ + 1)) Φ t := by
  by_cases ht : t ∈ Set.Icc (σ - 1) (σ + 1)
  · rw [Set.indicator_of_mem ht]
  · have h1 : 1 < |σ - t| := by
      rw [Set.mem_Icc] at ht
      rcases not_and_or.mp ht with h | h
      · have hlt : t < σ - 1 := not_le.mp h
        rw [abs_of_pos (by linarith : (0 : ℝ) < σ - t)]; linarith
      · have hlt : σ + 1 < t := not_le.mp h
        rw [abs_of_neg (by linarith : σ - t < 0)]; linarith
    rw [Set.indicator_of_notMem ht, mul_zero, hk0 _ h1, abs_zero, zero_mul]

theorem prod_integrable_of_slice_bound {k : ℝ → ℝ} {w : ℝ → ℝ → ℝ} {Φ : ℝ → ℝ} {M σ : ℝ}
    (hkm : Measurable k) (hkM : ∀ x : ℝ, |k x| ≤ M) (hk0 : ∀ x : ℝ, 1 < |x| → k x = 0)
    (hw_meas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => w p.1 p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hw_int : ∀ t : ℝ, MeasureTheory.IntegrableOn (fun s : ℝ => w t s) Work.Spaces.Iθ)
    (hw_bd : ∀ t : ℝ, ∫ s in Work.Spaces.Iθ, |w t s| ≤ Φ t)
    (hΦ_int : MeasureTheory.IntegrableOn Φ (Set.Icc (σ - 1) (σ + 1))) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => k (σ - p.1) * w p.1 p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  classical
  -- `M` is nonnegative and `Φ` is nonnegative (it dominates a nonnegative integral)
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (k 0)) (hkM 0)
  have hΦnn : ∀ t : ℝ, 0 ≤ Φ t := fun t =>
    le_trans (integral_nonneg (f := fun s : ℝ => |w t s|) (fun s => abs_nonneg _)) (hw_bd t)
  -- the dominating `z`-marginal: `M · Φ` cut down to the support interval
  have hDind : Integrable (Set.indicator (Set.Icc (σ - 1) (σ + 1)) Φ) volume :=
    hΦ_int.integrable_indicator measurableSet_Icc
  have hDint : Integrable
      (fun t : ℝ => M * Set.indicator (Set.Icc (σ - 1) (σ + 1)) Φ t) volume :=
    hDind.const_mul M
  -- pointwise bound of the norm of each slice
  have hpt : ∀ t : ℝ, ‖∫ s, ‖k (σ - t) * w t s‖ ∂(volume.restrict Work.Spaces.Iθ)‖
      ≤ M * Set.indicator (Set.Icc (σ - 1) (σ + 1)) Φ t := by
    intro t
    have hnn : 0 ≤ ∫ s, ‖k (σ - t) * w t s‖ ∂(volume.restrict Work.Spaces.Iθ) :=
      integral_nonneg (fun s => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    calc ∫ s, ‖k (σ - t) * w t s‖ ∂(volume.restrict Work.Spaces.Iθ)
        = ∫ s in Work.Spaces.Iθ, |k (σ - t)| * |w t s| := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
          simp only [Real.norm_eq_abs, abs_mul]
      _ = |k (σ - t)| * ∫ s in Work.Spaces.Iθ, |w t s| := integral_const_mul _ _
      _ ≤ |k (σ - t)| * Φ t := mul_le_mul_of_nonneg_left (hw_bd t) (abs_nonneg _)
      _ ≤ M * Set.indicator (Set.Icc (σ - 1) (σ + 1)) Φ t := by
          rw [abs_k_mul_eq_indicator hk0 t]
          exact mul_le_mul_of_nonneg_right (hkM _)
            (Set.indicator_nonneg (fun a _ => hΦnn a) t)
  -- joint measurability of the integrand
  have hkm2 : Measurable (fun p : ℝ × ℝ => k (σ - p.1)) :=
    hkm.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => σ - p.1))
  have hsm : AEStronglyMeasurable (fun p : ℝ × ℝ => k (σ - p.1) * w p.1 p.2)
      (volume.prod (volume.restrict Work.Spaces.Iθ)) :=
    hkm2.aestronglyMeasurable.mul hw_meas
  -- measurability of the `z`-marginal
  have hnm : AEStronglyMeasurable
      (fun t : ℝ => ∫ s, ‖k (σ - t) * w t s‖ ∂(volume.restrict Work.Spaces.Iθ)) volume :=
    hsm.norm.integral_prod_right'
  -- integrability of the `z`-marginal
  have hmarg : Integrable
      (fun t : ℝ => ∫ s, ‖k (σ - t) * w t s‖ ∂(volume.restrict Work.Spaces.Iθ)) volume :=
    Integrable.mono' hDint hnm (Filter.Eventually.of_forall hpt)
  -- Fubini
  exact (integrable_prod_iff hsm).mpr
    ⟨Filter.Eventually.of_forall (fun t => (hw_int t).const_mul (k (σ - t))), hmarg⟩

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_taylor_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

open MeasureTheory Set Filter
open scoped Topology

/-- Taylor's formula of order two with the remainder in integral form, on the open interval
`(0, π/2)`: for `f : ℝ → ℝ` of class `C²` on `Ioo 0 (π/2)` and points `a, x ∈ Ioo 0 (π/2)`
(no ordering assumed — the interval integral is the signed one),
`f x = f a + (x - a) f'(a) + ∫_a^x (x - t) f''(t) dt`.

Both the fundamental theorem of calculus and the integration by parts used below are stated in
Mathlib for arbitrary (unordered) endpoints via `Set.uIcc`, so the two orderings need not be
separated. -/
theorem slice_taylor_two {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {a x : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    f x = f a + (x - a) * deriv f a + ∫ t in a..x, (x - t) * deriv (deriv f) t := by
  -- the closed interval between `a` and `x` lies in the open interval where `f` is `C²`
  have hsub : Set.uIcc a x ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro t ht
    rcases le_total a x with h | h
    · rw [uIcc_of_le h] at ht
      exact ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hx.2⟩
    · rw [uIcc_of_ge h] at ht
      exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 ha.2⟩
  have hcont1 : ContinuousOn (deriv f) (Set.uIcc a x) := (c2_continuousOn_deriv hf).mono hsub
  have hcont2 : ContinuousOn (deriv (deriv f)) (Set.uIcc a x) :=
    (c2_continuousOn_deriv_deriv hf).mono hsub
  have hderiv1 : ∀ t ∈ Set.uIcc a x, HasDerivAt (deriv f) (deriv (deriv f) t) t :=
    fun t ht => c2_hasDerivAt_deriv hf (hsub ht)
  -- fundamental theorem of calculus: `∫_a^x f' = f x - f a`
  have hFTC : ∫ t in a..x, deriv f t = f x - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := f) (f' := fun t : ℝ => deriv f t) (a := a) (b := x)
      (fun t ht => c2_hasDerivAt_self hf (hsub ht)) hcont1.intervalIntegrable
  -- integration by parts with `u t = x - t` (so `u' = -1`) and `v = deriv f` (so `v' = f''`):
  -- `∫_a^x (x - t) f'' = -(x - a) f'(a) + ∫_a^x f'`
  have hIBP : ∫ t in a..x, (x - t) * deriv (deriv f) t
      = -(x - a) * deriv f a + ∫ t in a..x, deriv f t := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := a) (b := x)
      (u := fun t : ℝ => x - t) (u' := fun _ : ℝ => (-1 : ℝ))
      (v := fun t : ℝ => deriv f t) (v' := fun t : ℝ => deriv (deriv f) t)
      (fun t _ => by simpa using (hasDerivAt_id t).const_sub x)
      hderiv1 intervalIntegrable_const hcont2.intervalIntegrable
    have hneg : (fun t : ℝ => (-1 : ℝ) * deriv f t) = fun t : ℝ => -(deriv f t) := by
      funext t
      ring
    rw [h, hneg, intervalIntegral.integral_neg]
    ring
  rw [hIBP, hFTC]
  ring

end Work.FTS.EllSol.EllPkgAux.MollSmooth
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.wExpCmp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

/-- A numerical bound: `e^{3/2} ≤ 5`.

This is the only numerical input needed by `wExpCmp`; it is proved from
`Real.exp_one_lt_d9 : exp 1 < 2.7182818286` by cubing. -/
lemma exp_three_halves_le_five : Real.exp (3 / 2) ≤ 5 := by
  have h3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [show (3 : ℝ) = 1 + (1 + 1) by norm_num, Real.exp_add, Real.exp_add]
    ring
  have hlt : (Real.exp 1) ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h25 : (2.7182818286 : ℝ) ^ 3 < 25 := by norm_num
  have hexp3 : Real.exp 3 < 25 := by rw [h3]; linarith
  have hsq : (Real.exp (3 / 2)) ^ 2 = Real.exp 3 := by
    rw [sq, ← Real.exp_add]; norm_num
  have hpos : 0 < Real.exp (3 / 2) := Real.exp_pos _
  nlinarith [hexp3, hsq, hpos]

/-- Comparison of the weight `w(z) = (1+z)²/z²` at `z = e^s` and `z = e^t`
for `|s - t| ≤ 1/2`:
`(w(e^s))² e^s ≤ 5 (w(e^t))² e^t`.

Since `w(e^u)² e^u = (1 + e^u)^4 e^{-3u}`, and writing `Q = e^t`, `R = e^{s-t}`
the claim becomes `(1 + QR)^4 ≤ 5 R^3 (1+Q)^4`, i.e.
`((1+QR)/(1+Q))^4 ≤ 5 R^3`.  For `R ≥ 1` one has `1 + QR ≤ R(1+Q)` and `R ≤ 5`;
for `R ≤ 1` one has `1 + QR ≤ 1 + Q` and `5 R^3 ≥ 1` because
`R ≥ e^{-1/2}` and `e^{3/2} ≤ 5`. -/
theorem wExpCmp (s t : ℝ) (hst : |s - t| ≤ 1 / 2) :
    (Work.Spaces.w (Real.exp s)) ^ 2 * Real.exp s
      ≤ 5 * ((Work.Spaces.w (Real.exp t)) ^ 2 * Real.exp t) := by
  have h5 : Real.exp (3 / 2) ≤ 5 := exp_three_halves_le_five
  obtain ⟨hu1, hu2⟩ := abs_le.mp hst
  set Q : ℝ := Real.exp t with hQdef
  set R : ℝ := Real.exp (s - t) with hRdef
  have hQpos : 0 < Q := by rw [hQdef]; exact Real.exp_pos t
  have hRpos : 0 < R := by rw [hRdef]; exact Real.exp_pos (s - t)
  have hP : Real.exp s = Q * R := by
    rw [hQdef, hRdef, ← Real.exp_add]
    rw [show t + (s - t) = s by ring]
  have hkey : (1 + Q * R) ^ 4 ≤ 5 * R ^ 3 * (1 + Q) ^ 4 := by
    have h4 : (0 : ℝ) ≤ (1 + Q) ^ 4 := by positivity
    rcases le_total 0 (s - t) with hu | hu
    · -- `R ≥ 1`
      have hR1 : 1 ≤ R := by
        rw [hRdef, ← Real.exp_zero]
        exact Real.exp_le_exp.mpr hu
      have hle : 1 + Q * R ≤ R * (1 + Q) := by nlinarith [hR1, hQpos]
      have hR5 : R ≤ 5 := by
        rw [hRdef]
        calc Real.exp (s - t) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hu2
          _ ≤ Real.exp (3 / 2) := Real.exp_le_exp.mpr (by norm_num)
          _ ≤ 5 := h5
      have hpow : (1 + Q * R) ^ 4 ≤ (R * (1 + Q)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hle 4
      have hR45 : R ^ 4 ≤ 5 * R ^ 3 := by
        have hh := mul_le_mul_of_nonneg_left hR5 (pow_nonneg hRpos.le 3)
        nlinarith [hh]
      calc (1 + Q * R) ^ 4 ≤ (R * (1 + Q)) ^ 4 := hpow
        _ = R ^ 4 * (1 + Q) ^ 4 := by ring
        _ ≤ 5 * R ^ 3 * (1 + Q) ^ 4 := mul_le_mul_of_nonneg_right hR45 h4
    · -- `R ≤ 1`
      have hR1 : R ≤ 1 := by
        rw [hRdef, ← Real.exp_zero]
        exact Real.exp_le_exp.mpr hu
      have hle : 1 + Q * R ≤ 1 + Q := by nlinarith [hR1, hQpos]
      have hpow : (1 + Q * R) ^ 4 ≤ (1 + Q) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hle 4
      have hR3eq : R ^ 3 = Real.exp (3 * (s - t)) := by
        rw [hRdef]
        exact (Real.exp_nat_mul (s - t) 3).symm
      have hu3 : -(3 / 2) ≤ 3 * (s - t) := by linarith [hu1]
      have hExp : Real.exp (-(3 / 2)) ≤ R ^ 3 := by
        rw [hR3eq]
        exact Real.exp_le_exp.mpr hu3
      have h5inv : (5 : ℝ)⁻¹ ≤ Real.exp (-(3 / 2)) := by
        rw [Real.exp_neg]
        have h := one_div_le_one_div_of_le (Real.exp_pos (3 / 2)) h5
        simpa [one_div] using h
      have h5R3 : 1 ≤ 5 * R ^ 3 := by
        have h := mul_le_mul_of_nonneg_left (le_trans h5inv hExp) (by norm_num : (0 : ℝ) ≤ 5)
        rw [mul_inv_cancel₀ (by norm_num : (5 : ℝ) ≠ 0)] at h
        exact h
      calc (1 + Q * R) ^ 4 ≤ (1 + Q) ^ 4 := hpow
        _ = 1 * (1 + Q) ^ 4 := by ring
        _ ≤ 5 * R ^ 3 * (1 + Q) ^ 4 := mul_le_mul_of_nonneg_right h5R3 h4
  have hL : (Work.Spaces.w (Real.exp s)) ^ 2 * Real.exp s
      = (1 + Real.exp s) ^ 4 / (Real.exp s) ^ 3 := by
    rw [Work.Spaces.w]; field_simp
  have hRside : (Work.Spaces.w (Real.exp t)) ^ 2 * Real.exp t
      = (1 + Real.exp t) ^ 4 / (Real.exp t) ^ 3 := by
    rw [Work.Spaces.w]; field_simp
  rw [hL, hRside, hP]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Q * R) ^ 3)]
  have hsimp : 5 * ((1 + Q) ^ 4 / Q ^ 3) * (Q * R) ^ 3 = 5 * R ^ 3 * (1 + Q) ^ 4 := by
    field_simp
  rw [hsimp]
  exact hkey

end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllSol.Flat.integrableOnSinTwoRpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Flat

open MeasureTheory Set
open scoped Real

/-- `sin (2θ) ^ c` is integrable on the closed interval `[0, π/2]` when `-1 < c`.

On `[0, π/2]` the weight vanishes only at the endpoints (a null set), so it suffices
to dominate it there: for `c ≥ 0` it is bounded by `1`, and for `c < 0` by the explicit
integrable majorant `(π/4) ^ (-c) * (θ ^ (-c) + (π/2 - θ) ^ (-c))`. -/
theorem integrableOn_sin_two_rpow_Icc {c : ℝ} (hc : -1 < c) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ c)
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ c)
      (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))) :=
    ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const c).aestronglyMeasurable
  have hsin0 : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  by_cases hc0 : 0 ≤ c
  · -- nonnegative exponent: bounded by the integrable constant `1`
    refine Integrable.mono'
      (MeasureTheory.integrableOn_const (s := Set.Icc (0 : ℝ) (Real.pi / 2))
        (C := (1 : ℝ)) ?_) hmeas ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have h0 := hsin0 θ hθ
      rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 c)]
      exact Real.rpow_le_one h0 (Real.sin_le_one (2 * θ)) hc0
  · -- negative exponent: Jordan's inequality gives an explicit `rpow` majorant
    have hcneg : c < 0 := not_le.mp hc0
    have hp0 : 0 < -c := by linarith
    have hp1 : -c < 1 := by linarith
    refine Integrable.mono'
      (Work.Spaces.integrableOn_majorant_rpow (-c) hp0 hp1) hmeas ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have h0 := hsin0 θ hθ
    rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 c)]
    simpa using Work.Spaces.sin_rpow_le_majorant (-c) θ hp0 hθ


end Work.FTS.EllSol.Flat
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.aemeasurable_of_continuousOn_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open scoped symmDiff

/-- A function on `ℝ × ℝ` which is continuous on the open strip `univ × (0, π/2)` is almost
everywhere measurable for the product of Lebesgue measure with Lebesgue measure restricted to
`Iθ = [0, π/2]`.  Indeed the strip `univ × Iθ` and the set where `F` is known to be continuous
differ by the null set `univ × {0, π/2}`, and restriction to a set is invariant under modification
of the set on a null set. -/
theorem aemeasurable_of_continuousOn_strip {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable F ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) := by
  -- `univ × {0, π/2}` is null for the product of Lebesgue measures.
  have hzero : (MeasureTheory.volume.prod MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      ((Set.univ : Set ℝ) ×ˢ ({0, Real.pi / 2} : Set ℝ)) = 0 := by
    have hsub : ({0, Real.pi / 2} : Set ℝ) ⊆ ({0} : Set ℝ) ∪ {Real.pi / 2} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] at hx ⊢
      tauto
    have h0 : MeasureTheory.volume ({0, Real.pi / 2} : Set ℝ) = 0 :=
      MeasureTheory.measure_mono_null hsub
        (MeasureTheory.measure_union_null Real.volume_singleton Real.volume_singleton)
    rw [MeasureTheory.Measure.prod_prod, h0]
    simp
  -- `Iθ` and `(0, π/2)` differ only by the endpoints.
  have hsubI : (Work.Spaces.Iθ ∆ Set.Ioo 0 (Real.pi / 2)) ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    rw [Set.mem_symmDiff] at hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hθ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Set.mem_Ioo] at h2
      by_cases h : θ ≤ 0
      · left; linarith [h1.1]
      · right
        have h' : 0 < θ := not_le.mp h
        by_contra hc
        exact h2 ⟨h', lt_of_le_of_ne h1.2 hc⟩
    · simp only [Set.mem_Ioo] at h1
      exfalso
      exact h2 ⟨le_of_lt h1.1, le_of_lt h1.2⟩
  -- hence `univ × Iθ` and `univ × (0, π/2)` agree almost everywhere.
  have hsym : ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ) ∆
        ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      ⊆ (Set.univ : Set ℝ) ×ˢ ({0, Real.pi / 2} : Set ℝ) := by
    intro p hp
    simp only [Set.mem_symmDiff, Set.mem_prod, Set.mem_univ, true_and] at hp ⊢
    exact hsubI hp
  have hnull := MeasureTheory.measure_mono_null hsym hzero
  have hae : ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)
      =ᵐ[(MeasureTheory.volume.prod MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))]
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.measure_symmDiff_eq_zero_iff.mp hnull
  have hrestrict := MeasureTheory.Measure.restrict_congr_set hae
  -- the product measure with a restricted second factor is a restriction of the product measure.
  have hprod : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict
        ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) := by
    rw [← MeasureTheory.Measure.prod_restrict
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) Set.univ Work.Spaces.Iθ,
      MeasureTheory.Measure.restrict_univ]
  rw [← hprod, hrestrict]
  exact hF.aemeasurable (MeasurableSet.univ.prod measurableSet_Ioo)

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.integrableOn_energy_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.EllSol.FlatFT

/-- If the jointly measurable product `(z,θ) ↦ φ z θ ^ 2 * w θ` is integrable on
`ℝ × Iθ`, then the `z`-energy `θ ↦ (∫ z, φ z θ ^ 2) * w θ` is integrable on `Iθ`.

This is the Fubini/Tonelli "second marginal" statement: the joint integrand is
`(z,θ) ↦ φ z θ ^ 2 * w θ`, whose `z`-integral is `(∫ z, φ z θ ^ 2) * w θ`
(by `integral_mul_const`, and trivially where `w θ = 0`). -/
theorem integrableOn_energy_mul {φ : ℝ → ℝ → ℝ} {w : ℝ → ℝ} (hw : Measurable w)
    (hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (φ p.1 p.2) ^ 2 * w p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (∫ t : ℝ, (φ t θ) ^ 2) * w θ) Work.Spaces.Iθ := by
  -- Step 1: turn the `IntegrableOn (univ ×ˢ Iθ)` hypothesis into integrability for the
  -- product measure `volume.prod (volume.restrict Iθ)`.
  have h1 : Integrable (fun p : ℝ × ℝ => (φ p.1 p.2) ^ 2 * w p.2)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    hprod
  rw [← Measure.prod_restrict (s := (Set.univ : Set ℝ)) (t := Work.Spaces.Iθ),
    Measure.restrict_univ] at h1
  -- Step 2: Fubini — the second marginal is integrable.
  have hint := h1.integral_prod_right
  -- Step 3: identify the second marginal with the stated function pointwise.
  refine hint.congr (Eventually.of_forall fun θ => ?_)
  show (∫ x : ℝ, (φ x θ) ^ 2 * w θ) = (∫ t : ℝ, (φ t θ) ^ 2) * w θ
  by_cases hw0 : w θ = 0
  · simp [hw0]
  · rw [integral_mul_const]

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.SpecAux.FlipDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.SpecAux

open MeasureTheory Set
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The time reversal `(t,θ) ↦ u (-t) θ`. -/
def timFlip (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ => u (-t) θ

@[simp] theorem timFlip_apply (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    timFlip u t θ = u (-t) θ := rfl

@[simp] theorem timFlip_neg (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    timFlip u (-t) θ = u t θ := by simp [timFlip]




/-- The reversal of the uncurrying is the composition with the (smooth) map
`(t,θ) ↦ (-t,θ)`. -/
theorem uncurry_timFlip_eq_comp (u : ℝ → ℝ → ℝ) :
    Function.uncurry (timFlip u) = Function.uncurry u ∘ fun p : ℝ × ℝ => (-p.1, p.2) := by
  funext p
  simp [Function.uncurry, timFlip]

end

end Work.FTS.EllSol.SpecAux
end
-- ===== merged: Submission.Work.FTS.EllSol.VthAux.endpoint.SigmaBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VthAux.endpoint

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The weight `sin (2θ) ^ (-η)` is `≥ 1` on the open interval. -/
theorem one_le_sigma {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs := sin_two_pos_of_mem hθ
  have hpow : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 := by
    have h1 : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ (1 : ℝ) ^ Work.Spaces.eta :=
      Real.rpow_le_rpow hs.le (Real.sin_le_one _) Work.Spaces.eta_pos.le
    simpa using h1
  rw [Real.rpow_neg hs.le]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos hs _)).mpr hpow

theorem restrict_Itheta :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  apply Measure.restrict_congr_set
  show Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2)
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

theorem ae_mem_Ioo_Itheta :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [restrict_Itheta]
  exact ae_restrict_mem isOpen_Ioo.measurableSet



/-- `(∫_a^b u v)² ≤ (∫_a^b u²) (∫_a^b v²)` for interval integrals (`a ≤ b`). -/
theorem sq_integral_mul_le {a b : ℝ} (hab : a ≤ b) {u v : ℝ → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (Set.Ioc a b)))
    (hv : AEStronglyMeasurable v (volume.restrict (Set.Ioc a b)))
    (hu2 : MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) (Set.Ioc a b))
    (hv2 : MeasureTheory.IntegrableOn (fun x => (v x) ^ 2) (Set.Ioc a b)) :
    (∫ x in a..b, u x * v x) ^ 2
      ≤ (∫ x in a..b, (u x) ^ 2) * (∫ x in a..b, (v x) ^ 2) := by
  have h := Work.Spaces.cs_integral
    ((MeasureTheory.memLp_two_iff_integrable_sq hu).mpr hu2)
    ((MeasureTheory.memLp_two_iff_integrable_sq hv).mpr hv2)
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hab] at h
  exact h



/-- `Icc a b ⊆ (0, π/2)` whenever both endpoints are in `(0, π/2)`. -/
theorem Icc_subset_Ioo {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  intro x hx
  rw [Set.mem_Icc] at hx
  exact ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩

/-- `|∫_a^b g| ≤ √(b-a) √(∫_a^b g²)` for `a ≤ b` (Cauchy–Schwarz with the constant function
`1`). -/
theorem abs_integral_le_sqrt_mul_sqrt {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Icc a b))
    (hint : MeasureTheory.IntegrableOn (fun x => (g x) ^ 2) (Set.Icc a b)) :
    |∫ x in a..b, g x| ≤ Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, (g x) ^ 2) := by
  have hcontIoc : ContinuousOn g (Set.Ioc a b) := hcont.mono Set.Ioc_subset_Icc_self
  have hii : MeasureTheory.IntegrableOn (fun x => (g x) ^ 2) (Set.Ioc a b) :=
    hint.mono_set Set.Ioc_subset_Icc_self
  have hone : MeasureTheory.IntegrableOn (fun x : ℝ => (1 : ℝ) ^ 2) (Set.Ioc a b) :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ) ^ 2)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hcs := sq_integral_mul_le hab (hcontIoc.aestronglyMeasurable measurableSet_Ioc)
    aestronglyMeasurable_const hii hone
  have h1 : (∫ x in a..b, (1 : ℝ) ^ 2) = b - a := by
    rw [intervalIntegral.integral_const]
    norm_num
  rw [h1] at hcs
  have hcs' : (∫ x in a..b, g x) ^ 2 ≤ (∫ x in a..b, (g x) ^ 2) * (b - a) := by
    simpa using hcs
  calc |∫ x in a..b, g x| = Real.sqrt ((∫ x in a..b, g x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∫ x in a..b, (g x) ^ 2) * (b - a)) := Real.sqrt_le_sqrt hcs'
    _ = Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, (g x) ^ 2) := by
        rw [Real.sqrt_mul (intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)), mul_comm]

end Work.FTS.EllSol.VthAux.endpoint
end
end
-- ===== merged: Submission.Work.FTS.EllSol.VthAux.traceAux.hardyPowAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAux.traceAux

open MeasureTheory Set Filter
open scoped Real Topology ENNReal Interval





end Work.FTS.EllSol.VthAux.traceAux
end
-- ===== merged: Submission.Work.FTS.EllSol.c2_deriv_sub_eq_intervalIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllSol

/-- The fundamental theorem of calculus for a `C²` function on an open interval: the
increment of the first derivative is the integral of the second derivative. -/
theorem c2_deriv_sub_eq_intervalIntegral {h : ℝ → ℝ} {ε a b : ℝ}
    (hC2 : ContDiffOn ℝ 2 h (Set.Ioo 0 ε)) (ha : 0 < a) (hab : a ≤ b) (hb : b < ε) :
    deriv h b - deriv h a = ∫ x in a..b, deriv (deriv h) x := by
  have hsub : Icc a b ⊆ Ioo 0 ε := fun x hx =>
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hcont : ContinuousOn (deriv h) (Icc a b) := (c2_continuousOn_deriv hC2).mono hsub
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt (deriv h) (deriv (deriv h) x) x :=
    fun x hx => c2_hasDerivAt_deriv hC2 (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv
    (c2_intervalIntegrable_deriv_deriv hC2 ha hab hb)).symm

end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EllSol.thetaWeightedCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.EllSol



end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeStepOneAux.HardyBddDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeStepOneAux

set_option autoImplicit false

/-- The sharp constant `a = (1+η)/2` of the weighted Hardy inequality. -/
noncomputable def hbA : ℝ := (1 + Work.Spaces.eta) / 2

theorem hbA_pos : 0 < hbA := by
  rw [hbA]
  have := Work.Spaces.eta_pos
  linarith

theorem hbA_nonneg : 0 ≤ hbA := le_of_lt hbA_pos





/-- The flux `G θ = 2a·cos(2θ)·(f θ)²·sin(2θ)^{-(1+η)}` of the weighted Hardy inequality. -/
noncomputable def hbPrim (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  2 * hbA * Real.cos (2 * θ) * (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))

/-- The explicit derivative of the flux `hbPrim`. -/
noncomputable def hbDeriv (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -4 * hbA * Real.sin (2 * θ) * (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
  + 4 * hbA * Real.cos (2 * θ) * (f θ) * deriv f θ * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
  - 4 * hbA * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2 * (f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))

/-- The identity `hbPrim f θ = 2·hbA·cos(2θ)·(f θ)²·sin(2θ)^{-(1+η)}` (definitional). -/
theorem hbPrim_def (f : ℝ → ℝ) (θ : ℝ) :
    hbPrim f θ = 2 * hbA * Real.cos (2 * θ) * (f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := rfl

end Work.FTS.EllipticEst.AeStepOneAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.weighted_slice_mono =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Alpha4


end Work.FTS.EllipticEst.Alpha4
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeZWtIBP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# An integration-by-parts identity in the radial variable `z`

The lemma `aeZWtIBP` is the weak-form integration-by-parts identity used in the
`AngAWeak` chain.  For `W` of class `C²` with compact support vanishing near `0` and
`φ, v` of class `C²` on `(0, ∞)` it states

  ∫ Wφ (-α²z² v'' - α(5+α)z v') v = α² ∫ Wφz² (v')²
      + (α(5+α)/2) ∫ (Wφz)' v² - (α²/2) ∫ (Wφz²)'' v²,

i.e. that the one-dimensional operator `L = -α²z² ∂² - α(5+α)z ∂` is formally
self-adjoint for the weight `W φ`.

The proof goes through the auxiliary function

  `T = -α²(Wφz²)v v' + (α²/2)(Wφz²)' v² - (α(5+α)/2)(Wφz)v²`,

whose derivative is the difference of the two integrands; the fundamental theorem of
calculus on `(0,∞)` (both boundary limits vanish, since everything is supported in
`[a,b]`) gives the identity.
-/

namespace Work.FTS.EllipticEst.AngAWeak

open MeasureTheory Set Filter
open scoped Topology

set_option autoImplicit false

/-- A function which is continuous on a compact interval and vanishes outside of it is
integrable on `(0, ∞)`. -/
private lemma integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
    {f : ℝ → ℝ} {c d : ℝ} (_hcd : c ≤ d)
    (hcont : ContinuousOn f (Set.Icc c d))
    (hzero : ∀ x, x ∉ Set.Icc c d → f x = 0) :
    IntegrableOn f (Set.Ioi 0) := by
  have h1 : IntegrableOn f (Set.Icc c d) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hcont
  have h2 : Integrable ((Set.Icc c d).indicator f) := h1.integrable_indicator measurableSet_Icc
  have h3 : f = (Set.Icc c d).indicator f := by
    funext x
    by_cases hx : x ∈ Set.Icc c d
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, hzero x hx]
  rw [← h3] at h2
  exact h2.integrableOn



end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.sliceLipschitzLeft =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open Filter Set MeasureTheory
open scoped Topology

set_option linter.style.haveILetI false


end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeakFts.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- The flux `Φ θ = f θ² cos(2θ) sin(2θ)^{-(1+η)}` of the Hardy argument. -/
def hardyFtsFlux (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (f θ) ^ 2 * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))

/-- The left hand integrand `f² cos²(2θ) sin(2θ)^{-(2+η)}`. -/
def hardyFtsL (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))

/-- The right hand integrand `(f')² sin(2θ)^{-η}`. -/
def hardyFtsD (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)

/-- The middle term `f² sin(2θ)^{-η}` (nonnegative). -/
def hardyFtsB (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)

/-- The cross term `f f' cos(2θ) sin(2θ)^{-(1+η)}`. -/
def hardyFtsG (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  deriv f θ * f θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))

/-- `sin(2θ) > 0` on the open angular interval. -/
theorem hardyFts_sin_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≥ 0` on the closed angular interval. -/
theorem hardyFts_sin_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])



end Work.FTS.EllipticEst.AngAWeak

end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGap.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

set_option autoImplicit false



/-- The primitive `G θ = ∫₀^θ h s · sin (2s) ds` of `h · sin 2θ`. -/
def angG (h : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ s in (0 : ℝ)..θ, h s * Real.sin (2 * s)

/-- `V = G / sin 2θ`, the `K`-variable of the weighted problem. -/
def angV (h : ℝ → ℝ) (θ : ℝ) : ℝ := angG h θ / Real.sin (2 * θ)

/-- `Q = h' - 2 cot(2θ) · h = sin 2θ · (h / sin 2θ)'`. -/
def angQ (h : ℝ → ℝ) (θ : ℝ) : ℝ := deriv h θ - 2 * Real.cot (2 * θ) * h θ

/-- The antiderivative of the completion-of-squares identity: `Φ_D = -2 h² cot 2θ`. -/
def angPhiD (h : ℝ → ℝ) (θ : ℝ) : ℝ := -2 * (h θ) ^ 2 * Real.cot (2 * θ)

/-- The antiderivative of the weighted Hardy identity: `Φ_H = 6 V² cot 2θ = 6 G² cos2θ / sin³2θ`. -/
def angPhiH (h : ℝ → ℝ) (θ : ℝ) : ℝ := 6 * (angV h θ) ^ 2 * Real.cot (2 * θ)

/-- The antiderivative of the integration-by-parts identity: `Φ_C = V · h = G h / sin 2θ`. -/
def angPhiC (h : ℝ → ℝ) (θ : ℝ) : ℝ := angV h θ * h θ

/-! ## Elementary facts about `sin (2θ)` and `cot (2θ)` on `(0, π/2)` -/

/-- On `(0, π/2)`, `sin (2θ) > 0`. -/
theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The derivative of `θ ↦ cot (2θ)` on `(0, π/2)`. -/
theorem hasDerivAt_cot_two (x : ℝ) (hx : x ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ : ℝ => Real.cot (2 * θ)) (-2 * (1 + (Real.cot (2 * x)) ^ 2)) x := by
  have hsinpos : 0 < Real.sin (2 * x) := sin_two_pos hx
  have hsin : Real.sin (2 * x) ≠ 0 := ne_of_gt hsinpos
  have h1 : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-(2 * Real.sin (2 * x))) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_cos (2 * x)).comp x (hasDerivAt_const_mul (x := x) (2 : ℝ))
  have h2 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * x)) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * x)).comp x (hasDerivAt_const_mul (x := x) (2 : ℝ))
  have h3 := h1.div h2 hsin
  have hfun : (fun θ : ℝ => Real.cot (2 * θ))
      = fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ) := by
    funext θ; rw [Real.cot_eq_cos_div_sin]
  rw [hfun]
  refine h3.congr_deriv ?_
  have hcot : Real.cot (2 * x) = Real.cos (2 * x) / Real.sin (2 * x) := Real.cot_eq_cos_div_sin (2 * x)
  rw [hcot]
  field_simp
  ring_nf

/-- On `(0, π/2)`, `|cot (2θ)| ≤ 1/sin (2θ)`. -/
theorem abs_cot_two_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Real.cot (2 * θ)| ≤ 1 / Real.sin (2 * θ) := by
  have hsinpos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsinpos]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hsinpos.le

end Work.FTS.EllipticEst.AngGap
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

open MeasureTheory

/-- Helper: if `f` is integrable on `s` and nonnegative on `s`, then `f ≥ 0` almost everywhere for
`volume.restrict s`.

Note that `s` is *not* assumed measurable, so `∀ᵐ z ∂(volume.restrict s), z ∈ s` is in general
false and one has to argue through `Measure.restrict_apply₀`, which evaluates
`(volume.restrict s) t` for null-measurable `t`. -/
private lemma ae_nonneg_of_on {s : Set ℝ} {f : ℝ → ℝ} (hf : IntegrableOn f s)
    (hn : ∀ z ∈ s, 0 ≤ f z) : ∀ᵐ z ∂(volume.restrict s), 0 ≤ f z := by
  rw [ae_iff]
  have hset : {a : ℝ | ¬ 0 ≤ f a} = {z : ℝ | f z < 0} := by ext z; exact not_le
  rw [hset]
  rw [Measure.restrict_apply₀
    (hf.aestronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const)]
  have hempty : {z : ℝ | f z < 0} ∩ s = ∅ := by
    ext z; constructor
    · intro hz; exact absurd (hn z hz.2) (not_le.mpr hz.1)
    · intro hz; exact absurd hz (Set.notMem_empty z)
  rw [hempty, measure_empty]

/-- Helper: a pointwise inequality on `s` between two a.e. strongly measurable functions is an
a.e. inequality for `volume.restrict s` (again for arbitrary `s`: only the null-measurable set
`{z | g z < f z}` is measured, via `Measure.restrict_apply₀`). -/
private lemma ae_le_of_on {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s))
    (hg : AEStronglyMeasurable g (volume.restrict s))
    (h : ∀ z ∈ s, f z ≤ g z) : f ≤ᵐ[volume.restrict s] g := by
  show ∀ᵐ z ∂(volume.restrict s), f z ≤ g z
  rw [ae_iff]
  have hset : {a : ℝ | ¬ f a ≤ g a} = {z : ℝ | g z < f z} := by ext z; exact not_le
  rw [hset]
  rw [Measure.restrict_apply₀ (hg.nullMeasurableSet_lt hf)]
  have hempty : {z : ℝ | g z < f z} ∩ s = ∅ := by
    ext z; constructor
    · intro hz; exact absurd (h z hz.2) (not_le.mpr hz.1)
    · intro hz; exact absurd hz (Set.notMem_empty z)
  rw [hempty, measure_empty]

/-- Helper: for `f ≥ 0` on `s`, `z ↦ √(f z)²` agrees with `f` a.e. for `volume.restrict s`. -/
private lemma sqrt_sq_ae_eq {s : Set ℝ} {f : ℝ → ℝ} (hf : IntegrableOn f s)
    (hn : ∀ z ∈ s, 0 ≤ f z) : (fun z => Real.sqrt (f z) ^ 2) =ᵐ[volume.restrict s] f := by
  filter_upwards [ae_nonneg_of_on hf hn] with z hz
  exact Real.sq_sqrt hz

/-- **The radial ("in `z`") Cauchy–Schwarz step.**

If `C` is pointwise dominated by `√A · √B` on `s`, where `A` and `B` are integrable and
nonnegative on `s`, then `|∫_s C| ≤ √(∫_s A) · √(∫_s B)`.

Route: `|∫_s C| ≤ ∫_s |C| ≤ ∫_s √A·√B` (the last integrand is integrable by
`Work.Coercivity.integrable_sqrt_mul_sqrt`, dominated by `(A+B)/2`), then Cauchy–Schwarz
(`Work.Coercivity.holder_two_mul`) with `u = √∘A`, `v = √∘B` — whose a.e. strong measurability
comes from the integrability of `A`, `B` — gives `(∫_s √A·√B)² ≤ (∫_s A)(∫_s B)`, and taking
square roots (both sides are nonnegative) yields `∫_s √A·√B ≤ √(∫_s A)·√(∫_s B)`. -/
theorem abs_setIntegral_le_sqrt_mul_sqrt {s : Set ℝ} {A B C : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A s) (hB : MeasureTheory.IntegrableOn B s)
    (hC : MeasureTheory.IntegrableOn C s)
    (hAn : ∀ z ∈ s, 0 ≤ A z) (hBn : ∀ z ∈ s, 0 ≤ B z)
    (h : ∀ z ∈ s, |C z| ≤ Real.sqrt (A z) * Real.sqrt (B z)) :
    |∫ z in s, C z| ≤ Real.sqrt (∫ z in s, A z) * Real.sqrt (∫ z in s, B z) := by
  set ν : Measure ℝ := volume.restrict s with hν
  -- `√∘A` and `√∘B` are a.e. strongly measurable, and their squares are integrable
  have aA : AEStronglyMeasurable (fun z => Real.sqrt (A z)) ν :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have aB : AEStronglyMeasurable (fun z => Real.sqrt (B z)) ν :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hsqA : Integrable (fun z => Real.sqrt (A z) ^ 2) ν :=
    hA.congr (sqrt_sq_ae_eq hA hAn).symm
  have hsqB : Integrable (fun z => Real.sqrt (B z) ^ 2) ν :=
    hB.congr (sqrt_sq_ae_eq hB hBn).symm
  -- Cauchy–Schwarz for `L²` (also gives integrability of the product)
  obtain ⟨hABint, hABcs⟩ :=
    Work.Coercivity.holder_two_mul ν (fun z => Real.sqrt (A z)) (fun z => Real.sqrt (B z))
      aA aB hsqA hsqB
  have hABcs' : |∫ z, Real.sqrt (A z) * Real.sqrt (B z) ∂ν| ≤
      Real.sqrt (∫ z, A z ∂ν) * Real.sqrt (∫ z, B z ∂ν) := by
    have hh := hABcs
    rwa [integral_congr_ae (sqrt_sq_ae_eq hA hAn),
      integral_congr_ae (sqrt_sq_ae_eq hB hBn)] at hh
  -- the pointwise domination on `s`, upgraded to an a.e. domination
  have hle : (fun z => |C z|) ≤ᵐ[ν] (fun z => Real.sqrt (A z) * Real.sqrt (B z)) :=
    ae_le_of_on (continuous_abs.comp_aestronglyMeasurable hC.aestronglyMeasurable)
      (aA.mul aB) h
  have h1 : |∫ z, C z ∂ν| ≤ ∫ z, |C z| ∂ν := abs_integral_le_integral_abs
  calc |∫ z, C z ∂ν| ≤ ∫ z, |C z| ∂ν := h1
    _ ≤ ∫ z, Real.sqrt (A z) * Real.sqrt (B z) ∂ν := integral_mono_ae hC.abs hABint hle
    _ ≤ |∫ z, Real.sqrt (A z) * Real.sqrt (B z) ∂ν| := le_abs_self _
    _ ≤ Real.sqrt (∫ z, A z ∂ν) * Real.sqrt (∫ z, B z ∂ν) := hABcs'

end Work.FTS.EllipticEst.AngSecond
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.lintegral_w_sq_shift_two_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false

/-! ## Change of variables for the lower Lebesgue integral on `(0,∞)` -/

/-- **Change of variables** `z ↦ c * z` (`c > 0`) for the lower Lebesgue integral over
`(0,∞)`:  `∫_{z > 0} F (c z) dz = c⁻¹ ∫_{z > 0} F z dz`.

No (a.e.) measurability of `F` is required: `z ↦ c z` is a measurable equivalence of `ℝ` and
`MeasureTheory.lintegral_map_equiv` holds for arbitrary `ℝ≥0∞`-valued integrands. -/
theorem lintegral_Ioi_comp_mul_pos (c : ℝ) (hc : 0 < c) (F : ℝ → ENNReal) :
    (∫⁻ z in Set.Ioi 0, F (c * z)) = ENNReal.ofReal c⁻¹ * ∫⁻ z in Set.Ioi 0, F z := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hmem : ∀ z : ℝ, (z ∈ Set.Ioi 0) ↔ (c * z ∈ Set.Ioi 0) := by
    intro z
    simp only [Set.mem_Ioi]
    exact (mul_pos_iff_of_pos_left hc).symm
  -- the same statement without the restriction to `(0,∞)`
  have hmain : ∀ H : ℝ → ENNReal, (∫⁻ z, H (c * z)) = ENNReal.ofReal c⁻¹ * ∫⁻ z, H z := by
    intro H
    let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc0).toMeasurableEquiv
    have he : ⇑e = (fun z : ℝ => c * z) := rfl
    have hmap : Measure.map (⇑e) volume = ENNReal.ofReal c⁻¹ • volume := by
      rw [he, Real.map_volume_mul_left hc0, abs_of_pos (inv_pos.mpr hc)]
    calc ∫⁻ z, H (c * z)
        = ∫⁻ z, H (e z) := by rw [he]
      _ = ∫⁻ z, H z ∂(Measure.map (⇑e) volume) := (lintegral_map_equiv H e).symm
      _ = ∫⁻ z, H z ∂(ENNReal.ofReal c⁻¹ • volume) := by rw [hmap]
      _ = ENNReal.ofReal c⁻¹ * ∫⁻ z, H z := by
            rw [lintegral_smul_measure, smul_eq_mul]
  -- restrict to `(0,∞)`: the indicators of `(0,∞)` agree for `F` and `F ∘ (c * ·)`
  set G : ℝ → ENNReal := Set.indicator (Set.Ioi 0) F with hG
  have hL : (∫⁻ z in Set.Ioi 0, F (c * z)) = ∫⁻ z, G (c * z) := by
    rw [← lintegral_indicator measurableSet_Ioi (fun z => F (c * z))]
    refine lintegral_congr (fun z => ?_)
    rw [hG]
    by_cases hz : z ∈ Set.Ioi 0
    · rw [Set.indicator_of_mem ((hmem z).mp hz), Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem (fun h => hz ((hmem z).mpr h)), Set.indicator_of_notMem hz]
  calc (∫⁻ z in Set.Ioi 0, F (c * z))
      = ∫⁻ z, G (c * z) := hL
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ z, G z := hmain G
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ z in Set.Ioi 0, F z := by
          rw [hG, lintegral_indicator measurableSet_Ioi F]

/-! ## The pointwise weight comparison -/


/-! ## The main estimate -/


end Work.FTS.EllipticEst.AngSecond
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.aesm_integral_divCosSq_Ico =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Auxiliary


end Work.FTS.EllipticEst.Auxiliary
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.continuousOn_antideriv_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology Real
open Filter

namespace Work.FTS.EllipticEst.Auxiliary

theorem continuousOn_antideriv_fts (f : ℝ → ℝ)
    (hs : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h1 : f (π / 2) = 0) :
    ContinuousOn (fun θ => -(derivWithin f (Set.Icc 0 (π / 2)) θ) * f θ
      + (1 / 2) * Real.tan θ * (f θ) ^ 2) (Set.Icc 0 (π / 2)) := by
  have hpi : (0 : ℝ) < π / 2 := Real.pi_div_two_pos
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hpi
  have hderiv : ContinuousOn (derivWithin f (Set.Icc 0 (π / 2))) (Set.Icc 0 (π / 2)) :=
    hs.continuousOn_derivWithin hU (by norm_num)
  have hf : ContinuousOn f (Set.Icc 0 (π / 2)) := hs.continuousOn
  have hA : ContinuousOn (fun θ => -(derivWithin f (Set.Icc 0 (π / 2)) θ) * f θ)
      (Set.Icc 0 (π / 2)) := hderiv.neg.mul hf
  obtain ⟨C, _hC0, hCb⟩ :=
    Work.FTS.EllipticEst.exists_bound_div_cos f hs h1
  have htan_id : ∀ θ : ℝ,
      Real.tan θ * (f θ) ^ 2 = Real.sin θ * (f θ / Real.cos θ) * f θ := by
    intro θ
    rw [Real.tan_eq_sin_div_cos]
    ring
  have hmem : (π / 2) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_of_lt hpi, le_refl _⟩
  have hB : ContinuousOn (fun θ => (1 / 2) * Real.tan θ * (f θ) ^ 2)
      (Set.Icc 0 (π / 2)) := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with hxeq | hxlt
    · -- endpoint `x = π/2`: the factor `tan θ * f θ²` is squeezed by `f θ → 0`
      rw [hxeq, ContinuousWithinAt]
      rw [show (1 / 2) * Real.tan (π / 2) * (f (π / 2)) ^ 2 = 0 by simp [h1]]
      have hbound : Tendsto (fun θ => (1 / 2) * C * |f θ|)
          (𝓝[Set.Icc 0 (π / 2)] (π / 2)) (𝓝 0) := by
        have hft : Tendsto f (𝓝[Set.Icc 0 (π / 2)] (π / 2)) (𝓝 0) := by
          have h := (hf.continuousWithinAt hmem).tendsto
          rwa [h1] at h
        simpa using hft.abs.const_mul ((1 / 2) * C)
      refine squeeze_zero_norm' (a := fun θ => (1 / 2) * C * |f θ|) ?_ hbound
      · filter_upwards [self_mem_nhdsWithin] with θ hθ
        rw [Real.norm_eq_abs]
        have hb : |Real.tan θ * (f θ) ^ 2| ≤ C * |f θ| := by
          rw [htan_id θ, abs_mul, abs_mul]
          calc |Real.sin θ| * |f θ / Real.cos θ| * |f θ|
              ≤ 1 * C * |f θ| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul (Real.abs_sin_le_one θ) (hCb θ hθ)
                    (abs_nonneg _) (by norm_num))
                  (abs_nonneg _)
            _ = C * |f θ| := by ring
        calc |(1 / 2) * Real.tan θ * (f θ) ^ 2|
            = (1 / 2) * |Real.tan θ * (f θ) ^ 2| := by
              rw [show (1 / 2) * Real.tan θ * (f θ) ^ 2
                    = (1 / 2) * (Real.tan θ * (f θ) ^ 2) by ring,
                abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          _ ≤ (1 / 2) * (C * |f θ|) := mul_le_mul_of_nonneg_left hb (by norm_num)
          _ = (1 / 2) * C * |f θ| := by ring
    · -- interior point: `tan` is continuous there
      have hcos : Real.cos x ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, hpi], hxlt⟩)
      have htan : ContinuousWithinAt Real.tan (Set.Icc 0 (π / 2)) x :=
        (Real.continuousAt_tan.mpr hcos).continuousWithinAt
      have hfx : ContinuousWithinAt f (Set.Icc 0 (π / 2)) x := hf x hx
      exact ((continuousWithinAt_const (b := (1 / 2))).mul htan).mul (hfx.pow 2)
  exact hA.add hB

end Work.FTS.EllipticEst.Auxiliary
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.integrableOn_Iz_of_support_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Auxiliary


end Work.FTS.EllipticEst.Auxiliary
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.pIBP_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Auxiliary

open scoped Real Topology
open MeasureTheory Set Filter

/-- `deriv (sin (2θ)) = 2 cos (2θ)`. -/
lemma deriv_sin_two : deriv (fun θ : ℝ => Real.sin (2 * θ)) = fun θ : ℝ => 2 * Real.cos (2 * θ) := by
  funext θ
  have h1 : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    simpa only [Function.comp_def, mul_comm] using ((Real.hasDerivAt_sin (2 * θ)).comp θ h1)
  exact h2.deriv

/-- `θ ↦ 2 cos (2θ)` is `C²`. -/
lemma contDiff_cos_two : ContDiff ℝ 2 (fun θ : ℝ => 2 * Real.cos (2 * θ)) := by
  have h2 : ContDiff ℝ 2 (fun θ : ℝ => (2 : ℝ) * θ) := contDiff_const.mul contDiff_id
  exact contDiff_const.mul (Real.contDiff_cos.comp h2)

/-- `deriv (2 cos (2θ)) = -4 sin (2θ)`. -/
lemma deriv_cos_two : deriv (fun θ : ℝ => 2 * Real.cos (2 * θ))
    = fun θ : ℝ => -4 * Real.sin (2 * θ) := by
  funext θ
  have h1 : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-Real.sin (2 * θ) * 2) θ := by
    simpa only [Function.comp_def, mul_comm] using ((Real.hasDerivAt_cos (2 * θ)).comp θ h1)
  have h3 : HasDerivAt (fun θ : ℝ => 2 * Real.cos (2 * θ)) (2 * (-Real.sin (2 * θ) * 2)) θ :=
    h2.const_mul 2
  rw [h3.deriv]
  ring

/-- Two integrations by parts against `sin (2θ)`: the boundary terms vanish because
`f` is `C²` on `[0,π/2]` and vanishes at both endpoints. -/
theorem pIBP_fts (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) (h0 : f 0 = 0)
    (h1 : f (π / 2) = 0) :
    (∫ θ in Work.Spaces.Iθ, deriv f θ * deriv (fun θ => Real.sin (2 * θ)) θ)
      = 4 * (∫ θ in Work.Spaces.Iθ, f θ * Real.sin (2 * θ)) := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hle : (0 : ℝ) ≤ π / 2 := hpi.le
  -- rewrite the set integrals over `Iθ = [0,π/2]` as interval integrals
  have hconv : ∀ g : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, g θ = ∫ θ in (0 : ℝ)..(π / 2), g θ := by
    intro g
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [hconv (fun θ => deriv f θ * deriv (fun θ => Real.sin (2 * θ)) θ),
    hconv (fun θ => f θ * Real.sin (2 * θ))]
  -- replace `deriv (sin (2θ))` by `2 cos (2θ)`
  rw [intervalIntegral.integral_congr (fun θ _ => by rw [deriv_sin_two])]
  -- integration by parts against the `C²` function `θ ↦ 2 cos (2θ)`
  have hIBP := Work.FTS.EllipticEst.ibp_contdiffon hpi (h := f)
    (ψ := fun θ : ℝ => 2 * Real.cos (2 * θ)) hf contDiff_cos_two
  rw [hIBP]
  -- the boundary terms vanish
  have hb : f (π / 2) * (2 * Real.cos (2 * (π / 2))) - f 0 * (2 * Real.cos (2 * 0)) = 0 := by
    rw [h0, h1]
    ring
  rw [hb, zero_sub]
  -- evaluate the remaining integral
  have hIntEq : (∫ x in (0 : ℝ)..(π / 2), f x * deriv (fun θ : ℝ => 2 * Real.cos (2 * θ)) x)
      = ∫ x in (0 : ℝ)..(π / 2), (-4) * (f x * Real.sin (2 * x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    rw [deriv_cos_two]
    ring
  rw [hIntEq, intervalIntegral.integral_const_mul]
  ring

end Work.FTS.EllipticEst.Auxiliary
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Auxiliary.zIBP1_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
-- The statement's hypotheses `hf_cont` and `hg_cont` are not needed for the identity
-- (only continuity of the derivatives is), but they are part of the requested statement.
set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllipticEst.Auxiliary

/-- A function vanishing on `(R, ∞)` (with `0 ≤ R`) has the same integral over
`Iz = [0, ∞)` as over `[0, R]`. -/
theorem setIntegral_Iz_eq_Icc {R : ℝ} (hR : 0 ≤ R) (h : ℝ → ℝ)
    (hh : ∀ x, R < x → h x = 0) :
    ∫ x in Work.Spaces.Iz, h x = ∫ x in Set.Icc (0 : ℝ) R, h x := by
  have hI : Work.Spaces.Iz = Set.Icc (0 : ℝ) R ∪ Set.Ioi R := by
    rw [Work.Spaces.Iz, ← Set.Icc_union_Ioi_eq_Ici hR]
  rw [hI]
  exact MeasureTheory.integral_union_eq_left_of_forall measurableSet_Ioi fun x hx => hh x hx


end Work.FTS.EllipticEst.Auxiliary
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

-- `hθ` is part of the requested signature but is not needed by the proof.
set_option linter.unusedVariables false in
/-- **An angular derivative divisible by `sin 2θ` costs nothing against the mixed weight.**
PLACEMENT: file `Submission/Work/FTS/EllipticEst/Blocks/angular_sq_mul_Wt_sq_le.lean`,
namespace `Work.FTS.EllipticEst.Blocks`, so the fully qualified name is
`Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le`.
If `d² ≤ K · sin(2θ)²` at `θ ∈ (0,π/2)` and `K ≥ 0`, then for arbitrary `u, α, z`
`(d·u)² · Wt(α,z,θ)² ≤ K · (u · Wt(α,z,θ))²`,
where `Wt α z θ = Work.Spaces.w z · sin(2θ)^{-γ/2}`, `γ = 1 + α/10`
(`Submission/Work/Spaces/Defs.lean`).  Indeed `sin(2θ)² ≤ 1`, so `hd` gives `d² ≤ K`; multiply by
the nonnegative factor `u² · Wt²`.  No hypothesis on `α` is needed (`hθ` is only cosmetic). -/
theorem angular_sq_mul_Wt_sq_le {K d u α z θ : ℝ} (hK : 0 ≤ K)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hd : d ^ 2 ≤ K * (Real.sin (2 * θ)) ^ 2) :
    (d * u) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      ≤ K * (u * Work.Spaces.Wt α z θ) ^ 2 := by
  have hsin : (Real.sin (2 * θ)) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
  have hdK : d ^ 2 ≤ K := by nlinarith [hK, hsin]
  have hmain : d ^ 2 * u ^ 2 ≤ K * u ^ 2 :=
    mul_le_mul_of_nonneg_right hdK (sq_nonneg u)
  have hW : 0 ≤ (Work.Spaces.Wt α z θ) ^ 2 := sq_nonneg _
  calc (d * u) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      = d ^ 2 * u ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ K * u ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hmain hW
    _ = K * (u * Work.Spaces.Wt α z θ) ^ 2 := by ring

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le_radial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

/-- **An angular derivative divisible by `sin 2θ` costs nothing against the radial weight.**
PLACEMENT: file `Submission/Work/FTS/EllipticEst/Blocks/angular_sq_mul_Wt_sq_le_radial.lean`,
namespace `Work.FTS.EllipticEst.Blocks`, so the fully qualified name is
`Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le_radial`.
If `d² ≤ K · sin(2θ)²` at `θ ∈ (0,π/2)`, `K ≥ 0` and `α ≤ 1`, then for arbitrary `u, z`
`(d·u)² · Wt(α,z,θ)² ≤ K · (u · w(z)/sin(2θ)^{η/2})²`,
where `Wt α z θ = w z · sin(2θ)^{-γ/2}`, `γ = 1 + α/10`, `η = 99/100` and
`w z = (1+z)²/z²` (`Submission/Work/Spaces/Defs.lean`).
Route: `Wt² = w²·sin(2θ)^{-γ}`, so after cancelling `w²u²` it suffices to show
`sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}`, i.e. `sin(2θ)^{2-γ+η} ≤ 1`, which holds because
`2 - γ + η ≥ 2 - 11/10 + 99/100 > 0` and `0 < sin(2θ) ≤ 1`. -/
theorem angular_sq_mul_Wt_sq_le_radial {K d u α z θ : ℝ} (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hd : d ^ 2 ≤ K * (Real.sin (2 * θ)) ^ 2) :
    (d * u) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      ≤ K * (u * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  set S := Real.sin (2 * θ) with hS
  -- `S = sin(2θ)` lies in `(0,1]` on the open quadrant.
  have hspos : 0 < S := by
    rw [hS]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsle1 : S ≤ 1 := by rw [hS]; exact Real.sin_le_one _
  have hsnn : 0 ≤ S := le_of_lt hspos
  -- `(S^a)^2 = S^(2a)`: the key `rpow` identity, valid since `S > 0`.
  have hsq : ∀ a : ℝ, (S ^ a) ^ 2 = S ^ (a * 2) := by
    intro a
    rw [pow_two, ← Real.rpow_add hspos]
    congr 1
    ring
  have hgam : (S ^ (-(Work.Spaces.gam α / 2))) ^ 2 = S ^ (-(Work.Spaces.gam α)) := by
    rw [hsq]; congr 1; ring
  have heta : (S ^ (-(Work.Spaces.eta / 2))) ^ 2 = S ^ (-(Work.Spaces.eta)) := by
    rw [hsq]; congr 1; ring
  -- The two sides in explicit form.
  have hWt2 : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hS, mul_pow, hgam]
  have hR2 : (u * (Work.Spaces.w z / S ^ (Work.Spaces.eta / 2))) ^ 2
      = u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.eta))) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hsnn, mul_pow, mul_pow, heta]
  have hL : (d * u) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      = d ^ 2 * u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α))) := by
    rw [mul_pow, hWt2]
  -- The core estimate.
  have hmain : d ^ 2 * u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)))
      ≤ K * (u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.eta)))) := by
    have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
    have hA : 0 ≤ (Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsnn _)
    have hc : 0 ≤ u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α))) :=
      mul_nonneg hu2 hA
    -- combine the two `rpow`s
    have hcomb : S ^ 2 * S ^ (-(Work.Spaces.gam α)) = S ^ (2 - Work.Spaces.gam α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hspos]
      congr 1
    -- the numerical exponent comparison `-η ≤ 2 - γ`
    have hexp : -(Work.Spaces.eta) ≤ 2 - Work.Spaces.gam α := by
      rw [Work.Spaces.eta, Work.Spaces.gam]; linarith
    have hSS : S ^ (2 - Work.Spaces.gam α) ≤ S ^ (-(Work.Spaces.eta)) :=
      Real.rpow_le_rpow_of_exponent_ge hspos hsle1 hexp
    have hcoef : 0 ≤ K * u ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (mul_nonneg hK hu2) (sq_nonneg _)
    calc d ^ 2 * u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)))
        = d ^ 2 * (u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)))) := by
          ring
      _ ≤ (K * S ^ 2) * (u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α)))) :=
          mul_le_mul_of_nonneg_right hd hc
      _ = K * u ^ 2 * (Work.Spaces.w z) ^ 2 * (S ^ 2 * S ^ (-(Work.Spaces.gam α))) := by
          ring
      _ = K * u ^ 2 * (Work.Spaces.w z) ^ 2 * S ^ (2 - Work.Spaces.gam α) := by rw [hcomb]
      _ ≤ K * u ^ 2 * (Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left hSS hcoef
      _ = K * (u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.eta)))) := by ring
  calc (d * u) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      = d ^ 2 * u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.gam α))) := hL
    _ ≤ K * (u ^ 2 * ((Work.Spaces.w z) ^ 2 * S ^ (-(Work.Spaces.eta)))) := hmain
    _ = K * (u * (Work.Spaces.w z / S ^ (Work.Spaces.eta / 2))) ^ 2 := by rw [hR2]

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.HasFiniteIntegralWInvSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

set_option autoImplicit false

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
def sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The angular weight with exponent `-(1+η)`: `sin(2θ)^{-(1+η)}`. -/
def sig1 (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))

/-- The angular weight with exponent `-(2+η)`: `sin(2θ)^{-(2+η)}`. -/
def sig2 (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))

/-- The boundary function `Phi f θ = σ θ * f θ * f' θ - cos(2θ) * sin(2θ)^{-(1+η)} * f θ^2`. -/
def Phi (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  sig θ * (f θ * deriv f θ) - Real.cos (2 * θ) * sig1 θ * (f θ) ^ 2

/-- The (nonnegative) bulk term `Psi f`. -/
def Psi (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  2 * sig θ * (f θ) ^ 2
    + (1 - Work.Spaces.eta ^ 2) * (Real.cos (2 * θ)) ^ 2 * sig2 θ * (f θ) ^ 2
    + sig2 θ * (deriv f θ * Real.sin (2 * θ) - (1 + Work.Spaces.eta) * Real.cos (2 * θ) * f θ) ^ 2


/-- `J θ = f θ^2 / sin(2θ)`. -/
def Jfun (f : ℝ → ℝ) (θ : ℝ) : ℝ := (f θ) ^ 2 / Real.sin (2 * θ)

theorem sig_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sig θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2]
  exact Real.rpow_pos_of_pos hs _


theorem sig2_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sig2 θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2]
  exact Real.rpow_pos_of_pos hs _

theorem one_sub_eta_sq_pos : (0 : ℝ) < 1 - Work.Spaces.eta ^ 2 := by
  rw [Work.Spaces.eta]; norm_num

theorem Psi_nonneg {f : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Psi f θ := by
  have h2 : (0:ℝ) < 1 - Work.Spaces.eta ^ 2 := one_sub_eta_sq_pos
  have h3 : (0:ℝ) < sig θ := sig_pos hθ
  have h4 : (0:ℝ) < sig2 θ := sig2_pos hθ
  have h5 : (0:ℝ) ≤ (f θ) ^ 2 := sq_nonneg _
  have h6 : (0:ℝ) ≤ (Real.cos (2 * θ)) ^ 2 := sq_nonneg _
  have h7 : (0:ℝ) ≤ (deriv f θ * Real.sin (2 * θ)
      - (1 + Work.Spaces.eta) * Real.cos (2 * θ) * f θ) ^ 2 := sq_nonneg _
  have hA : (0:ℝ) ≤ 2 * sig θ * (f θ) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt h3)) h5
  have hB : (0:ℝ) ≤ (1 - Work.Spaces.eta ^ 2) * (Real.cos (2 * θ)) ^ 2 * sig2 θ * (f θ) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt h2) h6) (le_of_lt h4)) h5
  have hC : (0:ℝ) ≤ sig2 θ * (deriv f θ * Real.sin (2 * θ)
      - (1 + Work.Spaces.eta) * Real.cos (2 * θ) * f θ) ^ 2 := mul_nonneg (le_of_lt h4) h7
  simp only [Psi]
  exact add_nonneg (add_nonneg hA hB) hC

end Work.FTS.EllipticEst.Cores.AeStep2Aux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.flux_mirror_symmetry =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Dispatch

open MeasureTheory Set Filter






end Work.FTS.EllipticEst.Dispatch
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzAmgm.OfRealIntervalIntegralSqLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Cauchy–Schwarz bound `(∫_a^b (b - t) f t)² ≤ ((b-a)³/3) ∫ f²`

`Work.FTS.EllipticEst.DzAmgm.OfRealIntervalIntegralSqLe`, in the `lintegral` (i.e.
unconditional, `ℝ≥0∞`-valued) form used by the sliced Agmon–Nirenberg assembly.

The proof is the sharp `L²` Cauchy–Schwarz inequality applied to the pair
`(g, f)`, `g t = b - t`, together with `∫_a^b (b - t)² dt = (b - a)³ / 3`:

`(∫_a^b g f)² ≤ (∫_a^b g²)(∫_a^b f²) = ((b-a)³/3) · ∫_a^b f²`.

No integrability of `f` is assumed: everything is phrased with `lintegral`, using
Hölder's inequality for `ℝ≥0∞`-valued functions in the `p = q = 2` case, which is
unconditional.  Bounding `|∫ (b-t) f t| ≤ ∫⁻ |(b-t) f t|` uses
`MeasureTheory.enorm_integral_le_lintegral_enorm`.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Set

namespace Work.FTS.EllipticEst.DzAmgm

/-- The plain interval integral of `t ↦ (b - t)²` over `[a, b]` equals `(b - a)³ / 3`. -/
theorem integral_sq_sub_eq (a b : ℝ) : ∫ t in a..b, (b - t) ^ 2 = (b - a) ^ 3 / 3 := by
  have h1 := intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ 2) b (a := a) (b := b)
  -- `h1 : ∫ x in a..b, (b - x)^2 = ∫ x in b - b..b - a, x^2`
  rw [h1, sub_self, integral_pow]
  norm_num

theorem OfRealIntervalIntegralSqLe {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioc a b))) :
    ENNReal.ofReal ((∫ t in a..b, (b - t) * f t) ^ 2)
      ≤ ENNReal.ofReal ((b - a) ^ 3 / 3)
        * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
  rw [intervalIntegral.integral_of_le hab]
  -- The two `L²` factors of Cauchy–Schwarz.
  set F : ℝ → ℝ≥0∞ := fun t => ‖b - t‖ₑ with hF
  set H : ℝ → ℝ≥0∞ := fun t => ‖f t‖ₑ with hH
  have hFmeas : AEMeasurable F (volume.restrict (Set.Ioc a b)) := by
    rw [hF]
    exact ((continuous_const.sub continuous_id).aemeasurable).enorm
  have hHmeas : AEMeasurable H (volume.restrict (Set.Ioc a b)) := by
    rw [hH]
    exact hf.enorm
  -- The `L²` norm of the bounded function `t ↦ b - t` is the sharp constant.
  have hF2 : ∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ) = ENNReal.ofReal ((b - a) ^ 3 / 3) := by
    have hpt : ∀ t : ℝ, (F t) ^ (2 : ℝ) = ENNReal.ofReal ((b - t) ^ 2) := by
      intro t
      simp only [hF]
      rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (abs_nonneg (b - t)) 2, sq_abs]
    simp_rw [hpt]
    have hI : IntegrableOn (fun t : ℝ => (b - t) ^ 2) (Set.Ioc a b) volume :=
      (ContinuousOn.integrableOn_compact isCompact_Icc
        ((continuous_const.sub continuous_id).pow 2).continuousOn).mono_set
        Ioc_subset_Icc_self
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun t => sq_nonneg (b - t))]
    rw [← intervalIntegral.integral_of_le hab, integral_sq_sub_eq]
  have hH2 : ∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)
      = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
    refine lintegral_congr fun t => ?_
    simp only [hH]
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg (f t)) 2, sq_abs]
  -- Cauchy–Schwarz for `ℝ≥0∞`-valued functions, `p = q = 2`.
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hCS : ∫⁻ t in Set.Ioc a b, F t * H t
      ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Ioc a b)) hpq hFmeas hHmeas
  -- Squaring Cauchy–Schwarz.
  have hrpow : ((∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ)
      = (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      ← ENNReal.rpow_mul,
      show (1 : ℝ) / 2 * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hCSsq : (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ)
      ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ))
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := by
    have h2 := ENNReal.rpow_le_rpow hCS (show (0 : ℝ) ≤ 2 by norm_num)
    rwa [hrpow] at h2
  -- Bound the absolute value of the integral by the `lintegral` of the product.
  have hInt : ENNReal.ofReal |∫ t in Set.Ioc a b, (b - t) * f t|
      ≤ ∫⁻ t in Set.Ioc a b, F t * H t := by
    have h1 : ‖∫ t in Set.Ioc a b, (b - t) * f t‖ₑ
        ≤ ∫⁻ t in Set.Ioc a b, ‖(b - t) * f t‖ₑ :=
      enorm_integral_le_lintegral_enorm (fun t => (b - t) * f t)
    rw [Real.enorm_eq_ofReal_abs] at h1
    refine h1.trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg (b - t))]
    simp only [hF, hH, Real.enorm_eq_ofReal_abs]
  have hleft : ENNReal.ofReal ((∫ t in Set.Ioc a b, (b - t) * f t) ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ) := by
    have h1 : ENNReal.ofReal ((∫ t in Set.Ioc a b, (b - t) * f t) ^ 2)
        = (ENNReal.ofReal |∫ t in Set.Ioc a b, (b - t) * f t|) ^ 2 := by
      rw [← sq_abs (∫ t in Set.Ioc a b, (b - t) * f t)]
      exact ENNReal.ofReal_pow (abs_nonneg _) 2
    rw [h1, ← ENNReal.rpow_two]
    exact ENNReal.rpow_le_rpow hInt (show (0 : ℝ) ≤ 2 by norm_num)
  calc ENNReal.ofReal ((∫ t in Set.Ioc a b, (b - t) * f t) ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ) := hleft
    _ ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ))
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := hCSsq
    _ = ENNReal.ofReal ((b - a) ^ 3 / 3) * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
        rw [hF2, hH2]

end Work.FTS.EllipticEst.DzAmgm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.DzAmgm.SliceTaylorIdentity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false

/-- **Taylor's formula with integral remainder, in dimension one, solved for the first
derivative.**  If `g` is `C²` on `(0,∞)`, `a > 0` and `δ > 0`, then

`∫_0^δ (δ - t) g''(a + t) dt = g (a + δ) - g a - δ g'(a)`,

an identity about an *open* condition: the hypotheses only require the `C²` behaviour of `g`
near the points of the segment `[a, a+δ]`, all of which are `> 0`. -/
theorem taylorIntegralRemainder_two {g : ℝ → ℝ} {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hg : ContDiffOn ℝ 2 g (Set.Ioi 0)) :
    ∫ t in (0 : ℝ)..δ, (δ - t) * deriv (deriv g) (a + t)
      = g (a + δ) - g a - δ * deriv g a := by
  have hle : a ≤ a + δ := by linarith
  -- `g` is `C²` at every point of the segment `[a, a+δ]`, since all are `> 0`.
  have hca : ∀ s ∈ Set.uIcc a (a + δ), ContDiffAt ℝ 2 g s := by
    intro s hs
    have hs' : 0 < s := by
      rw [Set.uIcc_of_le hle, Set.mem_Icc] at hs
      linarith [hs.1]
    exact hg.contDiffAt (isOpen_Ioi.mem_nhds hs')
  -- Change of variable `s = a + t`.
  have hstep1 : ∫ t in (0 : ℝ)..δ, (δ - t) * deriv (deriv g) (a + t)
      = ∫ s in a..a + δ, (a + δ - s) * deriv (deriv g) s := by
    have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := δ)
      (fun s : ℝ => (a + δ - s) * deriv (deriv g) s) a
    have h' : ∫ t in (0 : ℝ)..δ, (a + δ - (a + t)) * deriv (deriv g) (a + t)
        = ∫ s in a..a + δ, (a + δ - s) * deriv (deriv g) s := by
      simpa using h
    rw [← h']
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hstep1]
  -- The fundamental theorem of calculus applied to
  -- `s ↦ (a + δ - s) * g'(s) + g(s)`, whose derivative is `(a + δ - s) * g''(s)`.
  have hH : ∀ s ∈ Set.uIcc a (a + δ),
      HasDerivAt (fun s : ℝ => (a + δ - s) * deriv g s + g s)
        ((a + δ - s) * deriv (deriv g) s) s := by
    intro s hs
    have h2 : ContDiffAt ℝ 2 g s := hca s hs
    have h1 : ContDiffAt ℝ 1 (deriv g) s := h2.derivWithin (m := 1) (by norm_num)
    have hd2 : HasDerivAt (deriv g) (deriv (deriv g) s) s :=
      (h1.hasStrictDerivAt (by norm_num)).hasDerivAt
    have hd0 : HasDerivAt g (deriv g s) s := (h2.differentiableAt (by norm_num)).hasDerivAt
    have hd1 : HasDerivAt (fun s : ℝ => a + δ - s) (-1) s := by
      have h : HasDerivAt (fun s : ℝ => a + δ - s) (0 - 1) s :=
        (hasDerivAt_const s (a + δ)).sub (hasDerivAt_id s)
      simpa using h
    have h := (hd1.mul hd2).add hd0
    have hA : (-1 * deriv g s + (a + δ - s) * deriv (deriv g) s + deriv g s)
        = (a + δ - s) * deriv (deriv g) s := by ring
    rw [hA] at h
    exact h
  have hint : IntervalIntegrable (fun s : ℝ => (a + δ - s) * deriv (deriv g) s)
      MeasureTheory.volume a (a + δ) := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have h2 : ContDiffAt ℝ 2 g s := hca s hs
    have h1 : ContDiffAt ℝ 1 (deriv g) s := h2.derivWithin (m := 1) (by norm_num)
    have h0 : ContinuousAt (deriv (deriv g)) s :=
      (h1.derivWithin (m := 0) (by norm_num)).continuousAt
    exact ((continuous_const.sub continuous_id).continuousAt.mul h0).continuousWithinAt
  have hFTC : ∫ y in a..a + δ, (a + δ - y) * deriv (deriv g) y
      = (a + δ - (a + δ)) * deriv g (a + δ) + g (a + δ)
          - ((a + δ - a) * deriv g a + g a) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hH hint
    simpa using h
  rw [hFTC]
  ring

/-- **The slice Taylor identity.**  For `V` of class `C²` on the open quadrant, `z₀ > 0`,
`δ > 0` and `θ ∈ (0,π/2)`,

`∂_z V (z₀,θ) = δ⁻¹ * (V (z₀+δ,θ) - V (z₀,θ) - ∫_0^δ (δ-t) ∂_z²V (z₀+t,θ) dt)`.

This is Taylor's formula with integral remainder for the slice `z ↦ V z θ`, solved for the
first derivative: it expresses `∂_z` as a finite difference of `V` plus the second derivative,
which is exactly the form used to interpolate `D_z` against `z² ∂_z²` in the radial
Agmon–Nirenberg estimate. -/
theorem SliceTaylorIdentity (V : ℝ → ℝ → ℝ)
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z₀ δ θ : ℝ} (hz₀ : 0 < z₀) (hδ : 0 < δ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz V z₀ θ
      = δ⁻¹ * (V (z₀ + δ) θ - V z₀ θ
          - ∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ) := by
  -- The `θ`-slice of a `C²` function on the quadrant is `C²` on `(0,∞)`.
  have hslice : ContDiffOn ℝ 2 (fun z => V z θ) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (z, θ)) (Set.Ioi 0) := by fun_prop
    exact hV.comp h1 (by intro z hz; exact ⟨hz, hθ⟩)
  have hkey := taylorIntegralRemainder_two hz₀ hδ hslice
  have hpz : Work.Spaces.pz V z₀ θ = deriv (fun z => V z θ) z₀ := rfl
  -- `pzIter 2 V z θ` is `deriv (deriv (fun z => V z θ)) z` by definition.
  have hint : ∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ
      = ∫ t in (0 : ℝ)..δ, (δ - t) * deriv (deriv (fun z => V z θ)) (z₀ + t) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  rw [hpz, hint, hkey]
  field_simp
  ring

end Work.FTS.EllipticEst.DzAmgm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Level0ADefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-- The `A`-datum: `A Ψ = z² ∂_z² Ψ` (the twice radially differentiated datum). -/
abbrev Aof (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- The source of the `A`-datum: `G F = D_z² F − D_z F = z² ∂_z² F`. -/
abbrev Gof (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ

@[simp] theorem Aof_apply (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Aof Ψ z θ = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := rfl

@[simp] theorem Gof_apply (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Gof F z θ = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := rfl

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SlotA.radialDerivPointwiseOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise radial product rule for the open half-strip `(0,∞) × (0,π/2)`

This is the *weak-class* version of `Work.FTS.EllipticEst.H2W.radial_deriv_pointwise`:
the smoothness hypothesis is `C³` on the **open** half-strip `Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)`
(only the open quadrant, as in the almost-everywhere class `H2W.Ae.AeData`) instead of on the
neighbourhood `Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2+1)`.

For a function `Φ` of class `C³` on the open half-strip, at a point `(z,θ)` with `z > 0` and
`θ ∈ (0,π/2)`,

`deriv (fun z' => (z'^2 · ∂_zΦ(z',θ) · w(z')^2) · ∂_θ²Φ(z',θ)) z`
equals the four-term product rule expansion.

The proof is the one of the sibling file, with the two open sets replaced: the `θ`-slice
`z' ↦ Φ z' θ` is `C³` on `(0,∞)` because `Φ` is (`hsm.comp` with the embedding `z' ↦ (z',θ)`,
which lands in the open half-strip since `θ ∈ (0,π/2)`), and the curried `θ`-partials are
smooth in the pair by `ContDiffOn.fderiv_of_isOpen` — this needs only that the strip is open.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The open half-strip `(0,∞) × (0,π/2)`. -/
abbrev qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_qd : IsOpen qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## Two-variable calculus: slices and the curried partials -/

/-- The `z`-partial is the Fréchet derivative in the direction `(1,0)`. -/
private theorem pz_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    Work.Spaces.pz G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (1, 0) := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  exact (h.hasFDerivAt.comp_hasDerivAt z hcurve).deriv

/-- The `θ`-partial is the Fréchet derivative in the direction `(0,1)`. -/
private theorem pth_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    Work.Spaces.pth G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (0, 1) := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  exact (h.hasFDerivAt.comp_hasDerivAt θ hcurve).deriv

/-- The `θ`-partial of a function that is `C^{n+1}` on an open set is `C^n` there. -/
private theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact pth_eq_fderiv ((h.differentiableOn (n := (n + 1 : ℕ)) (by simp)).differentiableAt
      (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-! ## The product rule -/


end Work.FTS.EllipticEst.H2W.SlotA
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Step5.integrable_of_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

theorem integrable_of_majorant {f M : ℝ → ℝ → ℝ}
    (hslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (houter : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hMslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f z θ)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ ≤ M z θ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ, f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- `f` is squeezed between `0` and the integrable majorant `M` on the square
  -- `Iz × Iθ`, hence every `θ`-slice of `f` is integrable on `Iθ` ...
  have hsliceInt : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ := by
    intro z hz
    refine (hMslice z hz).mono' (hslice z hz) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ] with θ hθ
    have h1 : 0 ≤ f z θ := hnn z hz θ hθ
    have h2 : f z θ ≤ M z θ := hle z hz θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact h2
  -- ... and the `z`-function `∫ θ, f z θ` is squeezed between `0` and the
  -- integrable function `z ↦ ∫ θ, M z θ` on `Iz`.
  refine ⟨hsliceInt, ?_⟩
  refine hMz.mono' houter ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hz
  have hfi : MeasureTheory.IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ := hsliceInt z hz
  have hMi : MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ := hMslice z hz
  have hnnI : 0 ≤ ∫ θ in Work.Spaces.Iθ, f z θ :=
    MeasureTheory.setIntegral_nonneg hIθ (fun θ hθ => hnn z hz θ hθ)
  have hmono : ∫ θ in Work.Spaces.Iθ, f z θ ≤ ∫ θ in Work.Spaces.Iθ, M z θ :=
    MeasureTheory.setIntegral_mono_on hfi hMi hIθ (fun θ hθ => hle z hz θ hθ)
  rw [Real.norm_eq_abs, abs_of_nonneg hnnI]
  exact hmono

end Work.FTS.EllipticEst.H2W.Step5
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.powToolkit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

/-! ### Helpers for `powToolkit`

The eight conjuncts are

* two trigonometric comparisons on `(0, π/4]` resp. `[π/4, π/2)`, proved in the sibling modules
  `Work.FTS.EllipticEst.H2W.WeakPureAux.PowToolkitPieces.trigLeft` / `.trigRight` from Jordan's
  inequality `Real.mul_le_sin` (`2x/π ≤ sin x` for `x ∈ [0, π/2]`), with the exact constants
  `π²/8` and `π³/32`;
* six antiderivative evaluations, proved below from `integral_rpow` (together with the
  substitution `u = π/2 - s` in the last three). -/













end Work.FTS.EllipticEst.H2W.WeakPureAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.sharpHardyDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W



end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.sinRpowWeightDerivs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open Filter Set
open scoped Topology

namespace SinRpowWeight

/-! ## One-sided behaviour of `sin` at `0` and at the zeros of `sin (2·)` -/





/-! ## Non-differentiability at the zeros of `sin (2·)` -/





/-! ## The derivatives away from the zeros of `sin (2·)` -/




end SinRpowWeight


end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.sliceSigmaPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise `σ`-weighted slice identity (`sliceSigmaPointwise`)

Fix `η = Work.Spaces.eta` and write `a = (1+η)/2`, `S = sin(2θ)`, `C = cos(2θ)`,
`U = u θ`, `D = deriv u θ`.  For any `u` differentiable at the interior point
`θ ∈ (0, π/2)` one has the pointwise identity

  `D² S^{-η} - 4 a² U² S^{-(2+η)} = (∂_θ(u S^{-a}))² S^{2a-η} + ∂_θ(2a cos(2θ) U² S^{-(1+η)})
      + 4 a (1-a) U² S^{-η}`.

The identity is the pointwise form of `sliceSigmaSubinterval` (Elgindi's `§H2` weighted
angular Hardy/coercivity estimate): integrating it over `[a,b] ⊆ (0,π/2)` and using
`2a - η = 1`, `C² + S² = 1`, the total derivative in the middle integrates to the boundary
difference of `2a cos(2θ) u² sin(2θ)^{-(1+η)}` and the first term is a square, so the
difference of the first two terms of the left hand side is controlled by the right hand side.

## Proof

The two `deriv`s are computed with `HasDerivAt` (`Real.hasDerivAt_rpow_const` for the
`rpow` factor, the product rule for the products), and the resulting identity is the
algebraic lemma `sliceSigma_alg`, obtained by multiplying with `S^{2+η} ≠ 0` and reducing
every product `S^r · S^s` to `S^{r+s}` (`Real.rpow_add`); after that all `S`-powers combine
to `S^0, S^1, S^2` and the remaining ring identity is exactly `C² + S² = 1` together with
`2a = 1+η`.
-/

namespace Work.FTS.EllipticEst.H2W

/-- Pure algebra behind `sliceSigmaPointwise`, for positive `S` with `C²+S² = 1` and
`2a = 1+η`.  It is the statement obtained after substituting the two derivatives. -/
private lemma sliceSigma_alg {S C D U a η : ℝ} (hS : 0 < S) (hcs : C ^ 2 + S ^ 2 = 1)
    (ha : 2 * a = 1 + η) :
    D ^ 2 * S ^ (-η) - 4 * a ^ 2 * U ^ 2 * S ^ (-(2 + η))
      = (D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η)
        + (-4 * a * S * U ^ 2 * S ^ (-(1 + η)) + 4 * a * C * U * D * S ^ (-(1 + η))
            - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * S ^ (-(2 + η)))
        + 4 * a * (1 - a) * U ^ 2 * S ^ (-η) := by
  -- `S^r · S^s = S^(r+s)` for positive `S`.
  have hprod : ∀ r s t : ℝ, r + s = t → S ^ r * S ^ s = S ^ t :=
    fun r s t h => by rw [← Real.rpow_add hS, h]
  have e1 : S ^ (-η) * S ^ (2 + η) = S ^ 2 := by
    rw [hprod (-η) (2 + η) (2 : ℝ) (by ring), Real.rpow_two]
  have e2 : S ^ (-(2 + η)) * S ^ (2 + η) = 1 := by
    rw [hprod (-(2 + η)) (2 + η) (0 : ℝ) (by ring), Real.rpow_zero]
  have e3 : S ^ (-(1 + η)) * S ^ (2 + η) = S := by
    rw [hprod (-(1 + η)) (2 + η) (1 : ℝ) (by ring), Real.rpow_one]
  -- factor the bracket of the square
  have hfac : D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)
      = S ^ (-a - 1) * (D * S - 2 * a * C * U) := by
    have h : S ^ (-a - 1) * S ^ (1 : ℝ) = S ^ (-a) := hprod (-a - 1) 1 (-a) (by ring)
    rw [Real.rpow_one] at h
    calc D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)
        = D * (S ^ (-a - 1) * S) - 2 * a * C * U * S ^ (-a - 1) := by rw [h]
      _ = S ^ (-a - 1) * (D * S - 2 * a * C * U) := by ring
  have hsq : (S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η) = S ^ (-(2 + η)) := by
    have h2 : S ^ (-a - 1) * S ^ (-a - 1) = S ^ (-2 * a - 2) :=
      hprod (-a - 1) (-a - 1) (-2 * a - 2) (by ring)
    calc (S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η)
        = (S ^ (-a - 1) * S ^ (-a - 1)) * S ^ (2 * a - η) := by ring
      _ = S ^ (-2 * a - 2) * S ^ (2 * a - η) := by rw [h2]
      _ = S ^ (-(2 + η)) := by rw [hprod (-2 * a - 2) (2 * a - η) (-(2 + η)) (by ring)]
  have ht1 : S ^ (2 + η) * ((D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η))
      = (D * S - 2 * a * C * U) ^ 2 := by
    rw [hfac]
    calc S ^ (2 + η) * ((S ^ (-a - 1) * (D * S - 2 * a * C * U)) ^ 2 * S ^ (2 * a - η))
        = (D * S - 2 * a * C * U) ^ 2
            * ((S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η) * S ^ (2 + η)) := by ring
      _ = (D * S - 2 * a * C * U) ^ 2 * (S ^ (-(2 + η)) * S ^ (2 + η)) := by rw [hsq]
      _ = (D * S - 2 * a * C * U) ^ 2 * 1 := by rw [e2]
      _ = (D * S - 2 * a * C * U) ^ 2 := by ring
  have ht2 : S ^ (2 + η) * (-4 * a * S * U ^ 2 * S ^ (-(1 + η)) + 4 * a * C * U * D * S ^ (-(1 + η))
          - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * S ^ (-(2 + η)))
      = -4 * a * S * U ^ 2 * S + 4 * a * C * U * D * S - 4 * a * (1 + η) * C ^ 2 * U ^ 2 := by
    calc S ^ (2 + η) * (-4 * a * S * U ^ 2 * S ^ (-(1 + η)) + 4 * a * C * U * D * S ^ (-(1 + η))
          - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * S ^ (-(2 + η)))
        = -4 * a * S * U ^ 2 * (S ^ (-(1 + η)) * S ^ (2 + η))
            + 4 * a * C * U * D * (S ^ (-(1 + η)) * S ^ (2 + η))
            - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * (S ^ (-(2 + η)) * S ^ (2 + η)) := by ring
      _ = -4 * a * S * U ^ 2 * S + 4 * a * C * U * D * S - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * 1 :=
            by rw [e3, e2]
      _ = -4 * a * S * U ^ 2 * S + 4 * a * C * U * D * S - 4 * a * (1 + η) * C ^ 2 * U ^ 2 := by ring
  have ht3 : S ^ (2 + η) * (4 * a * (1 - a) * U ^ 2 * S ^ (-η))
      = 4 * a * (1 - a) * U ^ 2 * S ^ 2 := by
    calc S ^ (2 + η) * (4 * a * (1 - a) * U ^ 2 * S ^ (-η))
        = 4 * a * (1 - a) * U ^ 2 * (S ^ (-η) * S ^ (2 + η)) := by ring
      _ = 4 * a * (1 - a) * U ^ 2 * S ^ 2 := by rw [e1]
  have hL : S ^ (2 + η) * (D ^ 2 * S ^ (-η) - 4 * a ^ 2 * U ^ 2 * S ^ (-(2 + η)))
      = D ^ 2 * S ^ 2 - 4 * a ^ 2 * U ^ 2 := by
    calc S ^ (2 + η) * (D ^ 2 * S ^ (-η) - 4 * a ^ 2 * U ^ 2 * S ^ (-(2 + η)))
        = D ^ 2 * (S ^ (-η) * S ^ (2 + η))
            - 4 * a ^ 2 * U ^ 2 * (S ^ (-(2 + η)) * S ^ (2 + η)) := by ring
      _ = D ^ 2 * S ^ 2 - 4 * a ^ 2 * U ^ 2 * 1 := by rw [e1, e2]
      _ = D ^ 2 * S ^ 2 - 4 * a ^ 2 * U ^ 2 := by ring
  -- multiply by the positive factor `S^(2+η)` and cancel it
  apply mul_left_cancel₀ (a := S ^ (2 + η)) (ne_of_gt (Real.rpow_pos_of_pos hS (2 + η)))
  rw [hL]
  rw [show S ^ (2 + η) * ((D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η)
        + (-4 * a * S * U ^ 2 * S ^ (-(1 + η)) + 4 * a * C * U * D * S ^ (-(1 + η))
            - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * S ^ (-(2 + η)))
        + 4 * a * (1 - a) * U ^ 2 * S ^ (-η))
      = S ^ (2 + η) * ((D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)) ^ 2 * S ^ (2 * a - η))
        + S ^ (2 + η) * (-4 * a * S * U ^ 2 * S ^ (-(1 + η)) + 4 * a * C * U * D * S ^ (-(1 + η))
            - 4 * a * (1 + η) * C ^ 2 * U ^ 2 * S ^ (-(2 + η)))
        + S ^ (2 + η) * (4 * a * (1 - a) * U ^ 2 * S ^ (-η)) from by ring]
  rw [ht1, ht2, ht3]
  -- the remaining identity is `C² + S² = 1` and `2a = 1 + η`
  rw [show (1 + η) = 2 * a by linarith]
  linear_combination (4 * a ^ 2 * U ^ 2) * hcs

theorem sliceSigmaPointwise {u : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : DifferentiableAt ℝ u θ) :
    (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      - 4 * ((1 + Work.Spaces.eta) / 2) ^ 2 * (u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
    = (deriv (fun θ' : ℝ => u θ' * (Real.sin (2 * θ')) ^ (-((1 + Work.Spaces.eta) / 2))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * ((1 + Work.Spaces.eta) / 2) - Work.Spaces.eta)
      + deriv (fun θ' : ℝ => 2 * ((1 + Work.Spaces.eta) / 2) * Real.cos (2 * θ') * (u θ') ^ 2
            * (Real.sin (2 * θ')) ^ (-(1 + Work.Spaces.eta))) θ
      + 4 * ((1 + Work.Spaces.eta) / 2) * (1 - (1 + Work.Spaces.eta) / 2) * (u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  set a : ℝ := (1 + Work.Spaces.eta) / 2 with ha_def
  set S : ℝ := Real.sin (2 * θ) with hS_def
  set C : ℝ := Real.cos (2 * θ) with hC_def
  set D : ℝ := deriv u θ with hD_def
  set U : ℝ := u θ with hU_def
  have hSpos : 0 < S := by
    rw [hS_def]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hSne : S ≠ 0 := ne_of_gt hSpos
  have hcs : C ^ 2 + S ^ 2 = 1 := by
    rw [hC_def, hS_def]
    exact Real.cos_sq_add_sin_sq (2 * θ)
  have hint : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * C) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ hint
    refine h.congr_deriv ?_
    rw [hC_def]; ring
  have hcos : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-2 * S) θ := by
    have h := (Real.hasDerivAt_cos (2 * θ)).comp θ hint
    refine h.congr_deriv ?_
    rw [hS_def]; ring
  have hpow1 : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ (-a))
      (-a * S ^ (-a - 1) * (2 * C)) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := S) (p := -a) (Or.inl hSne)).comp θ hsin
    refine h.congr_deriv ?_
    ring
  have hd1 : HasDerivAt (fun θ' : ℝ => u θ' * (Real.sin (2 * θ')) ^ (-a))
      (D * S ^ (-a) - 2 * a * C * U * S ^ (-a - 1)) θ := by
    have h := hu.hasDerivAt.mul hpow1
    refine h.congr_deriv ?_
    rw [hD_def, hU_def]; ring
  have hu2 : HasDerivAt (fun θ' : ℝ => (u θ') ^ 2) (2 * U * D) θ := by
    have h := hu.hasDerivAt.pow 2
    have hd : (↑2 * u θ ^ (2 - 1) * deriv u θ : ℝ) = 2 * U * D := by
      rw [hU_def, hD_def]; norm_num
    exact h.congr_deriv hd
  have hpow2 : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ (-(1 + Work.Spaces.eta)))
      (-(1 + Work.Spaces.eta) * S ^ (-(1 + Work.Spaces.eta) - 1) * (2 * C)) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := S) (p := -(1 + Work.Spaces.eta))
      (Or.inl hSne)).comp θ hsin
    refine h.congr_deriv ?_
    ring
  have hd2 : HasDerivAt (fun θ' : ℝ => 2 * a * Real.cos (2 * θ') * (u θ') ^ 2
        * (Real.sin (2 * θ')) ^ (-(1 + Work.Spaces.eta)))
      (-4 * a * S * U ^ 2 * S ^ (-(1 + Work.Spaces.eta)) + 4 * a * C * U * D * S ^ (-(1 + Work.Spaces.eta))
        - 4 * a * (1 + Work.Spaces.eta) * C ^ 2 * U ^ 2 * S ^ (-(2 + Work.Spaces.eta))) θ := by
    have h := (((hasDerivAt_const θ (2 * a)).mul hcos).mul hu2).mul hpow2
    refine h.congr_deriv ?_
    rw [hU_def, hD_def, hC_def, hS_def]
    simp only [Pi.mul_apply]
    ring_nf
  rw [hd1.deriv, hd2.deriv]
  refine sliceSigma_alg hSpos hcs ?_
  rw [ha_def]; ring

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HkIntegrand_le_slice_sum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Index bookkeeping for the `H^k`-integrand

The second sum of `Work.Spaces.HkIntegrand α k f z θ` runs over the pairs `(i,j)` with
`0 ≤ i, j ≤ k` and carries the indicator `if 1 ≤ i ∧ i + j ≤ k then · else 0`.  For fixed `j`
this indicator selects exactly the index set `Finset.Icc 1 (k - j)` (truncated subtraction: for
`j > k` both sets are empty), which is the `θ`-slice index set of the stated right-hand side. -/

/-- For all `i j k : ℕ`, the `i ∈ {0,…,k}` with `1 ≤ i` and `i + j ≤ k` are exactly the
integers in `Icc 1 (k - j)`. -/
lemma filter_range_succ_eq_Icc (k j : ℕ) :
    (Finset.range (k + 1)).filter (fun i => 1 ≤ i ∧ i + j ≤ k) = Finset.Icc 1 (k - j) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

/-- The `if`-sum over `i ∈ range (k+1)` with indicator `1 ≤ i ∧ i + j ≤ k` is the sum over the
slice index set `Icc 1 (k-j)`. -/
lemma sum_range_ite_eq_sum_Icc (k j : ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i + j ≤ k then c i else 0))
      = ∑ i ∈ Finset.Icc 1 (k - j), c i := by
  rw [← Finset.sum_filter]
  congr 1
  exact filter_range_succ_eq_Icc k j


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HkNorm_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

open Work.Spaces

/-! ## Scalar homogeneity of the differential operators -/

private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    pz (fun z θ => c * f z θ) = fun z θ => c * pz f z θ := by
  funext z θ
  simp only [pz]
  exact deriv_const_mul_field c

private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    pth (fun z θ => c * f z θ) = fun z θ => c * pth f z θ := by
  funext z θ
  simp only [pth]
  exact deriv_const_mul_field c

private theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Dz (fun z θ => c * f z θ) = fun z θ => c * Dz f z θ := by
  funext z θ
  simp only [Dz, pz_const_mul]
  ring

private theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Dth (fun z θ => c * f z θ) = fun z θ => c * Dth f z θ := by
  funext z θ
  simp only [Dth, pth_const_mul]
  ring

private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    DzIter n (fun z θ => c * f z θ) = fun z θ => c * DzIter n f z θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Dz (DzIter n (fun z θ => c * f z θ)) = fun z θ => c * Dz (DzIter n f) z θ
    rw [ih]
    funext z θ
    simp only [Dz, pz_const_mul]
    ring

private theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    DthIter n (fun z θ => c * f z θ) = fun z θ => c * DthIter n f z θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Dth (DthIter n (fun z θ => c * f z θ)) = fun z θ => c * Dth (DthIter n f) z θ
    rw [ih]
    funext z θ
    simp only [Dth, pth_const_mul]
    ring

private theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    mixed j i (fun z θ => c * f z θ) = fun z θ => c * mixed j i f z θ := by
  show DzIter j (DthIter i (fun z θ => c * f z θ))
    = fun z θ => c * DzIter j (DthIter i f) z θ
  rw [DthIter_const_mul, DzIter_const_mul]

/-! ## Homogeneity of the integrand and of the squared norm -/

/-- The weighted `H^k`-integrand is homogeneous of degree `2` in the amplitude. -/
private theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkIntegrand α k (fun z θ => c * f z θ) z θ = c ^ 2 * HkIntegrand α k f z θ := by
  unfold HkIntegrand
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [DzIter_const_mul]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mixed_const_mul]
    split_ifs <;> ring

/-- The squared `H^k`-norm is homogeneous of degree `2` in the amplitude. -/
private theorem HkSq_const_mul_prv (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    HkSq α k (fun z θ => c * f z θ) = c ^ 2 * HkSq α k f := by
  unfold HkSq
  simp only [HkIntegrand_const_mul]
  have hinner : ∀ z, (∫ θ in Iθ, c ^ 2 * HkIntegrand α k f z θ)
      = c ^ 2 * ∫ θ in Iθ, HkIntegrand α k f z θ :=
    fun z => integral_const_mul _ _
  simp only [hinner]
  rw [integral_const_mul]

/-! ## The `H^k`-norm is absolutely homogeneous -/

set_option linter.unusedVariables false in
theorem HkNorm_const_mul (α : ℝ) (k : ℕ) (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Work.Spaces.HkNorm α k (fun z θ => c * f z θ) = |c| * Work.Spaces.HkNorm α k f := by
  unfold HkNorm
  rw [HkSq_const_mul_prv]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HkSq_congr_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllipticEst

/-- `F` and `G` agree on the open quadrant `(0,∞) × (0,π/2)`. -/
def AgreeOnQ (F G : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ

/-! ## Local congruence of the partial derivatives

If two functions agree on a neighbourhood of a point, their derivatives there agree.
For our functions of two variables this reads: agreement on a neighbourhood in the `z`
variable (at fixed `θ`) gives equality of `∂_z`, and likewise in the `θ` variable. -/

lemma pz_congr_of_eventuallyEq {F G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, F z' θ = G z' θ) :
    Work.Spaces.pz F z θ = Work.Spaces.pz G z θ :=
  Filter.EventuallyEq.deriv_eq h

lemma pth_congr_of_eventuallyEq {F G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ θ' in 𝓝 θ, F z θ' = G z θ') :
    Work.Spaces.pth F z θ = Work.Spaces.pth G z θ :=
  Filter.EventuallyEq.deriv_eq h

/-! ## Agreement of the weighted derivatives on the open quadrant

The open quadrant is open, so a function that vanishes on it has all its derivatives
vanishing on it; iterating, the same is true for `D_z`, `D_θ` and all their mixed
iterates. -/

lemma AgreeOnQ.pz {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    AgreeOnQ (Work.Spaces.pz F) (Work.Spaces.pz G) := by
  intro z θ hz hθ hlt
  refine pz_congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact h z' θ hz' hθ hlt

lemma AgreeOnQ.pth {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    AgreeOnQ (Work.Spaces.pth F) (Work.Spaces.pth G) := by
  intro z θ hz hθ hlt
  refine pth_congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ hlt] with θ' hθ'
  exact h z θ' hz hθ'.1 hθ'.2

lemma AgreeOnQ.Dz {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    AgreeOnQ (Work.Spaces.Dz F) (Work.Spaces.Dz G) := by
  intro z θ hz hθ hlt
  simp only [Work.Spaces.Dz]
  rw [h.pz z θ hz hθ hlt]

lemma AgreeOnQ.Dth {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    AgreeOnQ (Work.Spaces.Dth F) (Work.Spaces.Dth G) := by
  intro z θ hz hθ hlt
  simp only [Work.Spaces.Dth]
  rw [h.pth z θ hz hθ hlt]

lemma AgreeOnQ.DthIter {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    ∀ i : ℕ, AgreeOnQ (Work.Spaces.DthIter i F) (Work.Spaces.DthIter i G) := by
  intro i
  induction i with
  | zero => exact h
  | succ i ih => exact ih.Dth

lemma AgreeOnQ.DzIter {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) :
    ∀ j : ℕ, AgreeOnQ (Work.Spaces.DzIter j F) (Work.Spaces.DzIter j G) := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih => exact ih.Dz

lemma AgreeOnQ.mixed {F G : ℝ → ℝ → ℝ} (h : AgreeOnQ F G) (j i : ℕ) :
    AgreeOnQ (Work.Spaces.mixed j i F) (Work.Spaces.mixed j i G) :=
  (h.DthIter i).DzIter j

/-! ## Equality of the `H^k` integrands on the open quadrant -/

lemma HkIntegrand_congr {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ} (h : AgreeOnQ f g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α k f z θ = Work.Spaces.HkIntegrand α k g z θ := by
  intro z θ hz hθ hlt
  simp only [Work.Spaces.HkIntegrand]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [h.DzIter i z θ hz hθ hlt]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [h.mixed j i z θ hz hθ hlt]

/-! ## The main result -/

theorem HkSq_congr_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.HkSq α k f = Work.Spaces.HkSq α k g := by
  have hI := HkIntegrand_congr (α := α) (k := k) h
  -- For each `z > 0` the two inner integrands agree off the two endpoints `θ = 0`,
  -- `θ = π/2` of `[0,π/2]`, hence the two inner integrals agree.
  have hinner : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
    intro z hz
    apply integral_congr_ae
    show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k f z θ = Work.Spaces.HkIntegrand α k g z θ
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ) ∪ {Real.pi / 2}) ?_ ?_
    · intro θ hθ
      simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Icc, Work.Spaces.Iθ,
        Set.mem_union, Set.mem_singleton_iff] at hθ ⊢
      obtain ⟨⟨h0, h1⟩, hne⟩ := hθ
      rcases eq_or_lt_of_le h0 with h0' | h0'
      · exact Or.inl h0'.symm
      · refine Or.inr ?_
        by_contra h2
        exact hne (hI z θ hz h0' (lt_of_le_of_ne h1 h2))
    · exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
        (MeasureTheory.measure_singleton (Real.pi / 2))
  -- The outer integrands then agree for every `z ∈ [0,∞)` with `z ≠ 0`.
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  apply integral_congr_ae
  show ∀ᵐ a ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f a θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g a θ
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ)) ?_
    (MeasureTheory.measure_singleton 0)
  intro z hz
  simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Ici, Work.Spaces.Iz,
    Set.mem_singleton_iff] at hz ⊢
  obtain ⟨h0, hne⟩ := hz
  by_contra h1
  exact hne (hinner z (lt_of_le_of_ne h0 (Ne.symm h1)))

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonCosSliceIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Real

namespace Work.FTS.EllipticEst.Honest


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4SliceDivIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllipticEst.Honest

/-- **The integrability hypothesis of the boundary lemma.**

Let `Φ` be of class `C²` on `(0, π/2)` with `∫_θ (Φ/cos θ)²σ` and `∫_θ (Φ'')²σ` integrable over
`[0, π/2]` (`σ = sin(2θ)^{-η}`, `η = 99/100`).  Then the quantity `(P'/cos θ)²σ`, where
`P = cos²θ·(Φ/cos θ)'`, is integrable on `(0, π/2)` — this is the third hypothesis of
`Work.FTS.EllipticEst.Honest.I4BoundaryVanish` when it is applied with `ψ := Φ/cos θ`.

Route: by the pointwise calculus identity `P' = cos θ·(Φ'' + Φ)`
(`Work.FTS.EllipticEst.I4SliceAlgebra`), the integrand equals `(Φ'' + Φ)²σ` on `(0, π/2)`, which
is dominated by `2(Φ'')²σ + 2(Φ/cos θ)²σ` (since `Φ = cos θ·(Φ/cos θ)` and `σ ≥ 0`).  Both terms
are integrable by the hypotheses, so the domination `MeasureTheory.Integrable.mono'` applies,
with `AEStronglyMeasurable (fun θ => (Φ'' θ + Φ θ)²σ)` (a.e. strong measurability of the second
derivative is `aestronglyMeasurable_deriv`, of `Φ` from continuity, of `σ` from
`ContinuousOn.rpow_const` on `(0, π/2)` where `sin 2θ ≠ 0`).  Finally transfer the integrability
to the `P'`-form by a.e. equality on `(0, π/2)`. -/
theorem I4SliceDivIntegrable (Φ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2)))
    (hB : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => (Real.cos θ') ^ 2
            * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ / Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Ioo 0 (Real.pi / 2)) := by
  have hUmeas : MeasurableSet (Set.Ioo (0:ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hcospos : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.cos θ := by
    intro θ hθ
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hsin2pos : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- the pointwise calculus identity `P' = cos θ · (Φ'' + Φ)` on `(0, π/2)`
  have hid := (Work.FTS.EllipticEst.I4SliceAlgebra Φ hsm).2.2.1
  -- the two summands, restricted from `[0, π/2]` to `(0, π/2)`
  have hA' : MeasureTheory.IntegrableOn
      (fun θ => (Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hA.mono_set Set.Ioo_subset_Icc_self
  have hB' : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hB.mono_set Set.Ioo_subset_Icc_self
  -- the dominating function
  have hbounds : MeasureTheory.IntegrableOn
      (fun θ => 2 * ((deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        + 2 * ((Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hB'.const_mul 2).add (hA'.const_mul 2)
  -- a.e. strong measurability of `(Φ'' + Φ)²σ`
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (deriv (deriv Φ) θ + Φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (deriv (deriv Φ))
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      aestronglyMeasurable_deriv (deriv Φ) _
    have h2 : MeasureTheory.AEStronglyMeasurable Φ
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      hsm.continuousOn.aestronglyMeasurable hUmeas
    have h3 : MeasureTheory.AEStronglyMeasurable
        (fun θ => (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
      apply ContinuousOn.aestronglyMeasurable _ hUmeas
      exact (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const
        (fun x hx => Or.inl (ne_of_gt (hsin2pos x hx)))
    exact ((h1.add h2).pow 2).mul h3
  -- the pointwise domination `(Φ'' + Φ)²σ ≤ 2(Φ'')²σ + 2(Φ/cos θ)²σ`
  have hdom : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ‖(deriv (deriv Φ) θ + Φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))‖
      ≤ 2 * ((deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        + 2 * ((Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) := by
    rw [MeasureTheory.ae_restrict_iff' hUmeas]
    filter_upwards with θ hθ
    have hsinn := hsin2pos θ hθ
    have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)) := Real.rpow_nonneg (le_of_lt hsinn) _
    have hcos2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
    have hcos2pos : 0 < Real.cos θ ^ 2 := pow_pos (hcospos θ hθ) 2
    have hb : Φ θ ^ 2 ≤ (Φ θ / Real.cos θ) ^ 2 := by
      have h1 : 1 ≤ 1 / Real.cos θ ^ 2 := by
        rw [le_div_iff₀ hcos2pos]; simpa using hcos2
      calc Φ θ ^ 2 = Φ θ ^ 2 * 1 := by ring
        _ ≤ Φ θ ^ 2 * (1 / Real.cos θ ^ 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = (Φ θ / Real.cos θ) ^ 2 := by rw [div_pow]; ring
    have hkey : (deriv (deriv Φ) θ + Φ θ) ^ 2
        ≤ 2 * (deriv (deriv Φ) θ) ^ 2 + 2 * (Φ θ / Real.cos θ) ^ 2 := by
      have h1 := add_sq_le (a := deriv (deriv Φ) θ) (b := Φ θ)
      nlinarith [hb]
    have hmain : (deriv (deriv Φ) θ + Φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
        ≤ 2 * ((deriv (deriv Φ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
          + 2 * ((Φ θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) := by
      nlinarith [mul_le_mul_of_nonneg_right hkey hσnn]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσnn)]
    exact hmain
  -- integrability of `(Φ'' + Φ)²σ` on `(0, π/2)`
  have hgint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv Φ) θ + Φ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' hbounds haesm hdom
  -- transfer to the `P'`-form by a.e. equality on `(0, π/2)`
  refine hgint.congr ?_
  rw [Filter.EventuallyEq]
  rw [MeasureTheory.ae_restrict_iff' hUmeas]
  filter_upwards with θ hθ
  have hne : Real.cos θ ≠ 0 := ne_of_gt (hcospos θ hθ)
  rw [hid θ hθ, mul_div_cancel_left₀ _ hne]

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SliceBoundary =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-! ## Two elementary lower bounds for `sin (2θ)` near the endpoints -/

/-- On `[0, π/4]`, `sin (2θ)` dominates `(4/π) θ`. -/
theorem sin_two_ge_four_div_pi_mul (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
  have h := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith [Real.pi_pos])
  have e : (2 / Real.pi) * (2 * θ) = (4 / Real.pi) * θ := by ring
  rwa [e] at h

/-- On `[π/4, π/2)`, `sin (2θ)` dominates `(4/π) (π/2 - θ)`. -/
theorem sin_two_ge_four_div_pi_mul_sub (θ : ℝ) (h0 : Real.pi / 4 ≤ θ) (h1 : θ < Real.pi / 2) :
    (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  have ht0 : 0 ≤ Real.pi / 2 - θ := by linarith [Real.pi_pos]
  have ht1 : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith
  have h := sin_two_ge_four_div_pi_mul (Real.pi / 2 - θ) ht0 ht1
  rwa [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub] at h

/-! ## The pointwise bounds

Both are stated for a general "distance" `t` (which will be `θ` at the left endpoint and
`π/2 - θ` at the right one); the only input is `(4/π) t ≤ sin (2θ)`. -/

/-- `|sig η θ · f θ · f' θ| ≤ C² (4/π)^{-η} t^{1-η}` whenever `(4/π) t ≤ sin (2θ)`,
`|f θ| ≤ C t` and `|f' θ| ≤ C`. -/
theorem abs_sig_mul_le (f : ℝ → ℝ) (η C : ℝ) {t θ : ℝ} (hη0 : 0 ≤ η) (hC : 0 ≤ C)
    (ht0 : 0 < t) (hsin : 0 < Real.sin (2 * θ))
    (hge : (4 / Real.pi) * t ≤ Real.sin (2 * θ)) (hf : |f θ| ≤ C * t)
    (hd : |deriv f θ| ≤ C) :
    |sig η θ * f θ * deriv f θ| ≤ C ^ 2 * (4 / Real.pi) ^ (-η) * t ^ (1 - η) := by
  have htpos : (0 : ℝ) < (4 / Real.pi) * t := by positivity
  have hσ : |sig η θ| ≤ ((4 / Real.pi) * t) ^ (-η) := by
    simp only [sig]
    rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hsin) _)]
    exact Real.rpow_le_rpow_of_nonpos htpos hge (by linarith)
  have hxnn : (0 : ℝ) ≤ ((4 / Real.pi) * t) ^ (-η) := Real.rpow_nonneg (le_of_lt htpos) _
  have hstep : |sig η θ| * |f θ| * |deriv f θ| ≤ ((4 / Real.pi) * t) ^ (-η) * (C * t) * C := by
    refine mul_le_mul (mul_le_mul hσ hf (abs_nonneg _) hxnn) hd (abs_nonneg _) ?_
    exact mul_nonneg hxnn (mul_nonneg hC (le_of_lt ht0))
  have hcomb : t ^ (-η) * t = t ^ (1 - η) := by
    have h1 : t ^ (-η) * t ^ (1 : ℝ) = t ^ (-η + 1) := (Real.rpow_add ht0 (-η) 1).symm
    rw [Real.rpow_one] at h1
    rw [h1]
    congr 1
    ring
  have hfin : ((4 / Real.pi) * t) ^ (-η) * (C * t) * C
      = C ^ 2 * (4 / Real.pi) ^ (-η) * t ^ (1 - η) := by
    rw [Real.mul_rpow (by positivity) (le_of_lt ht0)]
    calc (4 / Real.pi) ^ (-η) * t ^ (-η) * (C * t) * C
        = (4 / Real.pi) ^ (-η) * C ^ 2 * (t ^ (-η) * t) := by ring
      _ = (4 / Real.pi) ^ (-η) * C ^ 2 * t ^ (1 - η) := by rw [hcomb]
      _ = C ^ 2 * (4 / Real.pi) ^ (-η) * t ^ (1 - η) := by ring
  calc |sig η θ * f θ * deriv f θ| = |sig η θ| * |f θ| * |deriv f θ| := by rw [abs_mul, abs_mul]
    _ ≤ ((4 / Real.pi) * t) ^ (-η) * (C * t) * C := hstep
    _ = C ^ 2 * (4 / Real.pi) ^ (-η) * t ^ (1 - η) := hfin

/-- `|rho η θ · f θ²| ≤ C² (4/π)^{-η-1} t^{1-η}` whenever `(4/π) t ≤ sin (2θ)` and
`|f θ| ≤ C t`. -/
theorem abs_rho_mul_le (f : ℝ → ℝ) (η C : ℝ) {t θ : ℝ} (hη0 : 0 ≤ η) (_hC : 0 ≤ C)
    (ht0 : 0 < t) (hsin : 0 < Real.sin (2 * θ))
    (hge : (4 / Real.pi) * t ≤ Real.sin (2 * θ)) (hf : |f θ| ≤ C * t) :
    |rho η θ * f θ ^ 2| ≤ C ^ 2 * (4 / Real.pi) ^ (-η - 1) * t ^ (1 - η) := by
  have htpos : (0 : ℝ) < (4 / Real.pi) * t := by positivity
  have hpow : |rho η θ| ≤ ((4 / Real.pi) * t) ^ (-η - 1) := by
    simp only [rho]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hsin) _)]
    have h1 : Real.sin (2 * θ) ^ (-η - 1) ≤ ((4 / Real.pi) * t) ^ (-η - 1) :=
      Real.rpow_le_rpow_of_nonpos htpos hge (by linarith)
    have h2 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h3 : 0 ≤ Real.sin (2 * θ) ^ (-η - 1) := Real.rpow_nonneg (le_of_lt hsin) _
    calc |Real.cos (2 * θ)| * Real.sin (2 * θ) ^ (-η - 1)
        ≤ 1 * Real.sin (2 * θ) ^ (-η - 1) := mul_le_mul_of_nonneg_right h2 h3
      _ = Real.sin (2 * θ) ^ (-η - 1) := one_mul _
      _ ≤ ((4 / Real.pi) * t) ^ (-η - 1) := h1
  have hxnn : (0 : ℝ) ≤ ((4 / Real.pi) * t) ^ (-η - 1) := Real.rpow_nonneg (le_of_lt htpos) _
  have hf2 : |f θ| ^ 2 ≤ (C * t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hf 2
  have hstep : |rho η θ| * |f θ| ^ 2 ≤ ((4 / Real.pi) * t) ^ (-η - 1) * (C * t) ^ 2 :=
    mul_le_mul hpow hf2 (by positivity) hxnn
  have hcomb : t ^ (-η - 1) * t ^ 2 = t ^ (1 - η) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht0]
    congr 1
    ring
  have hfin : ((4 / Real.pi) * t) ^ (-η - 1) * (C * t) ^ 2
      = C ^ 2 * (4 / Real.pi) ^ (-η - 1) * t ^ (1 - η) := by
    rw [Real.mul_rpow (by positivity) (le_of_lt ht0), mul_pow]
    calc (4 / Real.pi) ^ (-η - 1) * t ^ (-η - 1) * (C ^ 2 * t ^ 2)
        = (4 / Real.pi) ^ (-η - 1) * C ^ 2 * (t ^ (-η - 1) * t ^ 2) := by ring
      _ = (4 / Real.pi) ^ (-η - 1) * C ^ 2 * t ^ (1 - η) := by rw [hcomb]
      _ = C ^ 2 * (4 / Real.pi) ^ (-η - 1) * t ^ (1 - η) := by ring
  calc |rho η θ * f θ ^ 2| = |rho η θ| * |f θ| ^ 2 := by rw [abs_mul, abs_pow]
    _ ≤ ((4 / Real.pi) * t) ^ (-η - 1) * (C * t) ^ 2 := hstep
    _ = C ^ 2 * (4 / Real.pi) ^ (-η - 1) * t ^ (1 - η) := hfin

/-! ## The limit facts for the powers `θ^{1-η}` -/

/-- `θ^{1-η} → 0` as `θ → 0⁺` for `η < 1`. -/
theorem tendsto_rpow_one_sub_nhdsGT_zero {η : ℝ} (hη1 : η < 1) :
    Filter.Tendsto (fun θ : ℝ => θ ^ (1 - η)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine (((tendsto_rpow_neg_atTop (y := 1 - η) (by linarith)).comp
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x _
  rw [Function.comp_apply, Real.rpow_neg_eq_inv_rpow, inv_inv]

/-- `θ ↦ π/2 - θ` maps the left neighbourhood of `π/2` to the right neighbourhood of `0`. -/
theorem tendsto_sub_pi_div_two_nhdsLT :
    Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝[<] (Real.pi / 2)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h1 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 (Real.pi / 2))
        (𝓝 (Real.pi / 2 - Real.pi / 2)) := tendsto_const_nhds.sub tendsto_id
    simpa using h1.mono_left nhdsWithin_le_nhds
  · refine mem_of_superset self_mem_nhdsWithin ?_
    intro θ hθ
    show (0 : ℝ) < Real.pi / 2 - θ
    linarith [Real.pi_pos, Set.mem_Iio.mp hθ]

/-- `(π/2 - θ)^{1-η} → 0` as `θ → π/2⁻` for `η < 1`. -/
theorem tendsto_rpow_one_sub_nhdsLT_pi_div_two {η : ℝ} (hη1 : η < 1) :
    Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (1 - η))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
  (tendsto_rpow_one_sub_nhdsGT_zero hη1).comp tendsto_sub_pi_div_two_nhdsLT

/-! ## The four limits -/

theorem tendsto_sig_mul_deriv_nhdsGT_zero (f : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hC : 0 ≤ C) (hb1 : ∀ θ ∈ Iθo, |f θ| ≤ C * θ) (hb3 : ∀ θ ∈ Iθo, |deriv f θ| ≤ C) :
    Filter.Tendsto (fun θ => sig η θ * f θ * deriv f θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsGT_zero (η := η) hη1
  have hA : Filter.Tendsto (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η) * θ ^ (1 - η))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η))
  refine squeeze_zero_norm' ?_ hA
  have hsmall : Set.Iio (Real.pi / 4) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4))
  filter_upwards [self_mem_nhdsWithin, hsmall] with θ hθ0 hθ1
  have h0 : (0 : ℝ) < θ := Set.mem_Ioi.mp hθ0
  have h1 : θ ≤ Real.pi / 4 := le_of_lt (Set.mem_Iio.mp hθ1)
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨h0, by linarith [Real.pi_pos, h1]⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, h1])
  rw [Real.norm_eq_abs]
  exact abs_sig_mul_le f η C hη0 hC h0 hsin (sin_two_ge_four_div_pi_mul θ (le_of_lt h0) h1)
    (hb1 θ hθI) (hb3 θ hθI)

theorem tendsto_sig_mul_deriv_nhdsLT_pi_div_two (f : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hC : 0 ≤ C) (hb2 : ∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 2 - θ))
    (hb3 : ∀ θ ∈ Iθo, |deriv f θ| ≤ C) :
    Filter.Tendsto (fun θ => sig η θ * f θ * deriv f θ)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsLT_pi_div_two (η := η) hη1
  have hA : Filter.Tendsto
      (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 2 - θ) ^ (1 - η))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η))
  refine squeeze_zero_norm' ?_ hA
  have hbig : Set.Ioi (Real.pi / 4) ∈ 𝓝[<] (Real.pi / 2) :=
    mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2))
  filter_upwards [self_mem_nhdsWithin, hbig] with θ hθ1 hθ0
  have h1 : θ < Real.pi / 2 := Set.mem_Iio.mp hθ1
  have h0 : Real.pi / 4 ≤ θ := le_of_lt (Set.mem_Ioi.mp hθ0)
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨by linarith [Real.pi_pos, h0], h1⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, h0]) (by linarith [Real.pi_pos, h1])
  have ht0 : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos, h1]
  rw [Real.norm_eq_abs]
  exact abs_sig_mul_le f η C hη0 hC ht0 hsin (sin_two_ge_four_div_pi_mul_sub θ h0 h1)
    (hb2 θ hθI) (hb3 θ hθI)

theorem tendsto_rho_mul_sq_nhdsGT_zero (f : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hC : 0 ≤ C) (hb1 : ∀ θ ∈ Iθo, |f θ| ≤ C * θ) :
    Filter.Tendsto (fun θ => rho η θ * f θ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsGT_zero (η := η) hη1
  have hA : Filter.Tendsto (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η - 1) * θ ^ (1 - η))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η - 1))
  refine squeeze_zero_norm' ?_ hA
  have hsmall : Set.Iio (Real.pi / 4) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4))
  filter_upwards [self_mem_nhdsWithin, hsmall] with θ hθ0 hθ1
  have h0 : (0 : ℝ) < θ := Set.mem_Ioi.mp hθ0
  have h1 : θ ≤ Real.pi / 4 := le_of_lt (Set.mem_Iio.mp hθ1)
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨h0, by linarith [Real.pi_pos, h1]⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, h1])
  rw [Real.norm_eq_abs]
  exact abs_rho_mul_le f η C hη0 hC h0 hsin (sin_two_ge_four_div_pi_mul θ (le_of_lt h0) h1)
    (hb1 θ hθI)

theorem tendsto_rho_mul_sq_nhdsLT_pi_div_two (f : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hC : 0 ≤ C) (hb2 : ∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 2 - θ)) :
    Filter.Tendsto (fun θ => rho η θ * f θ ^ 2) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsLT_pi_div_two (η := η) hη1
  have hA : Filter.Tendsto
      (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η - 1) * (Real.pi / 2 - θ) ^ (1 - η))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η - 1))
  refine squeeze_zero_norm' ?_ hA
  have hbig : Set.Ioi (Real.pi / 4) ∈ 𝓝[<] (Real.pi / 2) :=
    mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2))
  filter_upwards [self_mem_nhdsWithin, hbig] with θ hθ1 hθ0
  have h1 : θ < Real.pi / 2 := Set.mem_Iio.mp hθ1
  have h0 : Real.pi / 4 ≤ θ := le_of_lt (Set.mem_Ioi.mp hθ0)
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨by linarith [Real.pi_pos, h0], h1⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, h0]) (by linarith [Real.pi_pos, h1])
  have ht0 : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos, h1]
  rw [Real.norm_eq_abs]
  exact abs_rho_mul_le f η C hη0 hC ht0 hsin (sin_two_ge_four_div_pi_mul_sub θ h0 h1)
    (hb2 θ hθI)

theorem SliceBoundary (f : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (hC : 0 ≤ C)
    (hb1 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |f θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |f θ| ≤ C * (Real.pi / 2 - θ))
    (hb3 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |deriv f θ| ≤ C) :
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.Honest.sig η θ * f θ * deriv f θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.Honest.sig η θ * f θ * deriv f θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.Honest.rho η θ * f θ ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.Honest.rho η θ * f θ ^ 2) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  ⟨tendsto_sig_mul_deriv_nhdsGT_zero f η C hη0 hη1 hC hb1 hb3,
   tendsto_sig_mul_deriv_nhdsLT_pi_div_two f η C hη0 hη1 hC hb2 hb3,
   tendsto_rho_mul_sq_nhdsGT_zero f η C hη0 hη1 hC hb1,
   tendsto_rho_mul_sq_nhdsLT_pi_div_two f η C hη0 hη1 hC hb2⟩

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SliceIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option linter.unusedVariables false

/-! ## Elementary facts about the open interval `Iθo = (0, π/2)` -/

/-- `sin(2θ)` is positive on `Iθo`. -/
private lemma sin_two_pos_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])





/-! ## The integrability of the singular weight and the domination principle -/

/-- `θ ↦ sin(2θ)^p` is integrable on the open interval `Iθo` for `p > -1`. -/
private lemma integrableOn_sin_rpow_Ioo {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Iθo volume := by
  by_cases hp0 : 0 ≤ p
  · -- nonnegative exponent: the integrand is bounded by `1` on the finite interval
    have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Iθo :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ _ => Or.inr hp0)
    refine MeasureTheory.Integrable.mono' (f := fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
      (g := fun _ : ℝ => (1 : ℝ))
      (MeasureTheory.integrableOn_const (s := Iθo) (C := (1 : ℝ)) ?_) ?_ ?_
    · rw [Iθo, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    · exact hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sin_two_pos_Iθo hθ).le p)]
      exact Real.rpow_le_one (sin_two_pos_Iθo hθ).le (Real.sin_le_one _) hp0
  · -- negative exponent: compare with the integrable endpoint majorant
    simp only [not_le] at hp0
    have hq : 0 < -p := by linarith
    have hq1 : -p < 1 := by linarith
    have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Iθo :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Iθo hθ)))
    refine (Work.Elliptic.integrableOn_of_rpow_majorant (η := -p) hq.le hq1
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) (-p)) hcont
      ?_).mono_set Ioo_subset_Icc_self
    intro θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sin_two_pos_Iθo hθ).le p)]
    simpa only [neg_neg] using
      Work.Spaces.sin_rpow_le_majorant_pi (-p) θ hq ⟨hθ.1.le, hθ.2.le⟩


/-! ## Continuity of the derivatives of a `C²` function on the closed interval -/



/-! ## The theorem -/


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SliceWeightDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

/-- On the open interval `Iθo` the base `sin(2θ)` is strictly positive. -/
theorem sin_two_pos_of_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.sin (2 * θ) := by
  rw [Iθo, Set.mem_Ioo] at hθ
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])

/-- The derivative of `θ ↦ sin(2θ)` on the open interval. -/
theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := hasDerivAt_const_mul (2 : ℝ)
  exact (HasDerivAt.comp (hh₂ := Real.hasDerivAt_sin (2 * θ)) (hh := h1)).congr_deriv (by ring)

/-- The derivative of `θ ↦ cos(2θ)` on the open interval. -/
theorem hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-2 * Real.sin (2 * θ)) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := hasDerivAt_const_mul (2 : ℝ)
  exact (HasDerivAt.comp (hh₂ := Real.hasDerivAt_cos (2 * θ)) (hh := h1)).congr_deriv (by ring)

/-- The weight `sig η` has derivative `sigD η` at every point of the open interval. -/
theorem sig_hasDerivAt (η : ℝ) {θ : ℝ} (hθ : θ ∈ Iθo) :
    HasDerivAt (sig η) (sigD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) := sin_two_pos_of_Iθo hθ
  have hpow := (hasDerivAt_sin_two θ).rpow_const (p := -η) (Or.inl (ne_of_gt hspos))
  refine hpow.congr_deriv ?_
  simp only [sigD]
  ring

/-- The weight `rho η` has derivative `rhoD η` at every point of the open interval. -/
theorem rho_hasDerivAt (η : ℝ) {θ : ℝ} (hθ : θ ∈ Iθo) :
    HasDerivAt (rho η) (rhoD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) := sin_two_pos_of_Iθo hθ
  have hpow := (hasDerivAt_sin_two θ).rpow_const (p := -η - 1) (Or.inl (ne_of_gt hspos))
  have hprod := (hasDerivAt_cos_two θ).mul hpow
  refine hprod.congr_deriv ?_
  rw [show -η - 1 - 1 = -η - 2 by ring]
  -- `sin(2θ) · sin(2θ)^{-η-1} = sin(2θ)^{-η}` at the positive base
  have hrw : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-η - 1) = Real.sin (2 * θ) ^ (-η) := by
    nth_rewrite 1 [← Real.rpow_one (Real.sin (2 * θ))]
    rw [← Real.rpow_add hspos (1 : ℝ) (-η - 1)]
    congr 1
    ring
  simp only [rhoD]
  rw [show (-2 * Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (-η - 1)
        = -2 * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-η - 1)) by ring, hrw]
  rw [show -η - 2 = -(2 + η) by ring]
  ring


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.ZBoxLintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The "box" Tonelli lemma `ZBoxLintegral`

`ZBoxLintegral` compares a **slicewise** bound on a kernel `f u θ` with the **box** integral:
if for every `u ∈ [a,b]` the angular integral of `f u ·` is at most `c u`, then the angular
integral of the `u`-integral of `f` is at most the `u`-integral of `c`.  In symbols:

`∫⁻_θ (∫_u f u θ) ≤ ∫_u c u`, i.e. `"∫_θ ∫_u f ≤ ∫_u ∫_θ f ≤ ∫_u c"`.

The point is that the *first* inequality (`∫_θ ∫_u f ≤ ∫_u ∫_θ f`) is Tonelli for the
`θ`-then-`u` iterated integral, and the only joint measurability available is the one in the
order `(volume.restrict Iθ).prod (volume.restrict (Icc a b))` applied to the swapped function
`p ↦ f p.2 p.1` — exactly the hypothesis `haem` of the statement.  Mathlib's
`MeasureTheory.lintegral_lintegral_swap` is stated with precisely this measurability
hypothesis, so no separate "swap of almost-everywhere measurability" argument is needed.

The passage from the *Bochner* integral `∫ u in a..b, f u θ` to the `∫⁻`-integral is the
elementary inequality `ENNReal.ofReal (∫ f) ≤ ∫⁻ ENNReal.ofReal f` (`ofReal_integral_le_lintegral`
below), which holds for **every** real function: for a non-integrable function the Bochner
integral takes the junk value `0` while the right-hand side is at least `0`.  In particular the
statement does not need the nonnegativity hypothesis `hnn`, nor the slice measurability
`hslice_meas`; both are kept because the statement is fixed.
-/

namespace Work.FTS.EllipticEst.Honest

-- The nonnegativity `hnn` and the slice measurability `hslice_meas` of the statement are not
-- needed for the argument below (see the module docstring); they are kept because the statement
-- is fixed.
set_option linter.unusedVariables false

open MeasureTheory

/-- For any real-valued function, the `ENNReal.ofReal` of the Bochner integral is at most the
`∫⁻` of the `ofReal`s.  (For a non-integrable function the Bochner integral is the junk value
`0`, and for an integrable one the claim follows from
`integral_eq_lintegral_pos_part_sub_lintegral_neg_part` together with
`ENNReal.ofReal_toReal_le`.) -/
theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hf : Integrable f μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_toReal_le
    exact sub_le_self _ ENNReal.toReal_nonneg
  · rw [integral_undef hf]
    simp


end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.derivDeriv_divCos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The chain rule for `u = cos θ · ψ`.**  If `u` is `C²` at `θ` and `cos θ ≠ 0`, then with
`ψ = u / cos` one has `u''(θ) = ψ''(θ)·cos θ - 2·ψ'(θ)·sin θ - ψ(θ)·cos θ`.

Route: near `θ` the identity `u = ψ · cos` holds (as `cos ≠ 0`), so `u' = ψ'·cos - ψ·sin` as
functions near `θ`; differentiating that exhibited expression at `θ` (product rule, for which
`ψ'` must be differentiable at `θ`, which follows from `ψ` being `C²` there since it is the
quotient of the `C²` function `u` by the nonvanishing smooth function `cos`) gives the claim. -/
theorem derivDeriv_divCos (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    deriv (deriv u) θ
      = deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ * Real.cos θ
        - 2 * deriv (fun t : ℝ => u t / Real.cos t) θ * Real.sin θ
        - (u θ / Real.cos θ) * Real.cos θ := by
  obtain ⟨s, hs_mem, hs_reg⟩ := hu.contDiffOn le_rfl (by simp)
  have hmem : interior s ∈ 𝓝 θ :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs_mem)
  have hreg : ContDiffOn ℝ 2 u (interior s) := hs_reg.mono interior_subset
  have hdiff : ∀ t ∈ interior s, DifferentiableAt ℝ u t := fun t ht =>
    (hreg.differentiableOn (by simp)).differentiableAt (isOpen_interior.mem_nhds ht)
  have hcos_nhds : ∀ᶠ t in 𝓝 θ, Real.cos t ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hcos
  -- `u' = ψ' · cos - ψ · sin`, as an eventual equality of functions
  have heq_deriv : deriv u =ᶠ[𝓝 θ]
      fun t : ℝ =>
        deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t - (u t / Real.cos t) * Real.sin t := by
    filter_upwards [hcos_nhds, hmem] with t ht hts
    have heqt : u =ᶠ[𝓝 t] fun s : ℝ => (u s / Real.cos s) * Real.cos s := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne ht] with s hs
      exact (div_mul_cancel₀ (u s) hs).symm
    have hd : deriv (fun s : ℝ => (u s / Real.cos s) * Real.cos s) t
        = deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
          + (u t / Real.cos t) * (-Real.sin t) := by
      have hVt : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) t :=
        (hdiff t hts).div Real.differentiableAt_cos ht
      have h3 : HasDerivAt (fun s : ℝ => (u s / Real.cos s) * Real.cos s)
          (deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
            + (u t / Real.cos t) * (-Real.sin t)) t :=
        hVt.hasDerivAt.mul (Real.hasDerivAt_cos t)
      exact h3.deriv
    rw [heqt.deriv_eq, hd]
    ring
  rw [heq_deriv.deriv_eq]
  -- the two factors of the exhibited expression are differentiable at `θ`
  have hVd : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) θ :=
    (hu.div (Real.contDiff_cos.contDiffAt) hcos).differentiableAt (by simp)
  have hDd : DifferentiableAt ℝ (deriv (fun s : ℝ => u s / Real.cos s)) θ :=
    ((hu.div (Real.contDiff_cos.contDiffAt) hcos).derivWithin (m := 1) (by norm_num)
      ).differentiableAt (by simp)
  have h1 : HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t)
      (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
        + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ)) θ :=
    hDd.hasDerivAt.mul (Real.hasDerivAt_cos θ)
  have h2 : HasDerivAt (fun t : ℝ => (u t / Real.cos t) * Real.sin t)
      (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
        + (u θ / Real.cos θ) * Real.cos θ) θ :=
    hVd.hasDerivAt.mul (Real.hasDerivAt_sin θ)
  have h3 := h1.sub h2
  have h4 : deriv (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
        - (u t / Real.cos t) * Real.sin t) θ
      = (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
          + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ))
        - (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
            + (u θ / Real.cos θ) * Real.cos θ) := h3.deriv
  rw [h4]
  ring

/-- **The rearranged chain rule.**  If `u` is `C²` at `θ` and `cos θ ≠ 0`, then with
`ψ = u / cos` one has `cos θ · ψ''(θ) = u''(θ) + cos θ · ψ(θ) + 2 sin θ · ψ'(θ)`.

This is the form in which the second derivative `ψ''` of the slice variable is eliminated
from the products of the `I₄` calculus: multiplying by `sin θ · sin(2θ)^{-η} · ψ'(θ)` turns
`sin θ cos θ sin(2θ)^{-η} ψ' ψ''` into a combination of the (given) integrable quantities
`sin²θ sin(2θ)^{-η} (ψ')²`, `sin θ sin(2θ)^{-η} ψ' u''` and `sin θ cos θ sin(2θ)^{-η} ψ ψ'`. -/
theorem cos_mul_derivDeriv_divCos (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    Real.cos θ * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
      = deriv (deriv u) θ + Real.cos θ * (u θ / Real.cos θ)
        + 2 * Real.sin θ * deriv (fun t : ℝ => u t / Real.cos t) θ := by
  have h := derivDeriv_divCos u hu hcos
  linarith [h]

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.divCos_tendsto_of_tendsto_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

-- `u` smooth on the open interval, `u → 0` and `u' → L` at π/2^-  ⟹  u/cos θ → -L.
-- Route: u θ = -∫_θ^{π/2} u' (FTC on (θ, π/2-ε) for a fixed θ, then let ε→0 using u → 0), and
-- u' = L + (u'-L) with |∫_θ^{π/2}(u'-L)| ≤ δ·sup_{t>θ}|u'(t)-L| = o(δ), δ := π/2-θ; so
-- u θ/cos θ = -L·δ/cos θ - o(δ)/cos θ → -L, using δ/cos θ = δ/sin δ → 1.
theorem divCos_tendsto_of_tendsto_deriv {u : ℝ → ℝ} {L : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hzero : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hL : Filter.Tendsto (deriv u) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L)) :
    Filter.Tendsto (fun θ => u θ / Real.cos θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (-L)) := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by positivity
  have hdiff : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm 1).differentiableOn (by norm_num)
  have hff' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u x) x := by
    intro x hx
    exact ((hdiff x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
  have hgg' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt Real.cos ((fun x => -Real.sin x) x) x :=
    fun x _ => Real.hasDerivAt_cos x
  have hg' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (fun x => -Real.sin x) x ≠ 0 := by
    intro x hx
    have hπx : x < Real.pi := by linarith [Real.pi_pos, hx.2]
    have hpos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 hπx
    simp only
    intro h
    linarith
  have hgb : Filter.Tendsto Real.cos (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := by
    have h : Filter.Tendsto Real.cos (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (Real.cos (Real.pi / 2))) :=
      Real.continuous_cos.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [Real.cos_pi_div_two] using h
  have hdiv : Filter.Tendsto (deriv u / fun x => -Real.sin x)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (-L)) := by
    have hsin : Filter.Tendsto (fun x : ℝ => -Real.sin x)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (-1)) := by
      have h : Filter.Tendsto Real.sin (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (Real.sin (Real.pi / 2))) :=
        Real.continuous_sin.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h' := h.neg
      simpa [Real.sin_pi_div_two] using h'
    have hd := hL.div hsin (by norm_num : (-1 : ℝ) ≠ 0)
    have hLdiv : L / (-1 : ℝ) = -L := by ring
    rwa [hLdiv] at hd
  exact HasDerivAt.lhopital_zero_left_on_Ioo (f := u) (g := Real.cos)
    (f' := deriv u) (g' := fun x => -Real.sin x) (l := nhds (-L))
    hπ hff' hgg' hg' hzero hgb hdiv

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.subst_cos_cube_sin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.LevelOneAsm

open MeasureTheory intervalIntegral


end Work.FTS.EllipticEst.LevelOneAsm
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.zcutFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology
open Filter

namespace Work.FTS.EllipticEst.Mine

/-! ## Two generic `deriv` rules in the lambda form used below -/

/-- Derivative of `w ↦ f (w * B)` (the `B⁻¹`-rescaled right factor). -/
theorem deriv_comp_mul_right (B x : ℝ) (f : ℝ → ℝ) :
    deriv (fun w : ℝ => f (w * B)) x = deriv f (x * B) * B := by
  have hfun : (fun w : ℝ => f (w * B)) = fun w : ℝ => f (B * w) := by
    funext w; rw [mul_comm]
  rw [hfun, deriv_comp_mul_left]
  simp only [smul_eq_mul]
  rw [mul_comm B x]; ring

/-- Product rule in lambda form. -/
theorem deriv_prod_lam (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y : ℝ => f y * g y) x = deriv f x * g x + f x * deriv g x := by
  change deriv (f * g) x = deriv f x * g x + f x * deriv g x
  rw [deriv_mul hf hg]

/-- Difference rule in lambda form. -/
theorem deriv_sub_lam (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y : ℝ => f y - g y) x = deriv f x - deriv g x := by
  change deriv (f - g) x = deriv f x - deriv g x
  rw [deriv_sub hf hg]

/-! ## Smoothness and pointwise range of the cut-off -/

theorem zcChi_contDiff (n m : ℕ) : ContDiff ℝ m (zcChi n) := by
  have h1 : ContDiff ℝ m (fun z : ℝ => zcPsi (zcScale n * z)) :=
    (zcPsi_contDiff m).comp (contDiff_const.mul contDiff_id)
  have h2 : ContDiff ℝ m (fun z : ℝ => zcPsi (z * (zcScale n)⁻¹)) :=
    (zcPsi_contDiff m).comp (contDiff_id.mul contDiff_const)
  have h3 : ContDiff ℝ m (fun z : ℝ => 1 - zcPsi (z * (zcScale n)⁻¹)) :=
    contDiff_const.sub h2
  exact h1.mul h3

theorem zcChi_nonneg (n : ℕ) (z : ℝ) : 0 ≤ zcChi n z := by
  show 0 ≤ zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
  have h1 : 0 ≤ zcPsi (zcScale n * z) := zcPsi_nonneg _
  have h2 : 0 ≤ 1 - zcPsi (z * (zcScale n)⁻¹) := by
    linarith [zcPsi_le_one (z * (zcScale n)⁻¹)]
  positivity

theorem zcChi_le_one (n : ℕ) (z : ℝ) : zcChi n z ≤ 1 := by
  show zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)) ≤ 1
  have h1 : 0 ≤ zcPsi (zcScale n * z) := zcPsi_nonneg _
  have h2 : zcPsi (zcScale n * z) ≤ 1 := zcPsi_le_one _
  have h3 : 0 ≤ 1 - zcPsi (z * (zcScale n)⁻¹) := by
    linarith [zcPsi_le_one (z * (zcScale n)⁻¹)]
  have h4 : 1 - zcPsi (z * (zcScale n)⁻¹) ≤ 1 := by
    linarith [zcPsi_nonneg (z * (zcScale n)⁻¹)]
  nlinarith [mul_le_mul h2 h4 h3 (by norm_num : (0:ℝ) ≤ 1)]

/-! ## The three threshold regimes -/

theorem zcChi_eq_zero_left (n : ℕ) (z : ℝ) (hz : z ≤ 1 / ((n : ℝ) + 1)) : zcChi n z = 0 := by
  have hz' : z ≤ (zcScale n)⁻¹ := by rw [one_div] at hz; exact hz
  have h : zcScale n * z ≤ 1 := by
    calc zcScale n * z ≤ zcScale n * (zcScale n)⁻¹ :=
          mul_le_mul_of_nonneg_left hz' (le_of_lt (zcScale_pos n))
      _ = 1 := zcScale_mul_inv n
  show zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)) = 0
  rw [zcPsi_eq_zero h, zero_mul]

theorem zcChi_eq_one_mid (n : ℕ) (z : ℝ) (hz1 : 2 / ((n : ℝ) + 1) ≤ z)
    (hz2 : z ≤ (n : ℝ) + 1) : zcChi n z = 1 := by
  have hA : 0 < zcScale n := zcScale_pos n
  have hz1' : 2 * (zcScale n)⁻¹ ≤ z := by rw [div_eq_mul_inv] at hz1; exact hz1
  have hz2' : z ≤ zcScale n := hz2
  have h1 : 2 ≤ zcScale n * z := by
    have h := mul_le_mul_of_nonneg_right hz1' (le_of_lt hA)
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hA), mul_one] at h
    rwa [mul_comm z (zcScale n)] at h
  have h2 : z * (zcScale n)⁻¹ ≤ 1 := by
    calc z * (zcScale n)⁻¹ ≤ zcScale n * (zcScale n)⁻¹ :=
          mul_le_mul_of_nonneg_right hz2' (inv_nonneg.mpr (le_of_lt hA))
      _ = 1 := zcScale_mul_inv n
  show zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)) = 1
  rw [zcPsi_eq_one h1, zcPsi_eq_zero h2]
  ring

theorem zcChi_eq_zero_right (n : ℕ) (z : ℝ) (hz : 2 * ((n : ℝ) + 1) ≤ z) : zcChi n z = 0 := by
  have hA : 0 < zcScale n := zcScale_pos n
  have hz' : 2 * zcScale n ≤ z := hz
  have h : 2 ≤ z * (zcScale n)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_right hz' (inv_nonneg.mpr (le_of_lt hA))
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hA), mul_one] at h1
    exact h1
  show zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)) = 0
  rw [zcPsi_eq_one h, sub_self, mul_zero]

/-! ## The first weighted derivative, and its uniform bound -/

/-- `z ↦ z χ_n'(z)`, computed explicitly. -/
theorem deriv_zcChi_eq (n : ℕ) (z : ℝ) :
    deriv (zcChi n) z
      = deriv zcPsi (zcScale n * z) * zcScale n * (1 - zcPsi (z * (zcScale n)⁻¹))
        - zcPsi (zcScale n * z) * (deriv zcPsi (z * (zcScale n)⁻¹) * (zcScale n)⁻¹) := by
  have hd1 : DifferentiableAt ℝ (fun w : ℝ => zcPsi (zcScale n * w)) z := by
    have h : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  have hd2 : DifferentiableAt ℝ (fun w : ℝ => 1 - zcPsi (w * (zcScale n)⁻¹)) z := by
    have h : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  show deriv (fun w : ℝ => zcPsi (zcScale n * w) * (1 - zcPsi (w * (zcScale n)⁻¹))) z = _
  rw [deriv_prod_lam _ _ _ hd1 hd2, deriv_comp_mul_left, deriv_const_sub,
    deriv_comp_mul_right]
  ring

/-- **The first key identity**: `z χ_n'(z)` in terms of the weighted derivatives `k1`. -/
theorem zcChi_mul_deriv_eq (n : ℕ) (z : ℝ) :
    z * deriv (zcChi n) z
      = zcK1 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
        - zcPsi (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹) := by
  rw [deriv_zcChi_eq]
  simp only [zcK1]
  ring

theorem zcChi_deriv_bound (M₁ : ℝ) (hK1 : ∀ t : ℝ, |zcK1 t| ≤ M₁) (n : ℕ) (z : ℝ) :
    |z * deriv (zcChi n) z| ≤ 2 * M₁ := by
  rw [zcChi_mul_deriv_eq]
  have h1 : |1 - zcPsi (z * (zcScale n)⁻¹)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [zcPsi_le_one (z * (zcScale n)⁻¹)],
      by linarith [zcPsi_nonneg (z * (zcScale n)⁻¹)]⟩
  have h2 : |zcPsi (zcScale n * z)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [zcPsi_nonneg (zcScale n * z)], zcPsi_le_one _⟩
  have hM : 0 ≤ M₁ := le_trans (abs_nonneg _) (hK1 0)
  have hb1 : |zcK1 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))| ≤ M₁ := by
    rw [abs_mul]
    calc |zcK1 (zcScale n * z)| * |1 - zcPsi (z * (zcScale n)⁻¹)| ≤ M₁ * 1 :=
          mul_le_mul (hK1 _) h1 (abs_nonneg _) hM
      _ = M₁ := mul_one M₁
  have hb2 : |zcPsi (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)| ≤ M₁ := by
    rw [abs_mul]
    calc |zcPsi (zcScale n * z)| * |zcK1 (z * (zcScale n)⁻¹)| ≤ 1 * M₁ :=
          mul_le_mul h2 (hK1 _) (abs_nonneg _) (by norm_num)
      _ = M₁ := one_mul M₁
  calc |zcK1 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
        - zcPsi (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)|
      ≤ |zcK1 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))|
        + |zcPsi (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)| := abs_sub _ _
    _ ≤ M₁ + M₁ := add_le_add hb1 hb2
    _ = 2 * M₁ := by ring

/-! ## The second weighted derivative, and its uniform bound -/

/-- **The second key identity**: `z (z χ_n')'(z)` in terms of `k1` and `k2`. -/
theorem zcChi_second_mul (n : ℕ) (z : ℝ) :
    z * deriv (fun w : ℝ => w * deriv (zcChi n) w) z
      = zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
        - 2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)
        - zcPsi (zcScale n * z) * zcK2 (z * (zcScale n)⁻¹) := by
  have hfun : (fun w : ℝ => w * deriv (zcChi n) w)
      = fun w : ℝ => zcK1 (zcScale n * w) * (1 - zcPsi (w * (zcScale n)⁻¹))
          - zcPsi (zcScale n * w) * zcK1 (w * (zcScale n)⁻¹) :=
    funext fun w => zcChi_mul_deriv_eq n w
  rw [hfun]
  have hd1 : DifferentiableAt ℝ
      (fun w : ℝ => zcK1 (zcScale n * w) * (1 - zcPsi (w * (zcScale n)⁻¹))) z := by
    have h : Differentiable ℝ zcK1 := zcK1_diff
    have h' : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  have hd2 : DifferentiableAt ℝ
      (fun w : ℝ => zcPsi (zcScale n * w) * zcK1 (w * (zcScale n)⁻¹)) z := by
    have h : Differentiable ℝ zcK1 := zcK1_diff
    have h' : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  have hd3 : DifferentiableAt ℝ (fun w : ℝ => zcK1 (zcScale n * w)) z := by
    have h : Differentiable ℝ zcK1 := zcK1_diff
    fun_prop
  have hd4 : DifferentiableAt ℝ (fun w : ℝ => 1 - zcPsi (w * (zcScale n)⁻¹)) z := by
    have h : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  have hd5 : DifferentiableAt ℝ (fun w : ℝ => zcPsi (zcScale n * w)) z := by
    have h : Differentiable ℝ zcPsi := zcPsi_diff
    fun_prop
  have hd6 : DifferentiableAt ℝ (fun w : ℝ => zcK1 (w * (zcScale n)⁻¹)) z := by
    have h : Differentiable ℝ zcK1 := zcK1_diff
    fun_prop
  rw [deriv_sub_lam _ _ _ hd1 hd2, deriv_prod_lam _ _ _ hd3 hd4,
    deriv_prod_lam _ _ _ hd5 hd6,
    deriv_comp_mul_left, deriv_const_sub, deriv_comp_mul_right,
    deriv_comp_mul_left, deriv_comp_mul_right]
  simp only [zcK1, zcK2]
  ring

theorem zcChi_second_bound (M₁ M₂ : ℝ) (hK1 : ∀ t : ℝ, |zcK1 t| ≤ M₁)
    (hK2 : ∀ t : ℝ, |zcK2 t| ≤ M₂) (n : ℕ) (z : ℝ) :
    |z * deriv (fun w : ℝ => w * deriv (zcChi n) w) z| ≤ 2 * M₁ ^ 2 + 2 * M₂ := by
  rw [zcChi_second_mul]
  have h1 : |1 - zcPsi (z * (zcScale n)⁻¹)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [zcPsi_le_one (z * (zcScale n)⁻¹)],
      by linarith [zcPsi_nonneg (z * (zcScale n)⁻¹)]⟩
  have h2 : |zcPsi (zcScale n * z)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [zcPsi_nonneg (zcScale n * z)], zcPsi_le_one _⟩
  have hM : 0 ≤ M₁ := le_trans (abs_nonneg _) (hK1 0)
  have hb1 : |zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))| ≤ M₂ := by
    rw [abs_mul]
    calc |zcK2 (zcScale n * z)| * |1 - zcPsi (z * (zcScale n)⁻¹)| ≤ M₂ * 1 :=
          mul_le_mul (hK2 _) h1 (abs_nonneg _) (le_trans (abs_nonneg _) (hK2 0))
      _ = M₂ := mul_one M₂
  have hb2 : |2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)| ≤ 2 * M₁ ^ 2 := by
    have e : |2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)|
        = 2 * (|zcK1 (zcScale n * z)| * |zcK1 (z * (zcScale n)⁻¹)|) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
    rw [e]
    calc 2 * (|zcK1 (zcScale n * z)| * |zcK1 (z * (zcScale n)⁻¹)|) ≤ 2 * (M₁ * M₁) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hK1 _) (hK1 _) (abs_nonneg _) hM)
            (by norm_num)
      _ = 2 * M₁ ^ 2 := by ring
  have hb3 : |zcPsi (zcScale n * z) * zcK2 (z * (zcScale n)⁻¹)| ≤ M₂ := by
    rw [abs_mul]
    calc |zcPsi (zcScale n * z)| * |zcK2 (z * (zcScale n)⁻¹)| ≤ 1 * M₂ :=
          mul_le_mul h2 (hK2 _) (abs_nonneg _) (by norm_num)
      _ = M₂ := one_mul M₂
  have hsum :
      |zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
          - 2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)
          - zcPsi (zcScale n * z) * zcK2 (z * (zcScale n)⁻¹)|
        ≤ |zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))|
          + |2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹)|
          + |zcPsi (zcScale n * z) * zcK2 (z * (zcScale n)⁻¹)| := by
    have h1' := abs_sub (zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹))
      - 2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹))
      (zcPsi (zcScale n * z) * zcK2 (z * (zcScale n)⁻¹))
    have h2' := abs_sub (zcK2 (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)))
      (2 * zcK1 (zcScale n * z) * zcK1 (z * (zcScale n)⁻¹))
    linarith
  linarith [hsum, hb1, hb2, hb3]

/-! ## Convergence to `1` -/

theorem zcChi_tendsto (z : ℝ) (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => zcChi n z) Filter.atTop (nhds 1) := by
  have hscale : Filter.Tendsto (fun n : ℕ => zcScale n) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ))) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    simpa only [zcScale] using h1.atTop_add tendsto_const_nhds
  have e1 : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ z * zcScale n := by
    have h := (Filter.tendsto_atTop.1 hscale) (2 / z)
    filter_upwards [h] with n hn
    rw [div_le_iff₀ hz] at hn
    rwa [mul_comm]
  have e2 : ∀ᶠ n : ℕ in Filter.atTop, z ≤ zcScale n := (Filter.tendsto_atTop.1 hscale) z
  have hev : ∀ᶠ n : ℕ in Filter.atTop, zcChi n z = 1 := by
    filter_upwards [e1, e2] with n hn1 hn2
    have hn1' : 2 ≤ zcScale n * z := by linarith [hn1]
    have h3 : z * (zcScale n)⁻¹ ≤ 1 := by
      calc z * (zcScale n)⁻¹ ≤ zcScale n * (zcScale n)⁻¹ :=
            mul_le_mul_of_nonneg_right hn2 (inv_nonneg.mpr (le_of_lt (zcScale_pos n)))
        _ = 1 := zcScale_mul_inv n
    show zcPsi (zcScale n * z) * (1 - zcPsi (z * (zcScale n)⁻¹)) = 1
    rw [zcPsi_eq_one hn1', zcPsi_eq_zero h3]
    ring
  exact (Filter.tendsto_congr' hev).mpr tendsto_const_nhds

/-! ## Uniform bounds for `k1` and `k2`

Both `k1` and `k2` are continuous and vanish for `t < 1` and for `2 < t`, so they are bounded by
the supremum of their absolute values on the compact interval `[0,3]`.  This is also available as
the standalone module `Work.FTS.EllipticEst.Mine.zcutK12Bound`. -/

theorem zcK12Bound_self :
    ∃ M₁ M₂ : ℝ, 0 < M₁ ∧ 0 < M₂ ∧
      (∀ t : ℝ, |zcK1 t| ≤ M₁) ∧ (∀ t : ℝ, |zcK2 t| ≤ M₂) := by
  obtain ⟨a, _, ha⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 3)) zcK1_continuous.abs.continuousOn
  obtain ⟨b, _, hb⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 3)) zcK2_continuous.abs.continuousOn
  refine ⟨|zcK1 a| + 1, |zcK2 b| + 1, by positivity, by positivity, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 3
    · have hle : |zcK1 t| ≤ |zcK1 a| := ha ht
      linarith
    · rcases lt_or_ge t 0 with ht0 | ht0
      · rw [zcK1_eq_zero_of_lt_one (by linarith)]
        simp only [abs_zero]; positivity
      · have ht3 : 3 < t := lt_of_not_ge (fun hle => ht ⟨ht0, hle⟩)
        rw [zcK1_eq_zero_of_gt_two (by linarith)]
        simp only [abs_zero]; positivity
  · intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 3
    · have hle : |zcK2 t| ≤ |zcK2 b| := hb ht
      linarith
    · rcases lt_or_ge t 0 with ht0 | ht0
      · rw [zcK2_eq_zero_of_lt_one (by linarith)]
        simp only [abs_zero]; positivity
      · have ht3 : 3 < t := lt_of_not_ge (fun hle => ht ⟨ht0, hle⟩)
        rw [zcK2_eq_zero_of_gt_two (by linarith)]
        simp only [abs_zero]; positivity

/-! ## The cut-off family -/

theorem zcutFam :
    ∃ (χ : ℕ → ℝ → ℝ) (C₁ C₂ : ℝ), 0 < C₁ ∧ 0 < C₂ ∧
      (∀ n m : ℕ, ContDiff ℝ m (χ n)) ∧
      (∀ (n : ℕ) (z : ℝ), 0 ≤ χ n z ∧ χ n z ≤ 1) ∧
      (∀ (n : ℕ) (z : ℝ), z ≤ 1 / ((n : ℝ) + 1) → χ n z = 0) ∧
      (∀ (n : ℕ) (z : ℝ), 2 / ((n : ℝ) + 1) ≤ z → z ≤ (n : ℝ) + 1 → χ n z = 1) ∧
      (∀ (n : ℕ) (z : ℝ), 2 * ((n : ℝ) + 1) ≤ z → χ n z = 0) ∧
      (∀ (n : ℕ) (z : ℝ), |z * deriv (χ n) z| ≤ C₁) ∧
      (∀ (n : ℕ) (z : ℝ), |z * deriv (fun w : ℝ => w * deriv (χ n) w) z| ≤ C₂) ∧
      (∀ z, 0 < z → Filter.Tendsto (fun n : ℕ => χ n z) Filter.atTop (nhds 1)) := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hK1, hK2⟩ := zcK12Bound_self
  refine ⟨zcChi, 2 * M₁, 2 * M₁ ^ 2 + 2 * M₂, by linarith, by positivity, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact fun n m => zcChi_contDiff n m
  · exact fun n z => ⟨zcChi_nonneg n z, zcChi_le_one n z⟩
  · exact fun n z hz => zcChi_eq_zero_left n z hz
  · exact fun n z hz1 hz2 => zcChi_eq_one_mid n z hz1 hz2
  · exact fun n z hz => zcChi_eq_zero_right n z hz
  · exact fun n z => zcChi_deriv_bound M₁ hK1 n z
  · exact fun n z => zcChi_second_bound M₁ M₂ hK1 hK2 n z
  · exact fun z hz => zcChi_tendsto z hz

end Work.FTS.EllipticEst.Mine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.OpenFTC

/-- **FTC bound on an open interval.**  If `f` is `C¹` on the *open* interval `(0, π/2)`, vanishes
at some point `c` of that interval, and `|f'|` is integrable on the closed interval `Iθ = [0, π/2]`,
then `|f θ| ≤ ∫_{Iθ} |f'|` for every interior `θ ∈ (0, π/2)`.  Proof: the FTC on the segment
`[c, θ] ⊆ (0, π/2)` gives `f θ = ∫_c^θ f'`, and monotonicity of the integral of the nonnegative
`|f'|` bounds this by the integral over `Iθ`. -/
theorem absFtcLeIntegralAbsDeriv {f : ℝ → ℝ} {c : ℝ}
    (hcd : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hc : c ∈ Set.Ioo 0 (Real.pi / 2)) (hfz : f c = 0)
    (hint : MeasureTheory.IntegrableOn (fun s : ℝ => |deriv f s|) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ ∫ s in Work.Spaces.Iθ, |deriv f s| := by
  -- `Iθ = [0, π/2]` is the interval of integration, and the interval integral of a function
  -- agrees with the set integral over `Iθ`.
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hIeq : (∫ x in (0 : ℝ)..(Real.pi / 2), |deriv f x|)
      = ∫ s in Work.Spaces.Iθ, |deriv f s| := by
    rw [intervalIntegral.integral_of_le hle, Work.Spaces.Iθ,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- integrability of `|f'|` on the whole interval `[0, π/2]`, in interval-integral form
  have hgi : IntervalIntegrable (fun x : ℝ => |deriv f x|) volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hle]
    exact hint.mono_set Set.Ioc_subset_Icc_self
  intro θ hθ
  -- the segment `[c, θ]` lies in the open interval where `f` is `C¹`
  have hsub : Set.uIcc c θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hc.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hc.2⟩
  -- the fundamental theorem of calculus on that segment
  have hFTC : (∫ x in c..θ, deriv f x) = f θ - f c :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hcd.mono hsub)
  have hfθ : f θ = ∫ x in c..θ, deriv f x := by rw [hFTC, hfz, sub_zero]
  rw [hfθ]
  rcases le_total c θ with hct | htc
  · -- `θ` is to the right of `c`
    have h1 : |∫ x in c..θ, deriv f x| ≤ ∫ x in c..θ, |deriv f x| :=
      intervalIntegral.abs_integral_le_integral_abs (f := fun x => deriv f x) hct
    have h2 : (∫ x in c..θ, |deriv f x|) ≤ ∫ x in Work.Spaces.Iθ, |deriv f x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hc.1.le hct hθ.2.le
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    linarith
  · -- `θ` is to the left of `c`: reverse the orientation of the interval integral
    have hsym : (∫ x in c..θ, deriv f x) = -(∫ x in θ..c, deriv f x) := by
      rw [intervalIntegral.integral_symm (a := c) (b := θ)]
      ring
    have h1 : |∫ x in θ..c, deriv f x| ≤ ∫ x in θ..c, |deriv f x| :=
      intervalIntegral.abs_integral_le_integral_abs (f := fun x => deriv f x) htc
    have h2 : (∫ x in θ..c, |deriv f x|) ≤ ∫ x in Work.Spaces.Iθ, |deriv f x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hθ.1.le htc hc.2.le
        (Eventually.of_forall (fun x => abs_nonneg _)) hgi
    rw [hsym, abs_neg]
    linarith

end Work.FTS.EllipticEst.OpenFTC
end
