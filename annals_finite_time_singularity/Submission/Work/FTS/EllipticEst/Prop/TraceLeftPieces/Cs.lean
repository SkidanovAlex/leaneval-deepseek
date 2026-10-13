import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.derivIntegrableOfEnergy
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
import Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Cauchy–Schwarz bound `|∫ f χ f''| ≤ √A √D`
-/

namespace Work.FTS.EllipticEst.Prop.TraceLeftCore

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ### The weighted Cauchy–Schwarz bound on the `f f''`-term -/

theorem cutoff_cs (f χ : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hχcont : Continuous χ)
    (hχnn : ∀ θ : ℝ, 0 ≤ χ θ)
    (hχle : ∀ θ : ℝ, χ θ ≤ 1)
    (hA : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hD : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hkk : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2))) :
    |∫ θ in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), f θ * χ θ * deriv (deriv f) θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ) := by
  have hcont_f : ContinuousOn f (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) :=
    hf.continuousOn.mono sub_three
  have hcont_f2 : ContinuousOn (deriv (deriv f)) (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) :=
    ((hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (le_refl 1)).mono sub_three
  have hmf : AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hcont_f.aestronglyMeasurable measurableSet_Ioo
  have hmf2 : AEStronglyMeasurable (deriv (deriv f))
      (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hcont_f2.aestronglyMeasurable measurableSet_Ioo
  have hmχ : AEStronglyMeasurable χ (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hχcont.aestronglyMeasurable
  have hmw : AEStronglyMeasurable thEta (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    (continuousOn_thEta_Ioo.mono sub_three).aestronglyMeasurable measurableSet_Ioo
  have hcont_B : ContinuousOn (fun z : ℝ => (deriv (deriv f) z) ^ 2 * χ z / thEta z)
      (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) := by
    refine ContinuousOn.div ((hcont_f2.pow 2).mul hχcont.continuousOn)
      (continuousOn_thEta_Ioo.mono sub_three) ?_
    intro z hz
    exact (thEta_pos_of_Ioo (sub_three hz)).ne'
  have hmB : AEStronglyMeasurable (fun z : ℝ => (deriv (deriv f) z) ^ 2 * χ z / thEta z)
      (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hcont_B.aestronglyMeasurable measurableSet_Ioo
  have hAz : ∀ z ∈ Set.Ioo (0 : ℝ) (3 * Real.pi / 8), 0 ≤ (f z) ^ 2 * χ z * thEta z :=
    fun z hz => mul_nonneg (mul_nonneg (sq_nonneg _) (hχnn z)) (thEta_nonneg_Iθ (sub_three_Iθ hz))
  have hBz : ∀ z ∈ Set.Ioo (0 : ℝ) (3 * Real.pi / 8),
      0 ≤ (deriv (deriv f) z) ^ 2 * χ z / thEta z :=
    fun z hz => div_nonneg (mul_nonneg (sq_nonneg _) (hχnn z))
      (le_of_lt (thEta_pos_of_Ioo (sub_three hz)))
  -- integrability of the two weighted pieces
  have hAint : IntegrableOn (fun z : ℝ => (f z) ^ 2 * χ z * thEta z)
      (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) := by
    refine Integrable.mono' (hA.mono_set sub_three_Iθ) (((hmf.pow 2).mul hmχ).mul hmw) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hAz z hz)]
    calc (f z) ^ 2 * χ z * thEta z ≤ (f z) ^ 2 * 1 * thEta z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hχle z) (sq_nonneg (f z)))
            (thEta_nonneg_Iθ (sub_three_Iθ hz))
      _ = (f z) ^ 2 * thEta z := by ring
  have hBint : IntegrableOn (fun z : ℝ => (deriv (deriv f) z) ^ 2 * χ z / thEta z)
      (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) := by
    refine Integrable.mono' (hkk.mono_set sub_three) hmB ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hw1 : 1 ≤ thEta z := one_le_thEta_Ioo (sub_three hz)
    have hw0 : 0 < thEta z := thEta_pos_of_Ioo (sub_three hz)
    have hf2 : 0 ≤ (deriv (deriv f) z) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (hBz z hz)]
    rw [div_le_iff₀ hw0]
    calc (deriv (deriv f) z) ^ 2 * χ z ≤ (deriv (deriv f) z) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (hχle z) hf2
      _ = (deriv (deriv f) z) ^ 2 := by ring
      _ = (deriv (deriv f) z) ^ 2 * 1 := by ring
      _ ≤ (deriv (deriv f) z) ^ 2 * thEta z := mul_le_mul_of_nonneg_left hw1 hf2
  -- the pointwise Cauchy–Schwarz inequality
  have hpt : ∀ z ∈ Set.Ioo (0 : ℝ) (3 * Real.pi / 8),
      |f z * χ z * deriv (deriv f) z|
        ≤ Real.sqrt ((f z) ^ 2 * χ z * thEta z)
          * Real.sqrt ((deriv (deriv f) z) ^ 2 * χ z / thEta z) := by
    intro z hz
    have hwne : thEta z ≠ 0 := (thEta_pos_of_Ioo (sub_three hz)).ne'
    have hsq : (f z * χ z * deriv (deriv f) z) ^ 2
        = ((f z) ^ 2 * χ z * thEta z) * ((deriv (deriv f) z) ^ 2 * χ z / thEta z) := by
      field_simp
    have hcalc : |f z * χ z * deriv (deriv f) z|
        = Real.sqrt ((f z) ^ 2 * χ z * thEta z)
            * Real.sqrt ((deriv (deriv f) z) ^ 2 * χ z / thEta z) := by
      rw [(Real.sqrt_sq_eq_abs (f z * χ z * deriv (deriv f) z)).symm, hsq,
        Real.sqrt_mul (hAz z hz)]
    exact le_of_eq hcalc
  have hCint : IntegrableOn (fun z : ℝ => f z * χ z * deriv (deriv f) z)
      (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) := by
    refine Integrable.mono' (hAint.add hBint) ((hmf.mul hmχ).mul hmf2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have h := hpt z hz
    rw [Real.norm_eq_abs]
    show |f z * χ z * deriv (deriv f) z| ≤ (f z) ^ 2 * χ z * thEta z
      + (deriv (deriv f) z) ^ 2 * χ z / thEta z
    have hsqA := Real.sq_sqrt (hAz z hz)
    have hsqB := Real.sq_sqrt (hBz z hz)
    have htwo : 2 * (Real.sqrt ((f z) ^ 2 * χ z * thEta z)
        * Real.sqrt ((deriv (deriv f) z) ^ 2 * χ z / thEta z))
        ≤ (f z) ^ 2 * χ z * thEta z + (deriv (deriv f) z) ^ 2 * χ z / thEta z := by
      nlinarith [sq_nonneg (Real.sqrt ((f z) ^ 2 * χ z * thEta z)
        - Real.sqrt ((deriv (deriv f) z) ^ 2 * χ z / thEta z)), hsqA, hsqB]
    linarith [h, htwo, abs_nonneg (f z * χ z * deriv (deriv f) z)]
  have h12 := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
    (s := Set.Ioo (0 : ℝ) (3 * Real.pi / 8))
    (A := fun z : ℝ => (f z) ^ 2 * χ z * thEta z)
    (B := fun z : ℝ => (deriv (deriv f) z) ^ 2 * χ z / thEta z)
    (C := fun z : ℝ => f z * χ z * deriv (deriv f) z)
    hAint hBint hCint hAz hBz hpt
  -- comparison with the two target energies
  have hAle : (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2 * χ z * thEta z)
      ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ := by
    have h1 : (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2 * χ z * thEta z)
        ≤ ∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2 * thEta z := by
      refine integral_mono_ae hAint (hA.mono_set (sub_three.trans Set.Ioo_subset_Icc_self)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hle : (f z) ^ 2 * χ z ≤ (f z) ^ 2 := by
        calc (f z) ^ 2 * χ z ≤ (f z) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left (hχle z) (sq_nonneg (f z))
          _ = (f z) ^ 2 := by ring
      exact mul_le_mul_of_nonneg_right hle (thEta_nonneg_Iθ (sub_three_Iθ hz))
    have h2 : (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2 * thEta z)
        ≤ ∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2), (f z) ^ 2 * thEta z :=
      setIntegral_mono_set (hA.mono_set Set.Ioo_subset_Icc_self)
        (Filter.Eventually.mono (ae_restrict_mem measurableSet_Ioo)
          (fun z hz => mul_nonneg (sq_nonneg _)
            (thEta_nonneg_Iθ ⟨le_of_lt hz.1, le_of_lt hz.2⟩)))
        (ae_of_all _ (fun z hz => sub_three hz))
    have h3 : (∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2), (f z) ^ 2 * thEta z)
        = ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ := by
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioo]
    linarith
  have hDle : (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8),
        (deriv (deriv f) z) ^ 2 * χ z / thEta z)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ := by
    have h1 : (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8),
          (deriv (deriv f) z) ^ 2 * χ z / thEta z)
        ≤ ∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (deriv (deriv f) z) ^ 2 := by
      refine integral_mono_ae hBint (hkk.mono_set sub_three) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hw1 : 1 ≤ thEta z := one_le_thEta_Ioo (sub_three hz)
      have hw0 : 0 < thEta z := thEta_pos_of_Ioo (sub_three hz)
      have hf2 : 0 ≤ (deriv (deriv f) z) ^ 2 := sq_nonneg _
      rw [div_le_iff₀ hw0]
      calc (deriv (deriv f) z) ^ 2 * χ z ≤ (deriv (deriv f) z) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (hχle z) hf2
        _ = (deriv (deriv f) z) ^ 2 := by ring
        _ = (deriv (deriv f) z) ^ 2 * 1 := by ring
        _ ≤ (deriv (deriv f) z) ^ 2 * thEta z := mul_le_mul_of_nonneg_left hw1 hf2
    have h2 : (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (deriv (deriv f) z) ^ 2)
        ≤ ∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv f) z) ^ 2 :=
      setIntegral_mono_set hkk (ae_of_all _ (fun z => sq_nonneg _))
        (ae_of_all _ (fun z hz => sub_three hz))
    have h3 : (∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv f) z) ^ 2)
        ≤ ∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv f) z) ^ 2 * thEta z := by
      refine integral_mono_ae hkk (hD.mono_set Set.Ioo_subset_Icc_self) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      calc (deriv (deriv f) z) ^ 2 = (deriv (deriv f) z) ^ 2 * 1 := by ring
        _ ≤ (deriv (deriv f) z) ^ 2 * thEta z :=
            mul_le_mul_of_nonneg_left (one_le_thEta_Ioo hz) (sq_nonneg _)
    have h4 : (∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv f) z) ^ 2 * thEta z)
        = ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ := by
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioo]
    linarith
  exact h12.trans (mul_le_mul (Real.sqrt_le_sqrt hAle) (Real.sqrt_le_sqrt hDle)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end

end Work.FTS.EllipticEst.Prop.TraceLeftCore
