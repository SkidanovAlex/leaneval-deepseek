import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.derivIntegrableOfEnergy
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
import Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.Basic
import Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.Ibp
import Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.Cs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `F₀ L₀` bound `F₀ L₀ ≤ (K/2) A + √(A D)`
-/

namespace Work.FTS.EllipticEst.Prop.TraceLeftCore

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ### Comparison of the plain `L²`-integrals with the weighted energies -/

theorem fsq_le_energy (f : ℝ → ℝ)
    (hA : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hii : IntegrableOn (fun θ : ℝ => (f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2))) :
    (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ := by
  have hs : Set.Ioo (0 : ℝ) (3 * Real.pi / 8) ⊆ Work.Spaces.Iθ := sub_three_Iθ
  have h1 : (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2)
      ≤ ∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2 * thEta z := by
    refine integral_mono_ae (hii.mono_set sub_three) (hA.mono_set hs) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hw : 1 ≤ thEta z := one_le_thEta_Ioo (sub_three hz)
    calc (f z) ^ 2 = (f z) ^ 2 * 1 := by ring
      _ ≤ (f z) ^ 2 * thEta z := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
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

/-! ### The `F₀ L₀` bound -/

theorem prodTraceBound (f χ : ℝ → ℝ) {K F₀ L₀ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hχ : ∀ θ : ℝ, HasDerivAt χ (deriv χ θ) θ)
    (hχ2 : ∀ θ : ℝ, HasDerivAt (deriv χ) (deriv (deriv χ) θ) θ)
    (hχ1 : ∀ θ : ℝ, θ ≤ Real.pi / 4 → χ θ = 1)
    (hχ0 : ∀ θ : ℝ, 3 * Real.pi / 8 ≤ θ → χ θ = 0)
    (hχ1' : ∀ θ : ℝ, θ ≤ Real.pi / 4 → deriv χ θ = 0)
    (hχ0' : ∀ θ : ℝ, 3 * Real.pi / 8 ≤ θ → deriv χ θ = 0)
    (hχnn : ∀ θ : ℝ, 0 ≤ χ θ)
    (hχle : ∀ θ : ℝ, χ θ ≤ 1)
    (hχK : ∀ θ : ℝ, |deriv χ θ| ≤ K)
    (hχK2 : ∀ θ : ℝ, |deriv (deriv χ) θ| ≤ K)
    (hK0 : 0 ≤ K)
    (hχcont2 : Continuous (deriv (deriv χ)))
    (hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 F₀))
    (hlimL : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) (𝓝 L₀))
    (hA : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hD : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * thEta θ) Work.Spaces.Iθ)
    (hii : IntegrableOn (fun θ : ℝ => (f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)))
    (hjj : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)))
    (hkk : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)))
    (h12 : IntegrableOn (fun θ : ℝ => f θ * deriv f θ) (Set.Ioo 0 (Real.pi / 2)))
    (h23 : IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ) (Set.Ioo 0 (Real.pi / 2))) :
    F₀ * L₀ ≤ (K / 2) * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
      + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ)) := by
  have hχcont : Continuous χ := continuous_iff_continuousAt.mpr (fun θ => (hχ θ).continuousAt)
  have hdχcont : Continuous (deriv χ) :=
    continuous_iff_continuousAt.mpr (fun θ => (hχ2 θ).continuousAt)
  have hcont : ContinuousOn f (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) := hf.continuousOn.mono sub_three
  have hcont1 : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) :=
    ((hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).continuousOn).mono sub_three
  have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) :=
    ((hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (le_refl 1)).mono sub_three
  have hm1 : AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hm2 : AEStronglyMeasurable (deriv f)
      (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hcont1.aestronglyMeasurable measurableSet_Ioo
  have hm3 : AEStronglyMeasurable (deriv (deriv f))
      (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hcont2.aestronglyMeasurable measurableSet_Ioo
  have hmχ : AEStronglyMeasurable χ (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hχcont.aestronglyMeasurable
  have hmdχ : AEStronglyMeasurable (deriv χ)
      (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hdχcont.aestronglyMeasurable
  have hmd2χ : AEStronglyMeasurable (deriv (deriv χ))
      (volume.restrict (Set.Ioo (0 : ℝ) (3 * Real.pi / 8))) :=
    hχcont2.aestronglyMeasurable
  -- the four interval-integrability facts
  have hintA : IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2 * χ θ) volume 0
      (3 * Real.pi / 8) := by
    refine intervalIntegrable_of_integrableOn_Ioo (by positivity) ?_
    refine Integrable.mono' (hjj.mono_set sub_three) ((hm2.pow 2).mul hmχ) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hχnn z))]
    calc (deriv f z) ^ 2 * χ z ≤ (deriv f z) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (hχle z) (sq_nonneg _)
      _ = (deriv f z) ^ 2 := by ring
  have hintB : IntervalIntegrable (fun θ : ℝ => f θ * deriv χ θ * deriv f θ) volume 0
      (3 * Real.pi / 8) := by
    refine intervalIntegrable_of_integrableOn_Ioo (by positivity) ?_
    have hbd : IntegrableOn (fun z : ℝ => K * ((f z) ^ 2 + (deriv f z) ^ 2))
        (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) :=
      ((hii.mono_set sub_three).add (hjj.mono_set sub_three)).const_mul K
    refine Integrable.mono' hbd ((hm1.mul hmdχ).mul hm2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 : |f z| * |deriv f z| ≤ (f z) ^ 2 + (deriv f z) ^ 2 := by
      nlinarith [sq_abs (f z), sq_abs (deriv f z), sq_nonneg (|f z| - |deriv f z|),
        abs_nonneg (f z), abs_nonneg (deriv f z)]
    nlinarith [h1, abs_nonneg (deriv χ z), hχK z, abs_nonneg (f z),
      abs_nonneg (deriv f z)]
  have hintB' : IntervalIntegrable (fun θ : ℝ => f θ * deriv f θ * deriv χ θ) volume 0
      (3 * Real.pi / 8) := by
    have hcongr : (fun θ : ℝ => f θ * deriv χ θ * deriv f θ)
        = fun θ : ℝ => f θ * deriv f θ * deriv χ θ := by
      funext θ; ring
    rw [hcongr] at hintB
    exact hintB
  have hintC : IntervalIntegrable (fun θ : ℝ => f θ * χ θ * deriv (deriv f) θ) volume 0
      (3 * Real.pi / 8) := by
    refine intervalIntegrable_of_integrableOn_Ioo (by positivity) ?_
    have hbd : IntegrableOn (fun z : ℝ => (f z) ^ 2 + (deriv (deriv f) z) ^ 2)
        (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) :=
      (hii.mono_set sub_three).add (hkk.mono_set sub_three)
    refine Integrable.mono' hbd ((hm1.mul hmχ).mul hm3) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hχnn z)]
    have h1 : |f z| * |deriv (deriv f) z| ≤ (f z) ^ 2 + (deriv (deriv f) z) ^ 2 := by
      nlinarith [sq_abs (f z), sq_abs (deriv (deriv f) z),
        sq_nonneg (|f z| - |deriv (deriv f) z|), abs_nonneg (f z),
        abs_nonneg (deriv (deriv f) z)]
    nlinarith [h1, hχle z, abs_nonneg (f z), abs_nonneg (deriv (deriv f) z), hχnn z]
  have hintB2 : IntervalIntegrable (fun θ : ℝ => (f θ) ^ 2 * deriv (deriv χ) θ) volume 0
      (3 * Real.pi / 8) := by
    refine intervalIntegrable_of_integrableOn_Ioo (by positivity) ?_
    refine Integrable.mono' ((hii.mono_set sub_three).const_mul K)
      ((hm1.pow 2).mul hmd2χ) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc (f z) ^ 2 * |deriv (deriv χ) z| ≤ (f z) ^ 2 * K :=
          mul_le_mul_of_nonneg_left (hχK2 z) (sq_nonneg _)
      _ = K * (f z) ^ 2 := by ring
  -- the three ingredients
  have h1 := cutoff_ibp f χ hf hχ hχ1 hχ0 hlim hlimL ((hintA.add hintB).add hintC)
  have h2 := cutoff_ibp_cross f χ hf hχ2 hχ1' hχ0' hintB' hintB2
  have h3 := cutoff_cs f χ hf hχcont hχnn hχle hA hD hkk
  -- the non-negativity of the first slot
  have hIA : (0 : ℝ) ≤ ∫ θ in (0 : ℝ)..(3 * Real.pi / 8), (deriv f θ) ^ 2 * χ θ :=
    intervalIntegral.integral_nonneg (by positivity)
      (fun u _ => mul_nonneg (sq_nonneg _) (hχnn u))
  -- the bound on the `χ''`-slot
  have hIB2 : (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), (f θ) ^ 2 * deriv (deriv χ) θ)
      ≤ K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ) := by
    rw [intervalIntegral_three]
    have hint1 : IntegrableOn (fun z : ℝ => (f z) ^ 2 * deriv (deriv χ) z)
        (Set.Ioo (0 : ℝ) (3 * Real.pi / 8)) := by
      refine Integrable.mono' ((hii.mono_set sub_three).const_mul K) ((hm1.pow 2).mul hmd2χ) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc (f z) ^ 2 * |deriv (deriv χ) z| ≤ (f z) ^ 2 * K :=
            mul_le_mul_of_nonneg_left (hχK2 z) (sq_nonneg _)
        _ = K * (f z) ^ 2 := by ring
    have hstep1 : (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2 * deriv (deriv χ) z)
        ≤ ∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), K * (f z) ^ 2 :=
      integral_mono_ae hint1 ((hii.mono_set sub_three).const_mul K)
        (ae_of_all _ (fun z => by
          calc (f z) ^ 2 * deriv (deriv χ) z ≤ (f z) ^ 2 * |deriv (deriv χ) z| :=
                mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
            _ ≤ (f z) ^ 2 * K := mul_le_mul_of_nonneg_left (hχK2 z) (sq_nonneg _)
            _ = K * (f z) ^ 2 := by ring))
    have hstep2 : (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), K * (f z) ^ 2)
        = K * (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2) := by
      rw [MeasureTheory.integral_const_mul]
    have hstep3 : (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ :=
      fsq_le_energy f hA hii
    calc (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2 * deriv (deriv χ) z)
        ≤ K * (∫ z in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), (f z) ^ 2) := by
          rw [← hstep2]; exact hstep1
      _ ≤ K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ) :=
          mul_le_mul_of_nonneg_left hstep3 hK0
  -- the bound on the `f χ f''`-slot
  have hIC : |∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * χ θ * deriv (deriv f) θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ) := by
    rw [intervalIntegral_three]
    exact h3
  -- assemble
  have hsplit : (∫ θ in (0 : ℝ)..(3 * Real.pi / 8),
        ((deriv f θ) ^ 2 * χ θ + f θ * deriv χ θ * deriv f θ
          + f θ * χ θ * deriv (deriv f) θ))
      = (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), (deriv f θ) ^ 2 * χ θ)
        + (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * deriv χ θ * deriv f θ)
        + (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * χ θ * deriv (deriv f) θ) := by
    rw [intervalIntegral.integral_add (hintA.add hintB) hintC,
      intervalIntegral.integral_add hintA hintB]
  have h1' : F₀ * L₀ = -((∫ θ in (0 : ℝ)..(3 * Real.pi / 8), (deriv f θ) ^ 2 * χ θ)
      + (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * deriv χ θ * deriv f θ)
      + (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * χ θ * deriv (deriv f) θ)) := by
    rw [← hsplit]
    exact h1
  have hIB : (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * deriv χ θ * deriv f θ)
      = -(1 / 2) * (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), (f θ) ^ 2 * deriv (deriv χ) θ) := by
    have hcongr : (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * deriv f θ * deriv χ θ)
        = (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * deriv χ θ * deriv f θ) :=
      intervalIntegral.integral_congr (fun θ _ => by ring)
    rw [hcongr] at h2
    exact h2
  have hfinal : F₀ * L₀
      ≤ (1 / 2) * (K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ))
        + |∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * χ θ * deriv (deriv f) θ| := by
    rw [h1', hIB]
    have hhalf : (1 / 2) * (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), (f θ) ^ 2 * deriv (deriv χ) θ)
        ≤ (1 / 2) * (K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)) :=
      mul_le_mul_of_nonneg_left hIB2 (by norm_num)
    have hc : -(∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * χ θ * deriv (deriv f) θ)
        ≤ |∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * χ θ * deriv (deriv f) θ| :=
      neg_le_abs _
    linarith [hhalf, hIA, hc]
  have hlast : (1 / 2) * (K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ))
        + |∫ θ in (0 : ℝ)..(3 * Real.pi / 8), f θ * χ θ * deriv (deriv f) θ|
      ≤ (K / 2) * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
        + Real.sqrt (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ) := by
    have hK2 : (1 / 2) * (K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ))
        = (K / 2) * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ) := by ring
    rw [hK2]
    linarith [hIC]
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact measurableSet_Icc
  have hA0 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ :=
    MeasureTheory.setIntegral_nonneg hIθmeas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg_Iθ hθ))
  have hsqrtA : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ)
      = Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * thEta θ)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * thEta θ)) :=
    (Real.sqrt_mul hA0 _).symm
  rw [hsqrtA] at hlast
  exact hfinal.trans hlast

end

end Work.FTS.EllipticEst.Prop.TraceLeftCore
