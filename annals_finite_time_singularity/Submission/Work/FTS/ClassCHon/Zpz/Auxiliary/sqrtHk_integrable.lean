import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.H2W.ShiftC.integrableOn_sinCos2_pzIter2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz.Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## Elementary helpers -/

/-- `√a ≤ a + 1` for every `a ≥ 0`. -/
theorem sqrtHk_sqrt_le_add_one (a : ℝ) (ha : 0 ≤ a) : Real.sqrt a ≤ a + 1 := by
  rw [Real.sqrt_le_iff]
  exact ⟨by linarith, by nlinarith [sq_nonneg a]⟩

/-- The angular interval has finite Lebesgue measure. -/
theorem sqrtHk_volume_Iθ_ne_top : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- The constant `1` is integrable on the angular interval. -/
theorem sqrtHk_integrableOn_one_Iθ :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := by
  refine MeasureTheory.integrableOn_const ?_ ?_
  · exact sqrtHk_volume_Iθ_ne_top
  · simp

/-- A function of `ℝ × ℝ` continuous on the open quadrant is a.e. strongly measurable for the
product of the restrictions of Lebesgue measure to the box `Icc a b` (with `0 < a`) and to the
angular interval.  (The counterpart of `Work.Spaces.aesm_of_continuousOn_Qd` for a bounded
radial box.) -/
theorem sqrtHk_aesm_of_continuousOn_Qd_box {g : ℝ × ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (ha : 0 < a) :
    AEStronglyMeasurable g
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hbig : AEStronglyMeasurable g
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  exact hbig.mono_measure
    (MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono
        (fun x hx => le_trans (le_of_lt ha) hx.1) le_rfl) le_rfl)

/-! ## The main statement -/

theorem sqrtHk_integrable {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 2 F) :
    (∀ τ : ℝ, 0 ≤ τ → MeasureTheory.IntegrableOn
        (fun θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)) Work.Spaces.Iθ) ∧
      (∀ a b : ℝ, 0 < a → MeasureTheory.IntegrableOn
        (fun τ : ℝ => ∫ θ in Work.Spaces.Iθ,
          Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)) (Set.Icc a b)) := by
  -- ### Angular integrability, for every `τ ∈ Iz`.
  have hslice : ∀ τ : ℝ, 0 ≤ τ → IntegrableOn
      (fun θ : ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ)) Work.Spaces.Iθ := by
    intro τ hτ
    refine MeasureTheory.Integrable.mono' ((hF.1 τ hτ).add sqrtHk_integrableOn_one_Iθ) ?_ ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable
        (hF.1 τ hτ).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun θ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact sqrtHk_sqrt_le_add_one _ (Work.Spaces.HkIntegrand_nonneg α 2 F τ θ)
  refine ⟨hslice, ?_⟩
  -- ### Radial integrability on a box `[a,b]`, `a > 0`.
  intro a b ha
  -- The uncurried integrand is continuous on the open quadrant, hence a.e. strongly
  -- measurable for the product measure on the box.
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F p.1 p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h2 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 2 F p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hsm.continuousOn_HkIntegrand α 2
    have h3 := Real.continuous_sqrt.continuousOn.comp h2
      (fun p _ => Set.mem_univ _)
    simpa only [Function.comp_def] using h3
  have haesm_uncurry : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 2 F p.1 p.2))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    sqrtHk_aesm_of_continuousOn_Qd_box hcont ha
  have haesm : AEStronglyMeasurable
      (fun τ : ℝ => ∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ))
      (volume.restrict (Set.Icc a b)) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' haesm_uncurry
  -- The integrable majorant `A(τ) + ∫_{Iθ} 1`.
  have hA : IntegrableOn
      (fun τ : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F τ θ)
      (Set.Icc a b) :=
    (show IntegrableOn
        (fun τ : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F τ θ)
        Work.Spaces.Iz from hF.2).mono_set
      (fun x (hx : x ∈ Set.Icc a b) => le_trans (le_of_lt ha) hx.1)
  have hC : IntegrableOn
      (fun _ : ℝ => ∫ θ in Work.Spaces.Iθ, (1 : ℝ)) (Set.Icc a b) := by
    rw [MeasureTheory.IntegrableOn]
    refine MeasureTheory.integrable_const_iff.mpr (Or.inr ?_)
    rw [MeasureTheory.isFiniteMeasure_restrict, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hdom : IntegrableOn
      (fun τ : ℝ => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F τ θ)
        + ∫ θ in Work.Spaces.Iθ, (1 : ℝ)) (Set.Icc a b) :=
    hA.add hC
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  -- The pointwise (a.e.) bound.
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun τ hτ => ?_
  have hτ0 : 0 ≤ τ := le_trans (le_of_lt ha) hτ.1
  have hI : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 2 F τ θ) Work.Spaces.Iθ :=
    hF.1 τ hτ0
  have hsum : IntegrableOn
      (fun θ : ℝ => Work.Spaces.HkIntegrand α 2 F τ θ + 1) Work.Spaces.Iθ :=
    hI.add sqrtHk_integrableOn_one_Iθ
  have hmono : (∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ))
      ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 2 F τ θ + 1) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Real.sqrt_nonneg _) hsum
      (Filter.Eventually.of_forall fun θ =>
        sqrtHk_sqrt_le_add_one _ (Work.Spaces.HkIntegrand_nonneg α 2 F τ θ))
  have hsplit : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 2 F τ θ + 1))
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F τ θ)
        + ∫ θ in Work.Spaces.Iθ, (1 : ℝ) :=
    MeasureTheory.integral_add hI sqrtHk_integrableOn_one_Iθ
  rw [Real.norm_eq_abs,
    abs_of_nonneg (MeasureTheory.integral_nonneg fun θ => Real.sqrt_nonneg _)]
  exact hmono.trans_eq hsplit

end

end Work.FTS.ClassCHon.Zpz.Aux
