import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.Honest

/-- The joint integrand `(z,θ) ↦ ofReal (sEta θ * Ψ z θ ^ 2)` is continuous on the open
quadrant `(0,∞) × (0,π/2)`: `hsm 0` supplies the continuity of `Ψ` there, `sin (2·)` is
strictly positive on `(0,π/2)`, so `sEta θ = sin (2θ) ^ (-η)` depends continuously on `θ`,
and `ENNReal.ofReal` is continuous. -/
theorem continuousOn_uncurry_sEta_mul_sq (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta p.2 * (Ψ p.1 p.2) ^ 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hΨ : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hsm 0).continuousOn
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    apply Continuous.continuousOn
    fun_prop
  have hne : ∀ p ∈ (Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)), Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    have h1 : 0 < 2 * p.2 := by linarith [hp.2.1]
    have h2 : 2 * p.2 < Real.pi := by linarith [hp.2.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have hsEta : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    simp only [Work.FTS.EllipticEst.sEta]
    exact hsin.rpow_const (fun p hp => Or.inl (hne p hp))
  exact ENNReal.continuous_ofReal.comp_continuousOn (hsEta.mul (hΨ.pow 2))

/-- The uncurried integrand of the slice `Σ`-linear form is a.e. strongly measurable for the
product of the restrictions of Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`; this is
`continuousOn_uncurry_sEta_mul_sq` transported along the a.e. equality
`Iz ×ˢ Iθ =ᵐ (0,∞) ×ˢ (0,π/2)`. -/
theorem aesm_uncurry_sEta_mul_sq (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta p.2 * (Ψ p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hQm : MeasurableSet (Set.Ioi (0:ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.FTS.EllipticEst.sEta p.2 * (Ψ p.1 p.2) ^ 2))
      ((volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :=
    (continuousOn_uncurry_sEta_mul_sq Ψ hsm).aestronglyMeasurable hQm
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0:ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0:ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact haesm

theorem aemeasurable_sliceSigmaLin (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (Ψ z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  refine AEMeasurable.lintegral_prod_right ?_
  exact (aesm_uncurry_sEta_mul_sq Ψ hsm).aemeasurable

end Work.FTS.EllipticEst.Honest
