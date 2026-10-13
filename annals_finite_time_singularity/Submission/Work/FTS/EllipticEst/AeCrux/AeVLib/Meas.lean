import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.HeavyFlat.Defs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.AeCrux

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

/-! ## 1. The exponential substitution for `∫⁻` -/

theorem lintegral_Ioi_exp (G : ℝ → ℝ≥0∞) :
    ∫⁻ z, G z ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))
      = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * G (Real.exp t) := by
  have himg : Real.exp '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
    simpa only [Set.image_univ] using Real.range_exp
  have h := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp)
    (f' := Real.exp) (s := Set.univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn G
  rw [himg] at h
  rw [show (∫⁻ z, G z ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))))
      = ∫⁻ z in Set.Ioi (0 : ℝ), G z from rfl, h]
  rw [MeasureTheory.setLIntegral_univ]
  exact lintegral_congr fun t => by rw [abs_of_pos (Real.exp_pos t)]

/-! ## 2. The strip substitution -/

theorem lintegral_box_exp {F : ℝ → ℝ → ℝ≥0∞}
    (hAE : AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ)))
    (hAE₂ : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2)
      ((volume : Measure ℝ) |>.prod (volume.restrict Iθ))) :
    ∫⁻ p, F p.1 p.2 ∂((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ))
      = ∫⁻ q, ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2
          ∂((volume : Measure ℝ) |>.prod (volume.restrict Iθ)) := by
  have h1 : ∫⁻ p, F p.1 p.2 ∂((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ))
      = ∫⁻ z, (∫⁻ θ, F z θ ∂(volume.restrict Iθ)) ∂(volume.restrict (Set.Ioi (0 : ℝ))) :=
    MeasureTheory.lintegral_prod _ hAE
  have h2 : ∫⁻ z, (∫⁻ θ, F z θ ∂(volume.restrict Iθ))
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))
      = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t)
          * (∫⁻ θ, F (Real.exp t) θ ∂(volume.restrict Iθ)) :=
    lintegral_Ioi_exp (fun z => ∫⁻ θ, F z θ ∂(volume.restrict Iθ))
  have h3 : ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t)
        * (∫⁻ θ, F (Real.exp t) θ ∂(volume.restrict Iθ))
      = ∫⁻ t : ℝ, ∫⁻ θ, ENNReal.ofReal (Real.exp t) * F (Real.exp t) θ
          ∂(volume.restrict Iθ) := by
    refine lintegral_congr fun t => ?_
    exact (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  have h4 : ∫⁻ t : ℝ, ∫⁻ θ, ENNReal.ofReal (Real.exp t) * F (Real.exp t) θ
        ∂(volume.restrict Iθ)
      = ∫⁻ q, ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2
          ∂((volume : Measure ℝ) |>.prod (volume.restrict Iθ)) := by
    rw [MeasureTheory.lintegral_prod (f := fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2) hAE₂]
  rw [h1, h2, h3, h4]

/-! ## 3. The level-zero `HkIntegrand` -/

theorem HkIntegrand_zero (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Finset.sum_range_succ, Finset.sum_range_zero,
    Work.Spaces.DzIter_zero, zero_add, add_zero]
  norm_num

theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    have hη : 0 ≤ Work.Spaces.eta / 2 := by linarith [Work.Spaces.eta_pos]
    rw [sq, ← Real.rpow_add_of_nonneg hs hη hη,
      show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta by ring]
  rw [HkIntegrand_zero, mul_pow, div_pow, h1,
    Work.FTS.EllipticEst.sEta, div_eq_mul_inv, ← Real.rpow_neg hs]
  ring

/-! ## 4. Joint measurability on `univ × Iθ` -/

theorem aesm_prod_univ_Iθ {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => f q.1 q.2)
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) := by
  have hθ : Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : ((Set.univ : Set ℝ) ×ˢ Iθ : Set (ℝ × ℝ))
      =ᵐ[volume.prod volume] ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) hθ
  rw [show MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)
      = MeasureTheory.Measure.prod ((volume : Measure ℝ).restrict (Set.univ : Set ℝ))
          (volume.restrict Iθ) from by
    rw [Measure.restrict_univ]]
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact hf.aestronglyMeasurable (MeasurableSet.univ.prod isOpen_Ioo.measurableSet)

/-! ## 6. Continuity of the slot integrands -/

theorem continuousOn_slot {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.sEta p.2) ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)), 0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hs : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
        = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by funext p; rfl
    rw [hfun]
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  exact ((hf.pow 2).mul (hw.pow 2)).mul hs

theorem continuousOn_slotT {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
      * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)), 0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hΩ : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.HeavyFlat.omw p.1)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.FTS.EllSol.HeavyFlat.omw p.1)
        = fun p : ℝ × ℝ => (1 + Real.exp p.1) ^ 4 * Real.exp (-(3 * p.1)) := by funext p; rfl
    rw [hfun]
    exact ((continuousOn_const.add
        ((Real.continuous_exp.comp continuous_fst).continuousOn)).pow 4).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_fst).neg).continuousOn)
  have hs : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
        = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by funext p; rfl
    rw [hfun]
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  exact ((hg.pow 2).mul hΩ).mul hs


end Work.FTS.EllipticEst.AeCrux
