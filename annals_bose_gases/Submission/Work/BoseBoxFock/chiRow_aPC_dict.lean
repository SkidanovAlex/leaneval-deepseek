import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotOf_chiMode_eq
import Submission.Work.BoseBoxFock.chiRowDefs
import Submission.Work.BoseBoxFock.chiRow_constPart_vanish
import Submission.Work.BoseBoxFock.chiTail_bound
import Submission.Work.BoseBoxFock.pin_e0_eq
import Submission.Work.BoseBoxFock.potChiLin_eq_summed_good
import Submission.Work.BoseBoxFock.potTruncRepair
import Submission.Work.BoseBoxFock.thetaExp_eq_etaOf_of_pairing
import Submission.Work.BoseBoxFock.thetaTail_bound
import Submission.Work.BoseBoxFock.wLoc_fibre_kernelCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A measurable, bounded complex function of the `i`-th slot of a configuration is integrable
over the cube `acube ℓ` (the cube has finite volume).

This is the integrability input of `integral_re` in the first row of the dictionary: the
`ℂ`-valued Bochner integral of a non-integrable function is `0` *by definition*, so without
integrability the identity `(aPC F).re = aP (re ∘ F)` would be false in general; the boundedness
hypothesis `hFC` is exactly what rules that out. -/
theorem chiRow_integrableOn_update_of_bounded {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {F : Work.BoseDict.Xn n → ℂ} (hFm : Measurable F) {C : ℝ} (hFC : ∀ x, ‖F x‖ ≤ C)
    (x : Work.BoseDict.Xn n) :
    IntegrableOn (fun y : Work.BoseDict.Sp => F (Function.update x i y))
      (Submission.BoseGases.acube ℓ) volume := by
  refine IntegrableOn.of_bound ?_ ?_ C ?_
  · exact Submission.BoseGases.acube_lt_top ℓ hℓ.le
  · exact ((hFm.comp (measurable_update x (a := i))).aestronglyMeasurable).restrict
  · exact ae_of_all _ (fun y => hFC _)

theorem chiRow_aPC_dict {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∀ (i : Fin n) {F : Work.BoseDict.Xn n → ℂ} (hFm : Measurable F)
        (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C),
        (fun x => (Work.BoseBoxFock.aPC ℓ i F x).re)
          = Submission.BoseGases.aP ℓ i (fun y => (F y).re))
      ∧ (∀ (i : Fin n) (Φ : Submission.BoseGases.X n → ℝ), ∀ x ∈ Submission.BoseGases.abox n ℓ,
          Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.boxRestrictC ℓ Φ) x
            = ((Submission.BoseGases.aP ℓ i Φ x : ℝ) : ℂ))
      ∧ (∀ (j : Fin n) {F G : EuclideanSpace ℝ (Fin 3) → ℂ},
          F =ᵐ[MeasureTheory.volume] G →
          (fun x : Work.BoseDict.Xn n => F (x j))
            =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
            (fun x : Work.BoseDict.Xn n => G (x j))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Row 1: the real part of the complex slot mean is the real slot mean.
    intro i F hFm hFb
    obtain ⟨C, hC⟩ := hFb
    funext x
    have hint : IntegrableOn (fun y : Work.BoseDict.Sp => F (Function.update x i y))
        (Submission.BoseGases.acube ℓ) volume :=
      chiRow_integrableOn_update_of_bounded hℓ i hFm hC x
    -- the real part of the `ℂ`-valued slot integral
    have hre : (∫ y in Submission.BoseGases.acube ℓ, F (Function.update x i y)).re
        = ∫ y in Submission.BoseGases.acube ℓ, (F (Function.update x i y)).re :=
      setIntegral_re_complex _ _ hint
    -- and the real factor `ℓ⁻³` pulls out of the real part
    have hmul : (((1 / ℓ ^ 3 : ℝ) : ℂ) * ∫ y in Submission.BoseGases.acube ℓ,
        F (Function.update x i y)).re
        = (1 / ℓ ^ 3) * (∫ y in Submission.BoseGases.acube ℓ,
            F (Function.update x i y)).re := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    unfold Work.BoseBoxFock.aPC Submission.BoseGases.aP
    rw [hmul, hre]
  · -- Row 2: on the box the restriction indicator is `1` on the whole slot domain.
    intro i Φ x hx
    have hcongr : (fun y : Work.BoseDict.Sp =>
          Work.BoseBoxFock.boxRestrictC ℓ Φ (Function.update x i y))
        =ᵐ[(volume : Measure Work.BoseDict.Sp).restrict (Submission.BoseGases.acube ℓ)]
        (fun y : Work.BoseDict.Sp => (((Φ (Function.update x i y)) : ℝ) : ℂ)) := by
      filter_upwards [self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)] with y hy
      simp only [Work.BoseBoxFock.boxRestrictC,
        Set.indicator_of_mem (Submission.BoseGases.update_mem_abox i hx hy), Complex.ofReal_one,
        mul_one]
    rw [Work.BoseBoxFock.aPC, integral_congr_ae hcongr, integral_complex_ofReal,
      ← Complex.ofReal_mul]
    rfl
  · -- Row 3: a one-particle identity transports to the `j`-th coordinate on the box.
    intro j F G hFG
    rw [Submission.BoseGases.restrict_abox_eq_pi]
    have h : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp).restrict
        (Submission.BoseGases.acube ℓ), F y = G y :=
      ae_mono MeasureTheory.Measure.restrict_le_self hFG
    have h2 : ∀ᵐ x ∂Measure.pi (fun _ : Fin n =>
        (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp).restrict
          (Submission.BoseGases.acube ℓ)), F (x j) = G (x j) :=
      (Measure.quasiMeasurePreserving_eval (μ := fun _ : Fin n =>
        (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp).restrict
          (Submission.BoseGases.acube ℓ)) j).ae h
    simpa only [Filter.EventuallyEq] using h2

end Work.BoseBoxFock
