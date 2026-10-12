import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.aPCPairAlg
import Submission.Work.BoseBoxFock.chiRowDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- **The real part of the box-restricted pairing.**

`cIPn d Θ G = ∫_x conj(Θ x)·G x` is the complex `L²` pairing of the box restriction
`Θ = boxRestrictC ℓ Φ = Φ·1_{abox d ℓ}` with `G`.  Because `Θ` is real-valued and supported in the
box, the real part of the pairing collapses to the integral of `Φ·Re G` over the box alone:

    Re cIPn d (Φ·1_{abox}) G = ∫_{abox d ℓ} Φ x · Re (G x) .

The analytic content is (i) the integrand is *integrable* — `Φ` is continuous, hence bounded on the
compact box, `G` is bounded and the box has finite volume — so that `Re` may be moved inside the
Bochner integral (`ContinuousLinearMap.integral_comp_comm` for `Complex.reCLM`), and (ii) the
pointwise computation `Re (conj(Φ x) · G x) = Φ x·Re(G x)` on the box and `0` off it. -/
theorem re_cIPn_boxRestrict {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X d → ℝ} {G : Submission.BoseGases.X d → ℂ} (hΦc : Continuous Φ)
    (hGm : Measurable G) (hGb : ∃ C : ℝ, ∀ x : Submission.BoseGases.X d, ‖G x‖ ≤ C) :
    (Work.BoseDict.cIPn d (Work.BoseBoxFock.boxRestrictC ℓ Φ) G).re
      = ∫ x in Submission.BoseGases.abox d ℓ, Φ x * (G x).re := by
  classical
  have hs : MeasurableSet (Submission.BoseGases.abox d ℓ) :=
    Submission.BoseGases.abox_measurable d ℓ
  -- the two values of the box restriction, on and off the box
  have hbrOfMem : ∀ x : Submission.BoseGases.X d, x ∈ Submission.BoseGases.abox d ℓ →
      Work.BoseBoxFock.boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) := by
    intro x hx
    dsimp only [Work.BoseBoxFock.boxRestrictC]
    rw [Set.indicator_of_mem hx (fun _ => (1 : ℝ))]
    simp
  have hbrOfNotMem : ∀ x : Submission.BoseGases.X d, x ∉ Submission.BoseGases.abox d ℓ →
      Work.BoseBoxFock.boxRestrictC ℓ Φ x = 0 := by
    intro x hx
    dsimp only [Work.BoseBoxFock.boxRestrictC]
    rw [Set.indicator_of_notMem hx (fun _ => (1 : ℝ))]
    simp
  -- the box restriction is real-valued, so `star` acts trivially on it
  have hstar : ∀ x : Submission.BoseGases.X d,
      star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) = Work.BoseBoxFock.boxRestrictC ℓ Φ x := by
    intro x
    by_cases hx : x ∈ Submission.BoseGases.abox d ℓ
    · rw [hbrOfMem x hx, Complex.star_def, Complex.conj_ofReal]
    · rw [hbrOfNotMem x hx, star_zero]
  have hbrm : Measurable (Work.BoseBoxFock.boxRestrictC ℓ Φ) := by
    apply Measurable.mul
    · exact Complex.continuous_ofReal.measurable.comp hΦc.measurable
    · exact Complex.continuous_ofReal.measurable.comp
        (Measurable.indicator measurable_const hs)
  have hF_eq : (fun x : Submission.BoseGases.X d =>
        star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) * G x)
      = fun x => Work.BoseBoxFock.boxRestrictC ℓ Φ x * G x := by
    funext x; rw [hstar x]
  -- the pointwise value of the real part of the integrand
  have hpt : ∀ x : Submission.BoseGases.X d,
      (star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) * G x).re
        = (Submission.BoseGases.abox d ℓ).indicator (fun y => Φ y * (G y).re) x := by
    intro x
    rw [hstar x]
    by_cases hx : x ∈ Submission.BoseGases.abox d ℓ
    · rw [Set.indicator_of_mem hx, hbrOfMem x hx, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    · rw [Set.indicator_of_notMem hx (fun y => Φ y * (G y).re), hbrOfNotMem x hx, zero_mul,
        Complex.zero_re]
  -- boundedness of `Φ` on the compact box, and of `G` everywhere
  obtain ⟨Cg, hCg⟩ := hGb
  obtain ⟨M, hM⟩ := (Submission.BoseGases.abox_compact d hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  have hInt_g : Integrable
      ((Submission.BoseGases.abox d ℓ).indicator (fun _ : Submission.BoseGases.X d =>
        (max M 0 * max Cg 0 : ℝ))) volume :=
    (integrable_indicator_iff hs).mpr
      (ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact d hℓ)
        continuousOn_const)
  -- integrability of the pairing integrand (dominated by the bounded majorant above)
  have hFint : Integrable
      (fun x : Submission.BoseGases.X d => star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) * G x)
      volume := by
    rw [hF_eq]
    refine hInt_g.mono' ((hbrm.mul hGm).aestronglyMeasurable) (Filter.Eventually.of_forall ?_)
    intro x
    by_cases hx : x ∈ Submission.BoseGases.abox d ℓ
    · rw [Set.indicator_of_mem hx, hbrOfMem x hx, norm_mul, Complex.norm_real]
      exact mul_le_mul (le_trans (hM x hx) (le_max_left M 0))
        (le_trans (hCg x) (le_max_left Cg 0)) (norm_nonneg _) (le_max_right M 0)
    · rw [Set.indicator_of_notMem hx (fun _ => (max M 0 * max Cg 0 : ℝ)), hbrOfNotMem x hx,
        zero_mul, norm_zero]
  -- `Re` commutes with the Bochner integral
  have hstep1 : (∫ x : Submission.BoseGases.X d,
        star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) * G x).re
      = ∫ x : Submission.BoseGases.X d,
          (star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) * G x).re := by
    simpa only [Complex.reCLM_apply] using
      (ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) Complex.reCLM hFint).symm
  have hstep2 : (∫ x : Submission.BoseGases.X d,
        (star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) * G x).re)
      = ∫ x : Submission.BoseGases.X d,
          (Submission.BoseGases.abox d ℓ).indicator (fun y => Φ y * (G y).re) x :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hstep3 : (∫ x : Submission.BoseGases.X d,
        (Submission.BoseGases.abox d ℓ).indicator (fun y => Φ y * (G y).re) x)
      = ∫ x in Submission.BoseGases.abox d ℓ, Φ x * (G x).re :=
    integral_indicator hs
  have hstart : Work.BoseDict.cIPn d (Work.BoseBoxFock.boxRestrictC ℓ Φ) G
      = ∫ x : Submission.BoseGases.X d,
          star (Work.BoseBoxFock.boxRestrictC ℓ Φ x) * G x := rfl
  rw [hstart, hstep1, hstep2, hstep3]

end Work.BoseBoxFock
