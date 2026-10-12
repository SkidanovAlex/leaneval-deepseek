import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseKinLoc.Momentum.boxFTfun_kinFT
import Submission.Work.BoseKinLoc.Momentum.integrable_norm_sq_PsiC
import Submission.Work.BoseKinLoc.Momentum.setIntegral_bsBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.integrable_statU_sq_alt`

Port of `integrable_statU_sq` (FS `eq:Q1Qslide`): for `ℓ > 0`, `p ∈ ℝ³` and `ψ` smooth and
compactly supported, the sliding localised Fourier amplitude

  `u ↦ ‖kinFT (statU ℓ u ψ) p‖²`

is integrable on `ℝ³`.

The route is the pointwise identity of `eq:Q1Qslide`,

  `kinFT (statU ℓ u ψ) p = exp(-iℓ⟪p,u⟫) · PsiC ℓ p ψ (ℓ•u)`

(proved here as the `private` lemma `kinFT_statU_aux`, since the module
`Submission.Work.BoseKinLoc.Momentum.kinFT_statU_alt` carrying the same identity has not landed
with a complete proof yet), followed by `(integrable_norm_sq_PsiC ℓ p ψ hψ hcs).comp_smul (ne_of_gt hℓ)` — the
unconditional change of variables `u ↦ ℓ • u`, whose Jacobian is irrelevant for integrability.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option autoImplicit false

private lemma measurableSet_bsBox_aux (ℓ : ℝ) (u : ℝ³) :
    MeasurableSet (Work.BSKinetic.bsBox ℓ u) := by
  have h : Work.BSKinetic.bsBox ℓ u = (fun x : ℝ³ => x - ℓ • u) ⁻¹' acube ℓ := rfl
  rw [h]
  exact (acube_measurable ℓ).preimage (by fun_prop)

private lemma setIntegral_eq_indicator_aux {s : Set ℝ³} (hs : MeasurableSet s) (f : ℝ³ → ℂ) :
    (∫ x in s, f x) = ∫ x, s.indicator f x := (MeasureTheory.integral_indicator hs).symm

private lemma setIntegral_sub_aux {s : Set ℝ³} (hs : MeasurableSet s) {f g : ℝ³ → ℂ}
    (hf : IntegrableOn f s) (hg : IntegrableOn g s) :
    (∫ x in s, (f x - g x)) = (∫ x in s, f x) - ∫ x in s, g x := by
  rw [setIntegral_eq_indicator_aux hs f, setIntegral_eq_indicator_aux hs g,
    setIntegral_eq_indicator_aux hs (fun x => f x - g x)]
  rw [← MeasureTheory.integral_sub ((MeasureTheory.integrable_indicator_iff hs).mpr hf)
    ((MeasureTheory.integrable_indicator_iff hs).mpr hg)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, sub_self]

private lemma setIntegral_const_mul_aux (s : Set ℝ³) (c : ℂ) (f : ℝ³ → ℂ) :
    (∫ x in s, c * f x) = c * ∫ x in s, f x :=
  MeasureTheory.integral_const_mul c f

private lemma setIntegral_mul_const_aux (s : Set ℝ³) (c : ℂ) (f : ℝ³ → ℂ) :
    (∫ x in s, f x * c) = (∫ x in s, f x) * c :=
  MeasureTheory.integral_mul_const c f

/-- The `exp`-phase splits off the translation `ℓ • u` of the sliding box. -/
private lemma hphase_aux (ℓ : ℝ) (u p : ℝ³) (z : ℝ³) :
    Complex.exp (-(Complex.I * (inner ℝ p (ℓ • u + z) : ℂ)))
      = Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  rw [inner_add_right, inner_smul_right]
  push_cast
  ring

private lemma boxFTfun_eq_integral_aux (ℓ : ℝ) (p : ℝ³) (ψ : ℝ³ → ℝ) (u : ℝ³) :
    boxFTfun ℓ p ψ (ℓ • u)
      = ∫ z in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (ℓ • u + z) : ℂ) :=
  rfl

/-- FS `eq:Q1Qslide`, pointwise in `u`: the Fourier amplitude of the sliding localised
mean-free state is the phase times `PsiC` evaluated at the centre of the sliding box. -/
private lemma kinFT_statU_aux (ℓ : ℝ) (hℓ : 0 < ℓ) (u : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (p : ℝ³) :
    kinFT (statU ℓ u ψ) p
      = Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ))) * PsiC ℓ p ψ (ℓ • u) := by
  set m : ℝ := Work.BSKinetic.bsMean ℓ u ψ with hm
  have hψc : Continuous ψ := hψ.continuous
  have hcont1 : Continuous (fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (ℓ • u + z) : ℂ)) := by fun_prop
  have hcont2 : Continuous (fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (m : ℂ)) := by fun_prop
  have hs : MeasurableSet (Work.BSKinetic.bsBox ℓ u) := measurableSet_bsBox_aux ℓ u
  have hred : kinFT (statU ℓ u ψ) p
      = ∫ x in Work.BSKinetic.bsBox ℓ u,
          Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * ((ψ x - m : ℝ) : ℂ) := by
    rw [kinFT]
    rw [show (fun x : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * statU ℓ u ψ x)
        = (Work.BSKinetic.bsBox ℓ u).indicator
            (fun x => Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * ((ψ x - m : ℝ) : ℂ)) from by
      funext x
      simp only [statU, Work.BoseKinLoc.indU, Work.BoseKinLoc.lamBox, Work.BoseKinLoc.Qfree,
        Work.BSKinetic.bsQ]
      by_cases hx : x ∈ Work.BSKinetic.bsBox ℓ u
      · simp only [Set.indicator_of_mem hx]; push_cast; ring
      · simp only [Set.indicator_of_notMem hx]; simp]
    rw [MeasureTheory.integral_indicator hs]
  rw [hred, setIntegral_bsBox]
  rw [show (∫ z in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ p (ℓ • u + z) : ℂ))) * ((ψ (ℓ • u + z) - m : ℝ) : ℂ))
      = ∫ z in acube ℓ, Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          * (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((ψ (ℓ • u + z) - m : ℝ) : ℂ)) from by
    apply MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ)
    intro z _
    dsimp only
    rw [hphase_aux ℓ u p z]; ring]
  rw [setIntegral_const_mul_aux]
  rw [show (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((ψ (ℓ • u + z) - m : ℝ) : ℂ))
      = fun z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (ℓ • u + z) : ℂ)
          - Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (m : ℂ) from by
    funext z; push_cast; ring]
  rw [setIntegral_sub_aux (acube_measurable ℓ)
    (ContinuousOn.integrableOn_compact (acube_compact hℓ) hcont1.continuousOn)
    (ContinuousOn.integrableOn_compact (acube_compact hℓ) hcont2.continuousOn)]
  rw [setIntegral_mul_const_aux, integral_exp_acube]
  rw [show (m : ℂ) = (boxMeanR ℓ ψ (ℓ • u) : ℂ) from by rw [hm]; rfl]
  rw [PsiC, boxFTfun_eq_integral_aux]
  ring

theorem integrable_statU_sq_alt (ℓ : ℝ) (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Momentum.statU ℓ u ψ) p‖ ^ 2) := by
  have hpt : (fun u : ℝ³ => ‖kinFT (statU ℓ u ψ) p‖ ^ 2)
      = fun u : ℝ³ => ‖PsiC ℓ p ψ (ℓ • u)‖ ^ 2 := by
    funext u
    rw [kinFT_statU_aux ℓ hℓ u ψ hψ p, norm_mul,
      show Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          = Complex.exp (((-(ℓ * inner ℝ p u) : ℝ) : ℂ) * Complex.I) from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hpt]
  exact (integrable_norm_sq_PsiC ℓ p ψ hψ hcs).comp_smul (ne_of_gt hℓ)

end Work.BoseKinLoc.Momentum
