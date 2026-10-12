import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseKinLoc.Momentum.boxFTfun_kinFT
import Submission.Work.BoseKinLoc.Momentum.setIntegral_bsBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.integral_u_statU_sq_alt` — the `u`-average of the sliding box state

FS `eq:Q1Qslide`: the squared modulus of the `p`-Fourier transform of the mean-free sliding box
state `statU ℓ u ψ = 1_{Λ(u)}(ψ − m_u)` is, after the change of variables `x = ℓ • u`,

    `∫_u ‖kinFT (statU ℓ u ψ) p‖² = (ℓ³)⁻¹ ∫_x ‖PsiC ℓ p ψ x‖²`.

The proof has exactly two inputs:

* the pointwise phase identity `kinFT (statU ℓ u ψ) p = e^{-iℓ⟪p,u⟫} PsiC ℓ p ψ (ℓ•u)`,
  proved here from `setIntegral_bsBox` and `integral_exp_acube` (the module
  `kinFT_statU_alt` has the same statement under the name `kinFT_statU_alt`);
* the unconditional change of variables `Measure.integral_comp_smul_of_nonneg` for the
  dilation `u ↦ ℓ • u`, whose Jacobian is `(ℓ³)⁻¹` (in dimension `finrank ℝ ℝ³ = 3`).

The helper lemmas are `private` so that this file can be imported freely alongside the other
(in-progress) modules porting the same scratch proofs; only `integral_u_statU_sq_alt` is exported.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

private lemma measurableSet_bsBox (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    MeasurableSet (Work.BSKinetic.bsBox ℓ u) := by
  have h : Work.BSKinetic.bsBox ℓ u
      = (fun x : EuclideanSpace ℝ (Fin 3) => x - ℓ • u) ⁻¹' acube ℓ := rfl
  rw [h]
  exact (acube_measurable ℓ).preimage (by fun_prop)

private lemma setIntegral_eq_indicator {s : Set (EuclideanSpace ℝ (Fin 3))} (hs : MeasurableSet s)
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) :
    (∫ x in s, f x) = ∫ x, s.indicator f x := (MeasureTheory.integral_indicator hs).symm

private lemma setIntegral_sub' {s : Set (EuclideanSpace ℝ (Fin 3))} (hs : MeasurableSet s)
    {f g : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : IntegrableOn f s) (hg : IntegrableOn g s) :
    (∫ x in s, (f x - g x)) = (∫ x in s, f x) - ∫ x in s, g x := by
  rw [setIntegral_eq_indicator hs f, setIntegral_eq_indicator hs g,
    setIntegral_eq_indicator hs (fun x => f x - g x)]
  rw [← MeasureTheory.integral_sub ((MeasureTheory.integrable_indicator_iff hs).mpr hf)
    ((MeasureTheory.integrable_indicator_iff hs).mpr hg)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, sub_self]

private lemma setIntegral_const_mul' (s : Set (EuclideanSpace ℝ (Fin 3))) (c : ℂ)
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) :
    (∫ x in s, c * f x) = c * ∫ x in s, f x :=
  MeasureTheory.integral_const_mul c f

private lemma setIntegral_mul_const' (s : Set (EuclideanSpace ℝ (Fin 3))) (c : ℂ)
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) :
    (∫ x in s, f x * c) = (∫ x in s, f x) * c :=
  MeasureTheory.integral_mul_const c f

private lemma boxMeanR_eq (ℓ : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (boxMeanR ℓ ψ x : ℂ) = (ℓ ^ 3)⁻¹ * boxFTfun ℓ 0 ψ x := by
  have hJ : (∫ z in acube ℓ, (ψ (x + z) : ℂ)) = ((∫ z in acube ℓ, ψ (x + z) : ℝ) : ℂ) :=
    integral_ofReal
  unfold boxMeanR boxFTfun
  rw [show (fun z : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ (0 : EuclideanSpace ℝ (Fin 3)) z : ℂ)))
          * (ψ (x + z) : ℂ))
      = fun z : EuclideanSpace ℝ (Fin 3) => (ψ (x + z) : ℂ) from by
    funext z; simp]
  rw [hJ]
  push_cast
  ring

private lemma hphase (ℓ : ℝ) (u p : EuclideanSpace ℝ (Fin 3))
    (z : EuclideanSpace ℝ (Fin 3)) :
    Complex.exp (-(Complex.I * (inner ℝ p (ℓ • u + z) : ℂ)))
      = Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  rw [inner_add_right, inner_smul_right]
  push_cast
  ring

private lemma boxFTfun_eq_integral (ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    boxFTfun ℓ p ψ (ℓ • u)
      = ∫ z in acube ℓ,
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (ℓ • u + z) : ℂ) := rfl

/-- **The pointwise phase identity** (FS `eq:Q1Qslide`), port of `kinFT_statU`:
the `p`-Fourier transform of the mean-free sliding box state is the phase factor times
`PsiC` evaluated at the box centre. -/
private lemma kinFT_statU (ℓ : ℝ) (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    kinFT (statU ℓ u ψ) p
      = Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ))) * PsiC ℓ p ψ (ℓ • u) := by
  set m : ℝ := Work.BSKinetic.bsMean ℓ u ψ with hm
  have hψc : Continuous ψ := hψ.continuous
  have hcont1 : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (ℓ • u + z) : ℂ)) := by fun_prop
  have hcont2 : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (m : ℂ)) := by fun_prop
  have hs : MeasurableSet (Work.BSKinetic.bsBox ℓ u) := measurableSet_bsBox ℓ u
  have hred : kinFT (statU ℓ u ψ) p
      = ∫ x in Work.BSKinetic.bsBox ℓ u,
          Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * ((ψ x - m : ℝ) : ℂ) := by
    rw [kinFT]
    rw [show (fun x : EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * statU ℓ u ψ x)
        = (Work.BSKinetic.bsBox ℓ u).indicator
            (fun x => Complex.exp (-(Complex.I * (inner ℝ p x : ℂ)))
              * ((ψ x - m : ℝ) : ℂ)) from by
      funext x
      simp only [statU, Work.BoseKinLoc.indU, Work.BoseKinLoc.lamBox, Work.BoseKinLoc.Qfree,
        Work.BSKinetic.bsQ]
      by_cases hx : x ∈ Work.BSKinetic.bsBox ℓ u
      · simp only [Set.indicator_of_mem hx]; push_cast; ring
      · simp only [Set.indicator_of_notMem hx]; simp]
    rw [MeasureTheory.integral_indicator hs]
  rw [hred, setIntegral_bsBox]
  rw [show (∫ z in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ p (ℓ • u + z) : ℂ)))
          * ((ψ (ℓ • u + z) - m : ℝ) : ℂ))
      = ∫ z in acube ℓ, Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          * (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
            * ((ψ (ℓ • u + z) - m : ℝ) : ℂ)) from by
    apply MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ)
    intro z _
    dsimp only
    rw [hphase ℓ u p z]; ring]
  rw [setIntegral_const_mul']
  rw [show (fun z : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((ψ (ℓ • u + z) - m : ℝ) : ℂ))
      = fun z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (ℓ • u + z) : ℂ)
          - Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (m : ℂ) from by
    funext z; push_cast; ring]
  rw [setIntegral_sub' (acube_measurable ℓ)
    (ContinuousOn.integrableOn_compact (acube_compact hℓ) hcont1.continuousOn)
    (ContinuousOn.integrableOn_compact (acube_compact hℓ) hcont2.continuousOn)]
  rw [setIntegral_mul_const', integral_exp_acube]
  rw [show (m : ℂ) = (boxMeanR ℓ ψ (ℓ • u) : ℂ) from by rw [hm]; rfl]
  rw [PsiC, boxFTfun_eq_integral]
  ring

/-- **FS `eq:Q1Qslide`**: the `u`-average of the squared modulus of the `p`-Fourier transform of
the mean-free sliding box state, after the change of variables `x = ℓ • u`. -/
theorem integral_u_statU_sq_alt (ℓ : ℝ) (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    ∫ u : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Momentum.statU ℓ u ψ) p‖ ^ 2 =
      (ℓ ^ 3)⁻¹ * ∫ x : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.Momentum.PsiC ℓ p ψ x‖ ^ 2 := by
  have hpt : ∀ u : EuclideanSpace ℝ (Fin 3),
      ‖kinFT (statU ℓ u ψ) p‖ ^ 2 = ‖PsiC ℓ p ψ (ℓ • u)‖ ^ 2 := by
    intro u
    rw [kinFT_statU ℓ hℓ u ψ hψ p, norm_mul,
      show Complex.exp (-(Complex.I * ((ℓ * inner ℝ p u : ℝ) : ℂ)))
          = Complex.exp (((-(ℓ * inner ℝ p u) : ℝ) : ℂ) * Complex.I) from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [show (∫ u : EuclideanSpace ℝ (Fin 3), ‖kinFT (statU ℓ u ψ) p‖ ^ 2)
      = ∫ u : EuclideanSpace ℝ (Fin 3),
          (fun x : EuclideanSpace ℝ (Fin 3) => ‖PsiC ℓ p ψ x‖ ^ 2) (ℓ • u) from by
    apply integral_congr_ae; filter_upwards with u; exact hpt u]
  rw [MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun x : EuclideanSpace ℝ (Fin 3) => ‖PsiC ℓ p ψ x‖ ^ 2) ℓ (hR := hℓ.le)]
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from by simp [EuclideanSpace],
    smul_eq_mul]

end Work.BoseKinLoc.Momentum
