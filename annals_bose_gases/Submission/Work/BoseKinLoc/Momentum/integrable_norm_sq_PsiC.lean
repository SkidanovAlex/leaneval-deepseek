import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.nsq_hasCompactSupport_PsiC
import Submission.Work.BoseKinLoc.Momentum.nsq_norm_PsiC_le
import Submission.Work.BoseKinLoc.Momentum.nsq_stronglyMeasurable_PsiC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.integrable_norm_sq_PsiC`

The mean-free localised state of FS `eq:Q1Qslide`,

  `PsiC ℓ p ψ = boxFTfun ℓ p ψ − boxMeanR ℓ ψ · boxHat ℓ p`

(`Submission/Work/BoseKinLoc/Momentum/momDefs.lean`), is *square integrable* as soon as `ψ`
is smooth and compactly supported — in fact `‖PsiC ℓ p ψ‖² ∈ L¹(ℝ³)`.

The proof is elementary and uses no Fourier analysis:

* for `ℓ ≤ 0` the cube `acube ℓ` is contained in `acube 0`, which is a null set, so both
  ingredients of `PsiC` are integrals over a null set: `PsiC ℓ p ψ = 0` pointwise and the
  claim is trivial;
* for `0 < ℓ` the function `PsiC ℓ p ψ` is
  - strongly measurable in `x` (`nsq_stronglyMeasurable_PsiC`),
  - supported in a compact set (`nsq_hasCompactSupport_PsiC`),
  - uniformly bounded (`nsq_norm_PsiC_le`),
  and a strongly measurable, compactly supported, bounded function has integrable square of
  the norm (`nsq_integrable_norm_sq_of_bound`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

theorem integrable_norm_sq_PsiC (ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖Work.BoseKinLoc.Momentum.PsiC ℓ p ψ x‖ ^ 2) := by
  rcases le_or_gt ℓ 0 with hℓ | hℓ
  · -- `ℓ ≤ 0`: the cube is contained in the null cube `acube 0`, and `PsiC` vanishes
    have hsub : acube ℓ ⊆ acube 0 := by
      intro y hy m
      have h1 : y m ≤ ℓ / 2 := (hy m).2
      have h2 : -ℓ / 2 ≤ y m := (hy m).1
      have h3 : y m = 0 := by linarith
      simp [h3]
    have hzero : volume (acube ℓ) = 0 := by
      have h : volume (acube 0 : Set (EuclideanSpace ℝ (Fin 3))) = 0 := by
        rw [acube_volume 0 le_rfl]
        simp
      exact measure_mono_null hsub h
    have hPsi : ∀ x, PsiC ℓ p ψ x = 0 := by
      intro x
      simp only [PsiC, boxFTfun, boxMeanR]
      rw [setIntegral_measure_zero _ hzero, setIntegral_measure_zero _ hzero]
      simp
    refine Integrable.congr (integrable_zero (EuclideanSpace ℝ (Fin 3)) ℝ volume)
      (Filter.Eventually.of_forall fun x => ?_)
    simp [hPsi x]
  · -- `0 < ℓ`: measurable + compactly supported + bounded
    have hmeas := nsq_stronglyMeasurable_PsiC ℓ p ψ hψ hcs
    have hcps := nsq_hasCompactSupport_PsiC ℓ hℓ p ψ hψ hcs
    obtain ⟨C, _hC0, hC⟩ := nsq_norm_PsiC_le ℓ hℓ p ψ hψ hcs
    exact nsq_integrable_norm_sq_of_bound hmeas hcps hC

end Work.BoseKinLoc.Momentum
