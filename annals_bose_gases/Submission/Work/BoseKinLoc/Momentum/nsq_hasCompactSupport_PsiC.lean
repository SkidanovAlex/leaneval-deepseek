import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.nsqAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Momentum

set_option linter.unusedVariables false

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

open Submission.BoseGases

/-- **Compact support of `PsiC`.**  `PsiC ℓ p ψ = boxFTfun ℓ p ψ − boxMeanR ℓ ψ · boxHat ℓ p`
is the difference of two box-localised shift integrals of `ψ`, hence compactly supported
whenever `ψ` is and `ℓ > 0`. -/
theorem nsq_hasCompactSupport_PsiC (ℓ : ℝ) (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) : HasCompactSupport (Work.BoseKinLoc.Momentum.PsiC ℓ p ψ) := by
  -- The real box-localised shift integral of `ψ` is compactly supported (same argument as the
  -- complex version in `nsqAux`).
  have hreal : HasCompactSupport (fun x : ℝ³ => ∫ z in acube ℓ, ψ (x + z)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (fun q : ℝ³ × ℝ³ => q.1 - q.2) '' (tsupport ψ ×ˢ acube ℓ)) ?_ ?_
    · exact ((show IsCompact (tsupport ψ) from hcs).prod (acube_compact hℓ)).image continuous_sub
    · intro x hx
      rw [Function.mem_support] at hx
      by_contra hmem
      apply hx
      have hzero : ∀ z ∈ acube ℓ, ψ (x + z) = 0 := by
        intro z hz
        by_contra hne
        exact hmem ⟨(x + z, z), ⟨subset_tsupport ψ (Function.mem_support.mpr hne), hz⟩, by simp⟩
      rw [setIntegral_congr_fun (acube_measurable ℓ) hzero]
      simp
  -- `boxMeanR ℓ ψ` is a constant multiple of that integral.
  have hMean : HasCompactSupport (fun x : ℝ³ => (boxMeanR ℓ ψ x : ℂ)) := by
    have h1 : HasCompactSupport (boxMeanR ℓ ψ) :=
      hreal.mono (fun x hx hint => hx (by simp [boxMeanR, hint]))
    simpa [Function.comp_def] using h1.comp_left (show (Complex.ofReal (0:ℝ)) = 0 from by simp)
  -- `boxFTfun ℓ p ψ` is a box-localised shift integral of the complexification of `ψ`.
  have hFTraw : HasCompactSupport
      (fun x : ℝ³ => ∫ z in acube ℓ,
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (x + z) : ℂ)) := by
    have hg : HasCompactSupport (fun y : ℝ³ => (ψ y : ℂ)) :=
      by simpa [Function.comp_def] using hcs.comp_left (show (Complex.ofReal (0:ℝ)) = 0 from by simp)
    exact nsq_hasCompactSupport_shiftIntegral hℓ
      (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) (fun y : ℝ³ => (ψ y : ℂ)) hg
  have hFT : HasCompactSupport (boxFTfun ℓ p ψ) := hFTraw
  -- The second summand `boxMeanR ℓ ψ · boxHat ℓ p` is supported where `boxMeanR ℓ ψ` is.
  have hG : HasCompactSupport
      (fun x : ℝ³ => (boxMeanR ℓ ψ x : ℂ) * (Work.OneBodyKin.boxHat ℓ p : ℂ)) :=
    HasCompactSupport.mul_right (f := fun x : ℝ³ => (boxMeanR ℓ ψ x : ℂ))
      (f' := fun _ : ℝ³ => (Work.OneBodyKin.boxHat ℓ p : ℂ)) hMean
  -- Difference of two compactly supported functions; `PsiC` is definitionally that difference.
  exact hFT.sub hG

end Work.BoseKinLoc.Momentum
