import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Scaling/Defs` — the profile `φ = χ²` and its Fourier set-up

Vocabulary shared by the `Scaling` node (FS `sec:3Q`): the estimate
`|(ℓ⁻² − Δ)^M χ_Λ²| ≤ C ℓ^{-2M}` of `final_v2.tex` ll. 1531–1535, formalised as
`Work.BoseFixB3.Scaling.chiSq_mult_bound` (a bound on the Fourier multiplier
`Work.BoseFixB3.multOn` applied to `χ_Λ²`).

* `phi = χ²` is the square of the corpus's cubic bump (`Submission.BoseGases.chi`): the
  profile of the localisation window `χ_Λ²`, because `χ_Λ(x) = chiU ℓ 0 x = χ(ℓ⁻¹ • x)`.
* `phiC = (phi : ℂ)`; `phiSch` is the corresponding Schwartz function (smooth with compact
  support), so that `kinFT phiC = 𝓕 phiSch ∘ (2π)⁻¹` is the Fourier transform of a Schwartz
  function and therefore rapidly decaying.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators FourierTransform SchwartzMap

namespace Work.BoseFixB3.Scaling

/-- `φ = χ²`, the square of the corpus's cubic bump.  It is the profile of the localisation
window `χ_Λ²` up to the scaling `x ↦ ℓ⁻¹ • x`. -/
def phi (z : EuclideanSpace ℝ (Fin 3)) : ℝ := Submission.BoseGases.chi z ^ 2

lemma phi_nonneg (z : EuclideanSpace ℝ (Fin 3)) : 0 ≤ phi z :=
  sq_nonneg _

lemma phi_contDiff : ContDiff ℝ ∞ phi := Submission.BoseGases.chi_contDiff.pow 2

lemma phi_continuous : Continuous phi := phi_contDiff.continuous

lemma phi_hasCompactSupport : HasCompactSupport phi := by
  refine Submission.BoseGases.chi_hasCompactSupport.mono ?_
  intro z hz
  simp only [Function.mem_support] at hz ⊢
  intro h
  exact hz (by simp [phi, h])

/-- The complexification of `φ = χ²`. -/
def phiC (z : EuclideanSpace ℝ (Fin 3)) : ℂ := (phi z : ℂ)

lemma phiC_contDiff : ContDiff ℝ ∞ phiC :=
  Complex.ofRealCLM.contDiff.comp phi_contDiff

lemma phiC_hasCompactSupport : HasCompactSupport phiC := by
  refine phi_hasCompactSupport.mono ?_
  intro z hz
  simp only [Function.mem_support] at hz ⊢
  intro h
  exact hz (by simp [phiC, h])

/-- `φ` as a Schwartz function. -/
def phiSch : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ) :=
  phiC_hasCompactSupport.toSchwartzMap phiC_contDiff

lemma phiSch_apply (z : EuclideanSpace ℝ (Fin 3)) :
    (phiSch : EuclideanSpace ℝ (Fin 3) → ℂ) z = phiC z := by
  rw [phiSch]; rfl

/-- The corpus's `p`-convention Fourier transform of the profile: it is the Fourier transform
of the Schwartz function `phiSch` at the frequency `(2π)⁻¹ • q`. -/
lemma kinFT_phiC_fourier (q : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT phiC q
      = (FourierTransform.fourier phiSch : EuclideanSpace ℝ (Fin 3) → ℂ) ((2 * Real.pi)⁻¹ • q) := by
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, SchwartzMap.fourier_coe]
  rfl

end Work.BoseFixB3.Scaling
