import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.BasisCoeffsDelta
import Submission.Work.FunctionalEquations.ReconstructionCLM
import Submission.Work.FunctionalEquations.ReconstructionGaussian
import Submission.Work.FunctionalEquations.GaussiansDense
import Submission.Work.FunctionalEquations.SeminormGrowthOfRadialGrowth

/-!
# From the functional equations to the interpolation basis (CKMRV Theorem 3.1)

This file assembles the main theorem of the area: the data produced by a
well-behaved solution of CKMRV's functional equations
(`Work.FE.InterpolationSolution`) yields a `Work.Core.InterpolationBasis n 1`.

The three fields of the interpolation basis are supplied by

* `Work.FunctionalEquations.BasisCoeffsDelta` (the Kronecker delta pattern of the
  samples of the basis, paper Section 8),
* `S.growth_seminorm` (the polynomial growth of the Schwartz seminorms of the
  basis, the last sentence of Theorem 3.1),
* the density argument of Step 3 of the proof of Theorem 3.1: the defect functional
  `f ↦ ∑ i, (coeffs f i) * (basis i) x - f x` is continuous
  (`Work.FunctionalEquations.ReconstructionCLM`), vanishes on the complex Gaussians
  (`Work.FunctionalEquations.ReconstructionGaussian`), and hence vanishes on all
  radial Schwartz functions by the density of the complex Gaussians (paper Lemma 3.3),
  proved as `Work.FE.gaussiansDense` from
  `Work.FunctionalEquations.DensityOfGaussians`.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

/-- **CKMRV Theorem 3.1, assembled.**  A well-behaved solution of the functional
equations, together with the coefficient data of Section 3.1 and the normalisations of
Section 8 bundled in `InterpolationSolution`, produces an interpolation basis in the
sense of `Work.Core.InterpolationBasis`: the samples of the basis are Kronecker deltas,
the Schwartz seminorms of the basis grow at most polynomially, and every radial
Schwartz function is the sum of its samples times the basis.

This is a `def` and not a `theorem` because `Work.Core.InterpolationBasis n 1` is a
structure in `Type`, not a proposition. -/
noncomputable def interpolationBasis_of_functionalEquations (n : ℕ) [NeZero n]
    (S : InterpolationSolution n) : Work.Core.InterpolationBasis n 1 where
  basis := S.basis
  delta := Work.FunctionalEquations.BasisCoeffsDelta S
  growth := by
    intro k l
    obtain ⟨C, N, hC, h⟩ :=
      Work.FunctionalEquations.SeminormGrowthOfRadialGrowth S.basis S.growth_radial k l
    exact ⟨C, N, hC, fun i => h i.1 i.2⟩
  formula := by
    intro f x
    obtain ⟨Λ, hΛ⟩ := Work.FunctionalEquations.ReconstructionCLM S x
    have hgauss : ∀ (τ : ℂ), τ.im = 1 → ∀ G : 𝓢(E n, ℂ),
        (∀ y, G y = Work.Core.gaussianFun n τ y) → Λ G = 0 := by
      intro τ hτ G hG
      rw [hΛ G]
      exact Work.FunctionalEquations.ReconstructionGaussian S x τ (by rw [hτ]; norm_num) G hG
    have h0 : Λ f.1 = 0 :=
      gaussiansDense n 1 (by norm_num) Λ hgauss f.1 f.2
    rw [hΛ f.1] at h0
    exact (sub_eq_zero.mp h0).symm

end Work.FE

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation

/-- Alias of `Work.FE.interpolationBasis_of_functionalEquations` in the namespace of this
directory. -/
noncomputable def interpolationBasis_of_functionalEquations (n : ℕ) [NeZero n]
    (S : Work.FE.InterpolationSolution n) : Work.Core.InterpolationBasis n 1 :=
  Work.FE.interpolationBasis_of_functionalEquations n S

/-- The propositional form of the main theorem: the interpolation basis exists. -/
theorem interpolationBasis_of_functionalEquations_nonempty (n : ℕ) [NeZero n]
    (S : Work.FE.InterpolationSolution n) : Nonempty (Work.Core.InterpolationBasis n 1) :=
  ⟨Work.FE.interpolationBasis_of_functionalEquations n S⟩

end Work.FunctionalEquations
