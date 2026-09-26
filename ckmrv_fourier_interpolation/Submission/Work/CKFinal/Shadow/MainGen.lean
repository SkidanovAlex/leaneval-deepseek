import Submission.Work.FunctionalEquations.MainGen
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.DeltaGen
import Submission.Work.CKFinal.Shadow.Gen
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionCLMGen
import Submission.Work.CKFinal.Shadow.ReconstructionGaussianGen
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms
import Submission.Work.CKFinal.Shadow.ValuePatternGen

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FE
export _root_.Work.FE (gaussiansDense)
end Work.FE

/-!
# Theorem 3.1 with the interpolation basis starting at `k₀`

`Work.FE.interpolationBasis_of_functionalEquations` assembles the interpolation basis
starting at `m = 1` (the `E_8` case).  This file records the same assembly with the
index set `Set.Ici k₀`, which is what the Leech lattice (`d = 24`, `k₀ = 2`) needs:
there the generating functions decay like `o(e^{-2π Im τ})`, the `m = 1` coefficients
vanish, and the interpolation basis starts at `m = 2`.

The three fields of `Work.Core.InterpolationBasis n k₀` are supplied exactly as in
`Main.lean`, by `Work.FunctionalEquations.DeltaGen`, the `growth_seminorm` field and the
density argument (`Work.FunctionalEquations.ReconstructionCLMGen`,
`Work.FunctionalEquations.ReconstructionGaussianGen`, and `Work.FE.gaussiansDense`).
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

/-- **Theorem 3.1 with the basis starting at `k₀`.**  A well-behaved solution of the
functional equations, together with the coefficient data of Section 3.1 and the
normalisations of Section 8 indexed from `k₀ ≥ 1`, produces an interpolation basis
indexed by `SampleIdx k₀`. -/
noncomputable def interpolationBasis_of_functionalEquations_gen {n : ℕ} [NeZero n]
    {k₀ : ℕ} (hk : 1 ≤ k₀) (S : InterpolationSolutionGen n k₀) :
    Work.Core.InterpolationBasis n k₀ where
  basis := S.basis
  delta := Work.FunctionalEquations.DeltaGen hk S
  growth := by
    intro k l
    obtain ⟨C, N, hC, h⟩ :=
      Work.FunctionalEquations.SeminormGrowthOfRadialGrowth S.basis S.growth_radial k l
    exact ⟨C, N, hC, fun i => h i.1 i.2⟩
  formula := by
    intro f x
    obtain ⟨Λ, hΛ⟩ := Work.FunctionalEquations.ReconstructionCLMGen S x
    have hgauss : ∀ (τ : ℂ), τ.im = 1 → ∀ G : 𝓢(E n, ℂ),
        (∀ y, G y = Work.Core.gaussianFun n τ y) → Λ G = 0 := by
      intro τ hτ G hG
      rw [hΛ G]
      exact Work.FunctionalEquations.ReconstructionGaussianGen S x τ (by rw [hτ]; norm_num) G hG
    have h0 : Λ f.1 = 0 :=
      gaussiansDense n 1 (by norm_num) Λ hgauss f.1 f.2
    rw [hΛ f.1] at h0
    exact (sub_eq_zero.mp h0).symm

end Work.FE

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation

end Work.FunctionalEquations


end Work.CKFinal.Shadow
