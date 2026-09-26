import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Core.Gaussian
import Submission.Work.Sampling.coeffs_continuous_linear
import Submission.Work.Interpolation.reconstruction_clm
import Submission.Work.Radial.gaussians_dense
import Submission.Work.Radial.gaussian_schwartz

namespace Work.Interpolation

open LeanEval.Analysis.CKMRVInterpolation
open scoped FourierTransform SchwartzMap

/-- The linear functional `f ↦ f x - ∑ i, coeffs f i * basis i x` is continuous by
`reconstruction_clm`.  If the interpolation formula holds for every Gaussian
`x ↦ exp (π i τ ‖x‖²)` with `0 < Im τ`, then this functional vanishes on all of them;
by `gaussians_dense` it therefore vanishes on every radial Schwartz function, which
is exactly the interpolation formula. -/
theorem formula_of_gaussians (n k₀ : ℕ) [NeZero n]
    (basis : Set.Ici k₀ × Fin 4 → RadialSchwartz n)
    (growth : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ i : Set.Ici k₀ × Fin 4, (SchwartzMap.seminorm ℂ k l) (basis i).1
        ≤ C * ((i.1.1 : ℝ) + 1) ^ N)
    (h : ∀ (τ : ℂ) (hτ : 0 < τ.im), ∀ x : EuclideanSpace ℝ (Fin n),
      Work.Core.gaussianFun n τ x
        = ∑' i : Set.Ici k₀ × Fin 4,
            (coeffs n k₀ (Work.Core.gaussianSchwartz n τ hτ) i) * (basis i).1 x) :
    ∀ f : RadialSchwartz n, ∀ x : EuclideanSpace ℝ (Fin n),
      f.1 x = ∑' i : Set.Ici k₀ × Fin 4, (coeffs n k₀ f.1 i) * (basis i).1 x := by
  intro f x
  obtain ⟨Λ, hΛ⟩ := reconstruction_clm n k₀ x basis growth
  have hker : Λ f.1 = 0 := by
    refine Work.Radial.gaussians_dense n one_pos Λ ?_ f.1 f.2
    intro τ hτy F hF
    have hτ : 0 < τ.im := by rw [hτy]; exact one_pos
    have hFG : F = Work.Core.gaussianSchwartz n τ hτ := by
      apply SchwartzMap.ext
      intro z
      rw [hF z, Work.Core.gaussianSchwartz_apply]
    rw [hFG, hΛ]
    rw [Work.Core.gaussianSchwartz_apply, h τ hτ x, sub_self]
  have h1 := hΛ f.1
  rw [hker] at h1
  exact sub_eq_zero.mp h1.symm

end Work.Interpolation
