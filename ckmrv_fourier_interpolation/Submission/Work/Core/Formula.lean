import ChallengeDeps
import Submission.Work.Core.Basic
import Submission.Work.Core.Gaussian
import Submission.Work.Sampling.coeffs_continuous_linear
import Submission.Work.Interpolation.formula_of_gaussians

/-!
# The pointwise interpolation formula from convergence in the Schwartz space

The paper's Theorem 3.1 produces the interpolation identity as convergence of the
reconstruction series in the Schwartz space.  The `formula` field of
`Work.Core.InterpolationBasis` is the equivalent pointwise statement; this file
records the (easy) passage between the two, using that evaluation at a point is a
continuous linear functional (`Work.Sampling.evalAtCLM`).
-/

open LeanEval.Analysis.CKMRVInterpolation
open scoped FourierTransform SchwartzMap

namespace Work.Core

/-- Evaluation at a point interchanges with convergence of the reconstruction series:
if the series `∑ i, (coeffs f i) • basis i` converges to `f` in the Schwartz space, then
the corresponding pointwise series converges to `f x`. -/
theorem formula_of_hasSum (n k₀ : ℕ) [NeZero n]
    (basis : Set.Ici k₀ × Fin 4 → RadialSchwartz n)
    (h : ∀ f : RadialSchwartz n,
      HasSum (fun i => (coeffs n k₀ f.1 i) • (basis i).1) f.1) :
    ∀ f : RadialSchwartz n, ∀ x : EuclideanSpace ℝ (Fin n),
      f.1 x = ∑' i, (coeffs n k₀ f.1 i) * (basis i).1 x := by
  intro f x
  have hh := ContinuousLinearMap.hasSum (Work.Sampling.evalAtCLM x) (h f)
  rw [Work.Sampling.evalAtCLM_apply] at hh
  simpa [map_smul, Work.Sampling.evalAtCLM_apply, smul_eq_mul] using hh.tsum_eq.symm

/-- Interpolation data, from a basis with delta samples, polynomially growing seminorms and
convergence of the reconstruction series in the Schwartz space. -/
def interpolationBasis_of_hasSum (n k₀ : ℕ) [NeZero n]
    (basis : Set.Ici k₀ × Fin 4 → RadialSchwartz n)
    (delta : ∀ i, coeffs n k₀ (basis i).1 = fun j => if j = i then (1 : ℂ) else 0)
    (growth : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ i : Set.Ici k₀ × Fin 4, (SchwartzMap.seminorm ℂ k l) (basis i).1
        ≤ C * ((i.1.1 : ℝ) + 1) ^ N)
    (h : ∀ f : RadialSchwartz n,
      HasSum (fun i => (coeffs n k₀ f.1 i) • (basis i).1) f.1) :
    InterpolationBasis n k₀ where
  basis := basis
  delta := delta
  growth := growth
  formula := formula_of_hasSum n k₀ basis h

/-- Interpolation data from the interpolation identity at the complex Gaussians only:
by the density of the Gaussians in the radial Schwartz functions (paper Lemma 2.7) the
identity then holds for every radial Schwartz function. -/
def interpolationBasis_of_gaussians (n k₀ : ℕ) [NeZero n]
    (basis : Set.Ici k₀ × Fin 4 → RadialSchwartz n)
    (delta : ∀ i, coeffs n k₀ (basis i).1 = fun j => if j = i then (1 : ℂ) else 0)
    (growth : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ i : Set.Ici k₀ × Fin 4, (SchwartzMap.seminorm ℂ k l) (basis i).1
        ≤ C * ((i.1.1 : ℝ) + 1) ^ N)
    (h : ∀ (τ : ℂ) (hτ : 0 < τ.im), ∀ x : EuclideanSpace ℝ (Fin n),
      gaussianFun n τ x
        = ∑' i : Set.Ici k₀ × Fin 4, (coeffs n k₀ (gaussianSchwartz n τ hτ) i) * (basis i).1 x) :
    InterpolationBasis n k₀ where
  basis := basis
  delta := delta
  growth := growth
  formula := Work.Interpolation.formula_of_gaussians n k₀ basis growth h

end Work.Core
