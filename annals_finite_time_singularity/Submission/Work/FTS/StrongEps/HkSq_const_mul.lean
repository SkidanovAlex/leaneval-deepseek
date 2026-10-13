import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Hilbert.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- `H^k`-squared is homogeneous of degree two in the amplitude.

`HkSq` is the iterated integral (over `[0,∞) × [0,π/2]`, measure `dz dθ`) of the integrand
`HkIntegrand`, which is a sum of squares of expressions that are *linear* in `f`.  The pointwise
homogeneity of the integrand,
`HkIntegrand α k (fun z θ => c * f z θ) z θ = c ^ 2 * HkIntegrand α k f z θ`
(proved unconditionally in `Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul`: `deriv` is scalar
homogeneous with no differentiability hypothesis), reduces the claim to the unconditional
linearity of the Lebesgue integral in a constant factor,
`∫ θ in Iθ, c ^ 2 * g θ = c ^ 2 * ∫ θ in Iθ, g θ`, applied once to the inner and once to the
outer integral.  No regularity or integrability hypothesis on `f` is needed. -/
theorem HkSq_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => c * f z θ) = c ^ 2 * Work.Spaces.HkSq α k f := by
  have hpoint : ∀ z θ : ℝ,
      Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ
        = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α k c f z θ
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [funext (fun θ => hpoint z θ)]
    exact MeasureTheory.integral_const_mul (c ^ 2)
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  simp only [hinner]
  exact MeasureTheory.integral_const_mul (c ^ 2)
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)

end Work.FTS.StrongEps
