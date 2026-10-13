/-
# Homogeneity of the `ℋ^k`-squared norm in the amplitude

`HkSq α k (fun z θ => β * f z θ) = β ^ 2 * HkSq α k f`.

`HkSq` is the iterated integral (over `[0,∞) × [0,π/2]`, with measure `dz dθ`) of the
integrand `HkIntegrand`, which is a sum of squares of expressions linear in `f`.  The
pointwise homogeneity of the integrand,

`HkIntegrand α k (fun z θ => β * f z θ) z θ = β ^ 2 * HkIntegrand α k f z θ`,

is `Work.FTS.LocData.HkIntegrand_const_mul`.  The remaining step is the (unconditional,
in this Mathlib) linearity of the Lebesgue integral in a constant factor,
`∫ θ in Iθ, β ^ 2 * g θ = β ^ 2 * ∫ θ in Iθ, g θ` (`MeasureTheory.integral_const_mul`),
applied once to the inner and once to the outer integral.  Consequently the `HkMem`
hypothesis `hf` is not needed for the identity itself; it is kept because the caller of
this lemma uses `HkSq` under that hypothesis. -/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.HkIntegrand_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.FTS.LocData

theorem HkSq_const_mul (α : ℝ) (k : ℕ) (β : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkSq α k (fun z θ => β * f z θ) = β ^ 2 * Work.Spaces.HkSq α k f := by
  have hpoint : ∀ z θ : ℝ,
      Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ
        = β ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => HkIntegrand_const_mul α k β f z θ
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
        = β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [funext (fun θ => hpoint z θ)]
    exact integral_const_mul (β ^ 2)
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  simp only [hinner]
  exact integral_const_mul (β ^ 2)
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)

end Work.FTS.LocData
