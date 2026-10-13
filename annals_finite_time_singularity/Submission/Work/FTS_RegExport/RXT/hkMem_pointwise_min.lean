import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS_RegExport.RXT.HkMinPrep
import Submission.Work.FTS_RegExport.RXT.HkMinSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.hkMem_pointwise_min`

Pointwise bound for the mixed slots of order `≤ 2` of a datum which is `C⁴` on the *open*
quadrant and honestly in `ℋ⁴`, with the exact weight `min z 1` and **no** boundary-trace
hypothesis:

  `|D_z^b D_θ^a f z θ| ≤ C · min z 1 · |f|_{ℋ⁴}`  for `a + b ≤ 2`, `z > 0`, `0 < θ < π/2`.

This is the sharpened form of the paper's `SecondDerivativesBounded` (`10/√(γ-1)·|f|_{ℋ⁴}`):
the extra factor `min z 1` measures the localisation in the radial variable and reflects the
fact that only `HkMem α 4` (integrability over the quadrant) is available, with no decay at
`z = ∞` and no vanishing at `θ = 0, π/2`.

The proof is the squared estimate `Work.FTS_RegExport.RXT.hkMem_pointwise_min_sq` followed by
elementary square-root algebra.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-- **The pointwise bound.** -/
theorem hkMem_pointwise_min {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Work.FTS.Galerkin.Fn,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := by
  have hγ : 0 < Work.Spaces.gam α - 1 := by linarith [Work.Spaces.one_lt_gam hα]
  refine ⟨Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40),
    Real.sqrt_nonneg _, ?_⟩
  intro f h4 hmem b a hab z θ hz hθ0 hθ1
  have hC0 : (0 : ℝ) ≤ ((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40 := by
    positivity
  have hmin : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hsq := hkMem_pointwise_min_sq (α := α) hα hα1 h4 hmem hab hz hθ0 hθ1
  calc |Work.Spaces.mixed b a f z θ|
      = Real.sqrt ((Work.Spaces.mixed b a f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40
          * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40)
          * min z 1 * Work.Spaces.HkNorm α 4 f := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hC0, Real.sqrt_sq hmin]
        rfl

end Work.FTS_RegExport.RXT
