/-
# Monotonicity of `HkSq` in the regularity index

`Work.Spaces.HkSq α k f` is the square of the `H^k`-norm of the paper.  Enlarging `k`
only adds the squares of further weighted derivatives to the integrand
(`Work.Spaces.HkIntegrand`, a sum of squares), so the pointwise integrand is monotone
in `k` (`Work.Spaces.HkIntegrand_mono`, iterated here to `k ≤ l`).

Integrating the pointwise inequality gives `HkSq α k f ≤ HkSq α l f` as soon as the
`l`-th integrand has honest iterated integrals, i.e. under the single hypothesis
`Work.Spaces.HkMem α l f` (no smoothness of `f` is required: the integrability of the
*larger* integrand is exactly what `HkMem α l f` provides).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.HkSq_mono
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

set_option autoImplicit false

/-- The `H^k`-integrand is monotone in the exponent: for `k ≤ l` every summand of
`HkIntegrand α k f` occurs in `HkIntegrand α l f` with the same value, and all summands
are squares, hence nonnegative.  This is `Work.Spaces.HkIntegrand_mono` iterated. -/
private theorem HkIntegrand_mono_le (α : ℝ) {k l : ℕ} (hkl : k ≤ l) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α l f z θ :=
  Nat.le_induction (le_refl _)
    (fun n _ ih => le_trans ih (Work.Spaces.HkIntegrand_mono α n f z θ)) l hkl

theorem HkSq_mono_le (α : ℝ) {k l : ℕ} (hkl : k ≤ l) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α l f) : Work.Spaces.HkSq α k f ≤ Work.Spaces.HkSq α l f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    h.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l f z θ
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz =>
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      (h.1 z hz)
      (Eventually.of_forall fun θ => HkIntegrand_mono_le α hkl f z θ)

end Work.FTS.CoercivityStep.Norm
