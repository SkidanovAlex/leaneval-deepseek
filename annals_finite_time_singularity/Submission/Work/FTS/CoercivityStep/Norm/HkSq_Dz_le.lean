import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.HkMem_dth
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `|D_z f|_{H^n}² ≤ |f|_{H^{n+1}}²`

The `H^k`-integrand of the paper is a sum of squares of weighted `D`-derivatives.  For
`g = D_z f`, every summand of `HkIntegrand α n (D_z f)` is a summand of
`HkIntegrand α (n+1) f`:

* the pure family: `D_z^i (D_z f) = D_z^{i+1} f` is a pure derivative of `f` of order
  `i + 1 ≤ n + 1`;
* the mixed family: `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`, which uses the
  commutation of `D_z` and `D_θ` on the closed quadrant (available because `f` is
  smooth on a neighbourhood of it), is a mixed derivative of `f` of total order
  `i + j + 1 ≤ n + 1`.

This pointwise domination of the integrands is `Work.Coercivity.HkIntegrand_Dz_le`; the
present lemma is its integrated form.  Unlike the corresponding `D_θ` statement it needs
no hypothesis `0 < α`, because the pure family keeps the lighter weight `w/√sin(2θ)^η`
on both sides (only the `D_θ`-case has to compare that weight with `W`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

theorem HkSq_Dz_le (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f := by
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz f) z θ)
    h.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (n + 1) f z θ
  exact MeasureTheory.ae_restrict_of_forall_mem hmesz fun z hz =>
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz f) z θ)
      (h.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem hmesθ fun θ hθ =>
        Work.Coercivity.HkIntegrand_Dz_le α n hsm z θ hz hθ)

end Work.FTS.CoercivityStep.Norm
