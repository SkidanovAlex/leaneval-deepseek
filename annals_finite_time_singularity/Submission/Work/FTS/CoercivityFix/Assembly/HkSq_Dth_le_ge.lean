/-
# `HkSq α n (D_θ f) ≤ HkSq α (n+1) f` for the full range `α ≥ -1/10`

The threshold version of `Work.FTS.CoercivityStep.Norm.HkSq_Dth_le` (which assumed
`0 < α`), needed by the coercion assembly: the `Ê₂`-defect lives at level `n` and the
`StepReg2`-port `normSub` must be available on the sharp range `α ≥ -1/10` on which the
two angular weights of `HkIntegrand` cross (`sin(2θ)^{-η/2} ≤ W` iff `η ≤ γ(α)`, i.e.
iff `α ≥ -1/10`).

The pointwise domination of the integrands is
`Work.FTS.CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge` (already delivered):
`HkIntegrand α n (D_θ f) ≤ HkIntegrand α (n+1) f` on `Iz × Iθ`.  What is left here is the
elementary measure-theoretic transfer of a pointwise bound of *nonnegative* integrands to
the iterated integrals, using only the honesty of the dominating integrand — i.e. the
hypothesis `HkMem α (n+1) f` itself.  No measurability or smoothness is needed of the
dominated integrand: where a slice fails to be integrable Lean's totalised integral is the
junk value `0`, still dominated by the nonnegative integral of the majorant, and
`integral_mono_of_nonneg` covers both cases at once (this is why no `SmoothQuad`/`RegQ`
hypothesis appears in the statement).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

/-! ## The measure-theoretic transfer -/

/-- **Iterated integrals of a pointwise-dominated nonnegative integrand.**

If `0 ≤ A ≤ B` pointwise on `Iz × Iθ`, if every angular slice of `B` is integrable and
`z ↦ ∫_θ B z θ` is integrable on `Iz`, then `∫_z ∫_θ A ≤ ∫_z ∫_θ B`.

No measurability of `A` is assumed: where the slice `θ ↦ A z θ` is not integrable the
inner integral is `0 ≤ ∫_θ B z θ` (the latter being nonnegative by `0 ≤ B` on the slice),
and `MeasureTheory.integral_mono_of_nonneg` applies in each case. -/
private lemma iterated_integral_le {A B : ℝ → ℝ → ℝ}
    (hA0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A z θ)
    (hAB : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, A z θ ≤ B z θ)
    (hB : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => B z θ) Work.Spaces.Iθ)
    (hBz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, B z θ) Work.Spaces.Iz) :
    ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, A z θ) ≤
      ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, B z θ) := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  refine integral_mono_of_nonneg ?_ hBz ?_
  · -- nonnegativity of the inner integral of `A` on `Iz`
    refine ae_restrict_of_forall_mem hmesz (fun z hz => ?_)
    exact integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hA0 z hz θ hθ))
  · -- `z ↦ ∫_θ A z θ ≤ z ↦ ∫_θ B z θ` on `Iz`
    refine ae_restrict_of_forall_mem hmesz (fun z hz => ?_)
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hA0 z hz θ hθ))
      (hB z hz)
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hAB z hz θ hθ))

/-! ## The target -/

/-- The squared `ℋⁿ`-norm of `D_θ f` is dominated by the squared `ℋ^{n+1}`-norm of `f`,
for every `f` with honest `ℋ^{n+1}`-integrand and every `α ≥ -1/10`. -/
theorem HkSq_Dth_le_ge (α : ℝ) (hα : -(1/10 : ℝ) ≤ α) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f :=
  iterated_integral_le
    (fun z _ θ _ => Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ)
    (fun z hz θ hθ =>
      Work.FTS.CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge α hα n f z θ hz hθ)
    (fun z hz => h.1 z hz) h.2

end Work.FTS.CoercivityFix.Assembly
