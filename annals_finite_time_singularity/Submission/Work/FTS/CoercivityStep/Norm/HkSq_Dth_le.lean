/-
# The `ℋ^n`-norm of `D_θ f` is dominated by the `ℋ^{n+1}`-norm of `f`

`Work.Coercivity.HkIntegrand_Dth_le` gives, for `0 < α` and all `(z,θ) ∈ Iz × Iθ`,
the *pointwise* domination

  `HkIntegrand α n (D_θ f) z θ ≤ HkIntegrand α (n+1) f z θ`

of the `ℋ^n`-integrand of `D_θ f` by the `ℋ^{n+1}`-integrand of `f`: the pure summands
`D_z^i D_θ f` of the former are mixed summands of the latter at level `n+1`, carrying the
lighter weight `w/√sin(2θ)^η ≤ W = w·sin(2θ)^{-γ/2}` (`Work.Spaces.H_le_Wt`, using
`η < γ`), and the mixed summands are the mixed summands of `f` with the `D_θ`-order
raised by one.

The present file turns that pointwise bound into the statement about the squared norms.
The only additional input is the honesty of the dominating integrand, which is exactly
`HkMem α (n+1) f`: every angular slice `θ ↦ HkIntegrand α (n+1) f z θ` is integrable
(`z ∈ Iz`) and `z ↦ ∫_θ HkIntegrand α (n+1) f z θ` is integrable on `Iz`.

The transfer is the elementary measure-theoretic fact (`iterated_integral_le`) that a
pointwise bound `A ≤ B` of *nonnegative* integrands, together with the honesty of `B`'s
iterated integrals, implies `∫_z ∫_θ A ≤ ∫_z ∫_θ B`.  No measurability is required of
`A` — hence no smoothness hypothesis on `f` is needed: on a slice where `A` fails to be
integrable Lean's totalised integral is the junk value `0`, which is still dominated by
the (nonnegative) integral of `B`, and `integral_mono_of_nonneg` handles both cases at
once.
-/
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

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

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

/-- The squared `ℋ^n`-norm of `D_θ f` is dominated by the squared `ℋ^{n+1}`-norm of `f`,
for every `f` with honest `ℋ^{n+1}`-integrand. -/
theorem HkSq_Dth_le (α : ℝ) (hα : 0 < α) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f :=
  iterated_integral_le
    (fun z _ θ _ => Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ)
    (fun z hz θ hθ => Work.Coercivity.HkIntegrand_Dth_le α hα n f z θ hz hθ)
    (fun z hz => h.1 z hz) h.2

end Work.FTS.CoercivityStep.Norm
