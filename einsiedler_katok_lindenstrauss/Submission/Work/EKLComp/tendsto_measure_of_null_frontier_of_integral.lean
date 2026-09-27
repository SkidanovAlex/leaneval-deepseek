import Mathlib
import Submission.Work.EKLComp.USCBasic

/-!
# Weak convergence and null frontiers on `X₃`

Portmanteau step used in the EKL argument: if a sequence of probability measures `νₙ` on the space
of lattices `X₃ = SL₃(ℝ)/SL₃(ℤ)` converges weakly to a probability measure `μ` (tested against
bounded continuous functions), then for every measurable set `A` whose boundary is `μ`-null the
measures `νₙ A` converge to `μ A`.

This is the standard Portmanteau implication (T) ⟹ (B), available in Mathlib for spaces in which
indicators of closed sets are approximated from above by bounded continuous functions
(`MeasureTheory.HasOuterApproxClosed`).  `X₃` is second countable and `T₃` — it is the quotient of
the second countable group `SL₃(ℝ)` by its closed discrete subgroup `SL₃(ℤ)` — hence
pseudo-metrizable by Urysohn's metrization theorem, hence has that approximation property.

The only work here is bookkeeping: Mathlib's characterisation of weak convergence of probability
measures is `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`, whose right hand side is
exactly the shape of the hypothesis `hweak`.

A formal detail worth recording: the hypothesis that is consumed by Mathlib's portmanteau lemma has
type `Filter.Tendsto ν atTop (𝓝 μ₀)` with `μ₀ : ProbabilityMeasure X₃`.  Such a type cannot be
*stated* as a `have`/`example` goal: when the elaborator reaches the argument `𝓝 μ₀` it still has
the codomain of `ν` as a metavariable, and type class search for `TopologicalSpace ?m` fails.  It is
therefore produced *in place*, as the argument of the portmanteau lemma, where the expected type
(and hence the codomain) is already determined by the lemma's signature.
-/

open MeasureTheory Filter Topology

set_option linter.style.haveILetI false

namespace Work.EKLComp

open Work.EKLContract

/-- `X₃` has the `HasOuterApproxClosed` property: it is pseudo-metrizable (second countable and
`T₃`), and pseudo-metrizable spaces come with decreasing bounded continuous approximations to the
indicator of a closed set. -/
lemma hasOuterApproxClosed_X3 : HasOuterApproxClosed X3 := inferInstance

theorem tendsto_measure_of_null_frontier_of_integral (νseq : ℕ → MeasureTheory.Measure Work.EKLContract.X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) (hprob : ∀ n, MeasureTheory.IsProbabilityMeasure (νseq n)) [MeasureTheory.IsProbabilityMeasure μ] (hweak : ∀ f : BoundedContinuousFunction Work.EKLContract.X3 ℝ, Filter.Tendsto (fun n => ∫ x, f x ∂(νseq n)) Filter.atTop (nhds (∫ x, f x ∂μ))) {A : Set Work.EKLContract.X3} (hA : MeasurableSet A) (hbdry : μ (frontier A) = 0) : Filter.Tendsto (fun n => νseq n A) Filter.atTop (nhds (μ A)) := by
  have hAmeas : MeasurableSet A := hA
  haveI hOAC : HasOuterApproxClosed Work.EKLContract.X3 := hasOuterApproxClosed_X3
  -- Portmanteau (T) ⟹ (B) for probability measures; the weak convergence hypothesis is
  -- `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak`, supplied in place so that
  -- the codomain of the sequence is known while elaborating its `𝓝`.
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μs := fun n => (⟨νseq n, hprob n⟩ : ProbabilityMeasure Work.EKLContract.X3))
    (μ := (⟨μ, ‹MeasureTheory.IsProbabilityMeasure μ›⟩ : ProbabilityMeasure Work.EKLContract.X3))
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr (by
      intro f
      exact hweak f))
    hbdry

end Work.EKLComp
