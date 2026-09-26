import Submission.Work.Drive.EpsFormSphere.submodule_const_of_finrank_jumps
import Submission.Work.SurgeryInvariance.Defs

/-!
# Pardon's sweep-constancy, from the dimension-jump lemma

`Submission/Work/Drive/EpsFormSphere/span_const_of_sweep_axioms.lean` states the combinatorial core
of the sideways-slab sweep (Pardon's `spherefamily` argument) as `span_const_of_sweep_axioms`, with a
`sorry` at the time of writing.  Here the same statement is *proved*, by the delegated lemma
`Work.Drive.EpsFormSphere.submodule_const_of_finrank_jumps` (a child of this agent): the winding
span is a `ℚ`-submodule of `ℚ × ℚ`, so Pardon's two possible ranks `0` and `2` differ by more than
one and the rank jumps of size at most one cannot change the value.

So the residual of the sweep is P1 (the generic sweep), P2/P3 (the regularity and the jump, in the
`Prop`-form the structure `Work.Drive.EpsSphere.SideSweepData` consumes) and P4 (the dichotomy); the
*combinatorial* step is proved. -/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Drive.EpsForm

/-- **The sweep-constancy, proved.**  Same hypotheses as
`Work.Drive.EpsFormSphere.span_const_of_sweep_axioms`. -/
theorem span_const_of_sweep_axioms_of_finrank_jumps (P : Work.CoreTopology.ParamTorus)
    (X : ℝ → Set LeanEval.KnotTheory.PardonDistortion.R3)
    (lam0 lam1 : ℝ) (exc : Finset ℝ) (hl : lam0 < lam1)
    (hexc : ∀ t ∈ exc, lam0 < t ∧ t < lam1)
    (hmono : ∀ μ ν : ℝ, μ ≤ ν → X ν ⊆ X μ)
    (hreg : ∀ μ ν : ℝ, lam0 ≤ μ → μ ≤ ν → ν ≤ lam1 →
      (∀ t ∈ exc, t < μ ∨ ν < t) →
      Work.SurgeryInvariance.WindingSpan P (X μ) =
        Work.SurgeryInvariance.WindingSpan P (X ν))
    (hjump : ∀ lam ∈ exc, ∀ μ ν : ℝ, lam0 ≤ μ → μ < lam → lam < ν → ν ≤ lam1 →
      (∀ t ∈ exc, t < μ ∨ t = lam ∨ ν < t) →
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (X μ)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (X ν)) + 1 ∧
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (X ν)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (X μ)) + 1)
    (hdich : ∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) →
      Work.SurgeryInvariance.WindingSpan P (X lam) = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan P (X lam) = ⊤) :
    Work.SurgeryInvariance.WindingSpan P (X lam0) =
      Work.SurgeryInvariance.WindingSpan P (X lam1) :=
  Work.Drive.EpsFormSphere.submodule_const_of_finrank_jumps
    (V := fun lam => Work.SurgeryInvariance.WindingSpan P (X lam))
    lam0 lam1 exc hl hexc hreg hjump hdich

end Work.Drive.EpsForm
