import ChallengeDeps
import Submission.GreenInterface
import Submission.Work.Modulus.Defs
import Submission.Work.Parabolic.Basic
import Submission.Work.UnitGreen.Defs
import Submission.Work.Modulus.growth_of_unitGreen

/-!
# The hypothesis of the modulus chapter, and its relation to `Submission.HasGreenFunctionE`

The chapter `Submission/Work/Modulus` (Hubbard, *Teichmüller theory* Vol. 1, Chapter 1: the periods
of the conjugate of the Green function are multiples of `2π`) is stated throughout with the
hypothesis

`Work.UnitGreen.IsUnitGreenFunctionAt z₀ E`

— the *satisfiable* Green-function predicate: `E` is positive and harmonic off `z₀`, its
superlevel sets have compact closures (decay at the ideal boundary), and the logarithmic pole at
`z₀` has coefficient exactly one.  This is exactly the predicate consumed by the assembly
(`Submission.Gaps`, `Submission.Assembly.uniformization_via_green`).

## Why not `Submission.HasGreenFunctionE`

`Submission.HasGreenFunctionE` (in `Submission/GreenInterface.lean`) demands
`IsCompact {x | ε ≤ E x}` for **every** `ε > 0`, on a *total* function `E : X → ℝ`: for
`ε > E z₀` the superlevel set contains a punctured neighbourhood of `z₀` (by the growth clause at
the pole) but not `z₀` itself, so `z₀` lies in its closure and it is not closed — a non-closed
subset of a Hausdorff space is not compact.  Hence `HasGreenFunctionE z₀ E` is **unsatisfiable**
whenever `z₀` is not an isolated point, which is the case on a complex one-manifold
(`Work.Modulus.not_hasGreenFunctionE` below).  Every statement whose hypothesis is
`HasGreenFunctionE` is therefore vacuous; that is why the chapter is stated with the corrected
predicate.  The bridge below nevertheless lets a caller who has the old predicate use the whole
chapter.

The bridge is a genuine implication: `HasGreenFunctionE` asks for *more* than what the mathematics
needs (absolute compactness instead of relative compactness of the level sets), and the proof of
the bridge is the observation that a compact subset of a Hausdorff space is closed, so that the
superlevel set equals its closure.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The strong (unsatisfiable) Green predicate implies the unit-pole one.**  A compact subset of
a Hausdorff space is closed, so a compact superlevel set is closed and equals its own closure. -/
theorem isUnitGreenFunctionAt_of_hasGreenFunctionE {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionE z₀ E) :
    Work.UnitGreen.IsUnitGreenFunctionAt z₀ E := by
  obtain ⟨⟨hpos, hharm, hcomp⟩, hbnd, -⟩ := hE
  refine ⟨⟨hpos, hharm, fun ε hε => ?_⟩, hbnd⟩
  have hcl : closure {x : X | ε ≤ E x} = {x : X | ε ≤ E x} :=
    (hcomp ε hε).isClosed.closure_eq
  rw [hcl]
  exact hcomp ε hε

end Work.Modulus
