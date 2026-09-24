import ChallengeDeps
import Submission.Work.Modulus.Main
import Submission.Work.Modulus.Hypothesis
import Submission.Work.Modulus.Unsatisfiable

/-!
# The assembly-level statements of the modulus chapter

## The literal deliverable

`Work.Modulus.exists_holomorphic_modulus_of_greenFunction` (in
`Submission/Work/Modulus/Main.lean`, imported here) is the statement requested for this subproject,
verbatim: a strong Green function `E` with pole `z₀` (`Submission.HasGreenFunctionE`) on a surface
with `H¹(X,ℝ) = 0` has a holomorphic modulus `Φ`.

**It is vacuously true.**  `Submission.HasGreenFunctionE` is *unsatisfiable* on a
`ChartedSpace ℂ X`: its growth clause at the pole and its compact-superlevel-set clause for
`{E z₀' + 1 ≤ E}` contradict each other
(`Work.Modulus.not_hasGreenFunctionE`, `Submission/Work/Modulus/Unsatisfiable.lean`, machine
checked).  Its proof is therefore the one-line elimination of the unsatisfiable hypothesis, and the
mathematical content of the chapter is delivered in the corrected vocabulary instead.  The
statement is kept because the *form* of the request (and of `Submission.GreenInterface`) names it;
nothing downstream can use it in a non-vacuous way, and the assembly consumes
`Work.UnitGreen.IsUnitGreenFunctionAt` (`Submission.Gaps`).

## The corrected statement

`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction` below is the same theorem with the
satisfiable hypothesis and with Hubbard Theorem 1.1.2 (`Work.Spine`) as an explicit argument:

```
Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112 hE
  (fun hX x _ => Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal hX x)
```

With that one term supplied by the `Work.Spine` subproject, the theorem becomes exactly the
placeholder `Submission.exists_holomorphic_modulus_of_greenFunction` of
`Submission/Gaps.lean` (the statement there is this one with the topological input discharged), and
it has no `sorryAx` in its closure.  The version with the old hypothesis is
`exists_holomorphic_modulus_of_greenFunctionE_of_hubbard112` below.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The requested statement in the corrected vocabulary**: the drop-in replacement for the
placeholder `Submission.exists_holomorphic_modulus_of_greenFunction` of `Submission/Gaps.lean`,
with Hubbard Theorem 1.1.2 passed explicitly.  (Supplying that argument from `Work.Spine` — one
term — makes this the unconditional statement.) -/
theorem exists_holomorphic_modulus_of_unitGreenFunction {z₀ x₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    (hSpine : (¬ CompactSpace X) → (x : X) →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) :=
  exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112 (z₀ := z₀) (x₀ := x₀) hE hSpine

/-- **The requested statement with the old hypothesis and the topological input explicit.**  Here
the hypothesis `H¹(X,ℝ) = 0` is genuinely used (through `hSpine`), unlike in
`exists_holomorphic_modulus_of_greenFunction` above, where the Green data are contradictory: this
is the honest form of the deliverable. -/
theorem exists_holomorphic_modulus_of_greenFunctionE_of_hubbard112 {z₀ x₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionE z₀ E)
    (hSpine : (¬ CompactSpace X) → (x : X) →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) :=
  exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112 (z₀ := z₀) (x₀ := x₀)
    (isUnitGreenFunctionAt_of_hasGreenFunctionE hE) hSpine

end Work.Modulus
