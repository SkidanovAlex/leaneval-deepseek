import Submission.UnifDeps
import Submission.Work.Modulus.Defs
import Submission.Work.Modulus.Hypothesis
import Submission.Work.Modulus.greenNoncompact
import Submission.Work.Modulus.poleOrderModulus
import Submission.Work.Modulus.monodromyTrivial_of_simplyConnected
import Submission.Work.Modulus.PeriodSetup
import Submission.Work.Modulus.greenPeriodHom_two_pi_zmultiples
import Submission.Work.Modulus.hasTrivialModulusMonodromy_of_periods
import Submission.Work.Modulus.Unsatisfiable

/-!
# The holomorphic modulus of the Green function

This module assembles the chapter: a Green function `E` with pole `z₀` on a Riemann surface `X`
with `H¹(X,ℝ) = 0` has a holomorphic modulus `Φ` (holomorphic on `X`, with a logarithmic pole at
`z₀` and modulus `exp (-E)` off `z₀`) — the "periods of the conjugate differential are multiples of
`2π`" step of the hyperbolic case of uniformization (Hubbard, *Teichmüller theory* Vol. 1,
Chapter 1).

## Hypothesis

Everything is stated for `Work.UnitGreen.IsUnitGreenFunctionAt z₀ E` — the satisfiable
Green-function predicate (`E > 0` and harmonic off `z₀`, superlevel sets with compact closures,
logarithmic pole of coefficient one) consumed by `Submission.Gaps` and
`Submission.Assembly.uniformization_via_green`.  The old predicate `Submission.HasGreenFunctionE`
is *unsatisfiable* (`Work.Modulus.not_hasGreenFunctionE`), so statements conditioned on it are
vacuous; `Work.Modulus.isUnitGreenFunctionAt_of_hasGreenFunctionE` converts.

## What is proved

* `Work.Modulus.monodromyTrivial_of_simplyConnected` — **the analytic content**: on a simply
  connected surface every loop of `X ∖ {z₀}` is null-homotopic in `X`, so the periods of `*dE` are
  multiples of `2π` and `exp (-(E + iE*))` is single-valued;
* `Work.Modulus.poleOrderModulus_of_unitGreen` — the modulus identity forces the vanishing order
  one at `z₀`;
* `Work.Modulus.greenNoncompact` — `X` is not compact (so Hubbard 1.1.2 applies).

## The topological input

The only way the hypothesis `H¹(X,ℝ) = 0` of the uniformization theorem
(`Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)`) enters is through Hubbard Theorem 1.1.2,
formalised in the parallel subproject `Work.Spine` as
`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`: `π₁` of a connected non-compact
second countable surface is free, hence trivial under the hypothesis.  It is recorded below both as
an explicit hypothesis (`…_of_hubbard112`, a proved reduction) and as the minimal loop-level
consequence that the chapter actually consumes (`…_of_loops_trivial`).  The final assembly is then
the two-liner recorded in `Unconditional.lean`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Filter Set
open Classical

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The holomorphic modulus of the unit-pole Green function, assuming simple connectivity.**
This is the analytic content of the "periods are multiples of `2π`" step: on a simply connected
surface the conjugate of `E` is single-valued modulo `2π`, so `exp (-(E + iE*))` is a well defined
holomorphic function, and the modulus identity pins down its behaviour at the pole. -/
theorem exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) [SimplyConnectedSpace X] :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) := by
  obtain ⟨Φ, hhol, hne, hmod⟩ := monodromyTrivial_of_simplyConnected (z₀ := z₀) hE
  exact ⟨Φ, hhol, poleOrderModulus_of_unitGreen hE hhol hne hmod, hmod⟩

/-- **The statement requested for this subproject, verbatim.**  A strong Green function `E` with
pole `z₀` (`Submission.HasGreenFunctionE`) on a surface with `H¹(X,ℝ) = 0` has a holomorphic
modulus `Φ` with a logarithmic pole at `z₀` and `‖Φ x‖ = exp (-(E x))` off `z₀`.

⚠ **This is vacuously true**: `Submission.HasGreenFunctionE` is *unsatisfiable* on a charted space
(`Work.Modulus.not_hasGreenFunctionE` — the growth clause at the pole and the compact-superlevel-set
clause for `{E z₀ + 1 ≤ E}` contradict each other), so the proof is the elimination of the
hypothesis.  The mathematical content of the chapter is delivered with the satisfiable hypothesis
`Work.UnitGreen.IsUnitGreenFunctionAt`, which is the one the assembly consumes: see
`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction` and
`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112` below, and
`Submission/Work/Modulus/Unconditional.lean`. -/
theorem exists_holomorphic_modulus_of_greenFunction {z₀ x₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionE z₀ E)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) :=
  (not_hasGreenFunctionE hE).elim

/-- **The exact topological consequence consumed by this chapter.**

The only way the hypothesis `H¹(X,ℝ) = 0` enters the construction of the modulus is through the
statement that *every loop of the punctured surface `X ∖ {z₀}` is null-homotopic in `X`*: then the
period computation `Work.Modulus.greenPeriodHom_two_pi_zmultiples` applies to every loop and
`Work.Modulus.hasTrivialModulusMonodromy_of_periods` produces the single-valued modulus.

This is the minimum of the topological input: for an open surface it follows from freeness of `π₁`
(`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`), but the deliverable only uses this
consequence. -/
def AllLoopsOfPuncturedTrivialInX (z₀ : X) : Prop :=
  ∀ (u₀ : puncturedOpens z₀) (γ : FundamentalGroup (puncturedOpens z₀) u₀),
    FundamentalGroup.map (ContinuousMap.mk (Subtype.val : puncturedOpens z₀ → X)
      continuous_subtype_val) u₀ γ = 1

/-- **The holomorphic modulus of the unit-pole Green function from the minimal topological
input.**  This is `exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected` with the
simply-connectedness hypothesis replaced by the exact loop-level consequence that is used: every
loop of the punctured surface is null-homotopic in `X`. -/
theorem exists_holomorphic_modulus_of_unitGreenFunction_of_loops_trivial {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    (hloop : AllLoopsOfPuncturedTrivialInX (X := X) z₀) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) := by
  obtain ⟨Φ, hhol, hne, hmod⟩ :=
    hasTrivialModulusMonodromy_of_periods (z₀ := z₀) hE (fun u₀ γ =>
      greenPeriodHom_two_pi_zmultiples (z₀ := z₀) hE u₀ γ (hloop u₀ γ))
  exact ⟨Φ, hhol, poleOrderModulus_of_unitGreen hE hhol hne hmod, hmod⟩

/-- **The holomorphic modulus of the Green function**, with the topological input (Hubbard
Theorem 1.1.2, the subproject `Work.Spine`) passed as an explicit hypothesis `hSpine`, so that the
reduction is a proved theorem with no `sorryAx` in its closure.

`hSpine` is exactly `Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`. -/
theorem exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112 {z₀ x₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    (hSpine : (¬ CompactSpace X) → (x : X) →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) := by
  have hX : ¬ CompactSpace X := greenNoncompact hE
  haveI : SimplyConnectedSpace X := hSpine hX x₀ (inferInstance)
  exact exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected (z₀ := z₀) hE

/-! ## Aliases under the earlier names -/

/-- Earlier name of `exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected`. -/
theorem exists_holomorphic_modulus_of_simplyConnected {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) [SimplyConnectedSpace X] :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) :=
  exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected (z₀ := z₀) hE

/-- Earlier name of `exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112`. -/
theorem exists_holomorphic_modulus_of_greenFunction_of_hubbard112 {z₀ x₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    (hSpine : (¬ CompactSpace X) → (x : X) →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) :=
  exists_holomorphic_modulus_of_unitGreenFunction_of_hubbard112 (z₀ := z₀) (x₀ := x₀) hE hSpine

/-- Earlier name of `exists_holomorphic_modulus_of_unitGreenFunction_of_loops_trivial`. -/
theorem exists_holomorphic_modulus_of_greenFunction_of_loops_trivial {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    (hloop : AllLoopsOfPuncturedTrivialInX (X := X) z₀) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) :=
  exists_holomorphic_modulus_of_unitGreenFunction_of_loops_trivial (z₀ := z₀) hE hloop

end Work.Modulus
