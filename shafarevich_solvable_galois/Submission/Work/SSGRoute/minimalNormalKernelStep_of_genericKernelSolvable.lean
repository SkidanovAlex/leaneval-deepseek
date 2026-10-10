import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Shrink
import Mathlib.Data.Fintype.Shrink
import Mathlib.SetTheory.Cardinal.NatCard
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SSGRoute/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared vocabulary: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit — put any new shared definition in your own file). The proved class-field-theory library is available as NK.*. Siblings run in parallel; import them when they land.

# Guidance: universe transport for the deep input

`Work.GenericKernelReduction.minimalNormalKernelStep_of_genericKernel h : MinimalNormalKernelStep.{0}` exists.
The cone's `minimalNormalKernelStep` is universe-polymorphic `.{u}`.

# What this file does

The deep hypothesis `Work.GenericKernelReduction.GenericKernelSolvable` is a statement about
number fields over the fixed algebraic closure `AlgebraicClosure ℚ`, hence lives in universe `0`;
consequently `Work.GenericKernelReduction.realizable_of_genericKernel` only realizes groups
`G : Type` (universe `0`).  The target `Submission.MinimalNormalKernelStep` is universe
polymorphic, so we transport an arbitrary finite solvable `G : Type u` down to universe `0`
along `Shrink G` (`Shrink.{0,u} G`, which is a group isomorphic to `G` via `Shrink.mulEquiv`
and finite and solvable because `G` is), realize it there, and transport the realization back
along `RealizableOver.of_mulEquiv`.
-/

namespace Work.SSGRoute

universe u

open SSGRoute

/-- **Shafarevich's theorem from the generic-kernel hypothesis, in every universe**: every
finite solvable group is realizable over `ℚ`.  This is
`Work.GenericKernelReduction.realizable_of_genericKernel` transported from `Type` to `Type u`
along `Shrink`. -/
theorem realizableOver_rat_of_genericKernelSolvable
    (h : Work.GenericKernelReduction.GenericKernelSolvable) :
    ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G], Submission.RealizableOver ℚ G := by
  intro G _ _ _
  -- `G` is finite, hence small: it embeds in `Fin (Nat.card G) : Type`.
  have hsmall : Small.{0, u} G := Small.mk' (Finite.equivFin G)
  haveI := hsmall
  -- `Shrink G` is solvable because it is isomorphic to `G`.
  have hsol : Group.IsSolvable (Shrink G) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Shrink.mulEquiv (α := G)).toMonoidHom) (Shrink.mulEquiv (α := G)).injective
  haveI := hsol
  exact Submission.RealizableOver.of_mulEquiv (Shrink.mulEquiv (α := G))
    (Work.GenericKernelReduction.realizable_of_genericKernel h (Shrink G))

/-- **The deep input of the development from the generic-kernel hypothesis.**

`Submission.MinimalNormalKernelStep` is universe polymorphic, while the generic-kernel
hypothesis only realizes groups in universe `0`; the transport is by `Shrink`
(`realizableOver_rat_of_genericKernelSolvable` above).  Since the conclusion of
`MinimalNormalKernelStep` is unconditional once every finite solvable group is realizable, the
embedding hypotheses (`A`, minimality of `A`, realizability of `G ⧸ A`) are simply discarded. -/
theorem minimalNormalKernelStep_of_genericKernelSolvable
    (h : Work.GenericKernelReduction.GenericKernelSolvable) :
    Submission.MinimalNormalKernelStep := by
  intro G _ _ _ A _ _ _ _
  exact realizableOver_rat_of_genericKernelSolvable h G

end Work.SSGRoute
