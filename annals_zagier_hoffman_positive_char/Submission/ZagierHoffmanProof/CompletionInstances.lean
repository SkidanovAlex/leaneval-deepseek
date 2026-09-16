import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Submission.Commons.Topology.Algebra.Valued.nonarchimedeanAddGroup
import Submission.Commons.Topology.Algebra.Valued.nonarchimedeanRing

set_option autoImplicit false

open Polynomial RatFunc
open scoped WithZero Topology

/-!
# Instance glue for `RatFunc.CompletionAtInfty F`

`RatFunc.CompletionAtInfty F` is the completion of `F(t)` at infinity, i.e. the valued
field obtained from `RatFunc.inftyValued`.  Mathlib does not register global
`CompleteSpace`/`NonarchimedeanAddGroup`/`NonarchimedeanRing` instances for this *def* (the
general instances are stated for `UniformSpace.Completion X` and do not fire because the
uniform-space instance used at the definition site is the scoped valuation one).  Here we
register the instances we need, with the correct (infinite-place) uniform structure made
available locally.
-/

namespace ZagierHoffmanPositiveChar

/-- `F(t)` with the valuation at infinity is a nonarchimedean additive group.
The topology is the one induced by `RatFunc.inftyValued`. -/
noncomputable instance instNonarchimedeanAddGroupRatFunc (F : Type*) [Field F]
    [DecidableEq (RatFunc F)] :
    letI : UniformSpace (RatFunc F) := (RatFunc.inftyValued F).toUniformSpace
    letI : TopologicalSpace (RatFunc F) := UniformSpace.toTopologicalSpace
    NonarchimedeanAddGroup (RatFunc F) := by
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  letI : UniformSpace (RatFunc F) := (RatFunc.inftyValued F).toUniformSpace
  letI : TopologicalSpace (RatFunc F) := UniformSpace.toTopologicalSpace
  exact Commons.Topology.Algebra.Valued.nonarchimedeanAddGroup (K := RatFunc F) (Γ₀ := ℤᵐ⁰)

/-- `F(t)` with the valuation at infinity is a nonarchimedean topological ring. -/
noncomputable instance instNonarchimedeanRingRatFunc (F : Type*) [Field F]
    [DecidableEq (RatFunc F)] :
    letI : UniformSpace (RatFunc F) := (RatFunc.inftyValued F).toUniformSpace
    letI : TopologicalSpace (RatFunc F) := UniformSpace.toTopologicalSpace
    NonarchimedeanRing (RatFunc F) := by
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  letI : UniformSpace (RatFunc F) := (RatFunc.inftyValued F).toUniformSpace
  letI : TopologicalSpace (RatFunc F) := UniformSpace.toTopologicalSpace
  exact Commons.Topology.Algebra.Valued.nonarchimedeanRing (K := RatFunc F) (Γ₀ := ℤᵐ⁰)

/-- The completion of `F(t)` at infinity is complete. -/
noncomputable instance instCompleteSpaceCompletionAtInfty (F : Type*) [Field F]
    [DecidableEq (RatFunc F)] : CompleteSpace (RatFunc.CompletionAtInfty F) := by
  letI : UniformSpace (RatFunc F) := (RatFunc.inftyValued F).toUniformSpace
  change CompleteSpace (UniformSpace.Completion (RatFunc F))
  infer_instance

/-- The completion of `F(t)` at infinity is a nonarchimedean additive group. -/
noncomputable instance instNonarchimedeanAddGroupCompletionAtInfty (F : Type*) [Field F]
    [DecidableEq (RatFunc F)] : NonarchimedeanAddGroup (RatFunc.CompletionAtInfty F) := by
  letI : UniformSpace (RatFunc F) := (RatFunc.inftyValued F).toUniformSpace
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  letI : TopologicalSpace (RatFunc F) := UniformSpace.toTopologicalSpace
  haveI : NonarchimedeanAddGroup (RatFunc F) := instNonarchimedeanAddGroupRatFunc F
  change NonarchimedeanAddGroup (UniformSpace.Completion (RatFunc F))
  infer_instance

/-- The completion of `F(t)` at infinity is a nonarchimedean topological ring. -/
noncomputable instance instNonarchimedeanRingCompletionAtInfty (F : Type*) [Field F]
    [DecidableEq (RatFunc F)] : NonarchimedeanRing (RatFunc.CompletionAtInfty F) := by
  letI : UniformSpace (RatFunc F) := (RatFunc.inftyValued F).toUniformSpace
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  letI : TopologicalSpace (RatFunc F) := UniformSpace.toTopologicalSpace
  haveI : NonarchimedeanRing (RatFunc F) := instNonarchimedeanRingRatFunc F
  change NonarchimedeanRing (UniformSpace.Completion (RatFunc F))
  infer_instance

end ZagierHoffmanPositiveChar
