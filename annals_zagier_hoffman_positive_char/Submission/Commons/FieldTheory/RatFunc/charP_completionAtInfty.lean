import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.SimpleRing.Principal

open scoped WithZero

namespace Commons.FieldTheory.RatFunc

theorem charP_completionAtInfty (F : Type*) [Field F] [DecidableEq (RatFunc F)] {p : ℕ} [CharP F p] : CharP (RatFunc.CompletionAtInfty F) p := by
  -- `RatFunc.CompletionAtInfty F` is the completion of `F(t)` at the place at infinity.
  -- Make the corresponding uniform space (and valuation) available as local instances so
  -- that the general completion API applies to it.
  let : UniformSpace (RatFunc F) := (RatFunc.inftyValued F).toUniformSpace
  let : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  let : TopologicalSpace (RatFunc F) := UniformSpace.toTopologicalSpace
  have : T0Space (RatFunc F) := ValuedRing.separated
  change CharP (UniformSpace.Completion (RatFunc F)) p
  -- The completion map `F(t) → F((t⁻¹))` is injective, so the characteristic is unchanged.
  refine charP_of_injective_algebraMap (R := RatFunc F) ?_ p
  intro a b hab
  have h1 : (a : UniformSpace.Completion (RatFunc F)) =
      (b : UniformSpace.Completion (RatFunc F)) := by
    simpa [UniformSpace.Completion.algebraMap_def] using hab
  exact UniformSpace.Completion.coe_inj.mp h1

end Commons.FieldTheory.RatFunc