import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Algebra.Valued.ValuedField

set_option autoImplicit false

open Polynomial RatFunc
open scoped WithZero Topology
open WithZero

/-!
# Valuations of polynomial images inside `CompletionAtInfty F`

We record how the (unique extension of the) place at infinity evaluates on elements of
`F(t)` embedded into its completion `RatFunc.CompletionAtInfty F`.

Key API trick used below: write the image of a rational function as
`UniformSpace.Completion.coe' x` (rather than relying on the derived `Coe` instance of
`RatFunc.CompletionAtInfty`), with the `Valued (RatFunc F) ℤᵐ⁰` instance made local.
-/

namespace ZagierHoffmanPositiveChar

/-- The value of the extended place at infinity on (the completion-image of) a nonzero
polynomial `p` is `exp (natDegree p)`. -/
theorem inftyValued_v_polynomial (F : Type*) [Field F] [DecidableEq (RatFunc F)]
    (p : F[X]) (hp : p ≠ 0) :
    Valued.v ((p : RatFunc F) : RatFunc.CompletionAtInfty F) = exp (p.natDegree : ℤ) := by
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  rw [RatFunc.valuedCompletionAtInfty.def]
  change Valued.extensionValuation
    (UniformSpace.Completion.coe' (p : RatFunc F)) = exp (p.natDegree : ℤ)
  rw [Valued.extensionValuation_apply_coe]
  exact RatFunc.inftyValuation.polynomial F hp

/-- The value of the extended place at infinity on (the completion-image of) a nonzero
rational function `x` is `exp (intDegree x)`. -/
theorem inftyValued_v_ratFunc (F : Type*) [Field F] [DecidableEq (RatFunc F)]
    (x : RatFunc F) (hx : x ≠ 0) :
    Valued.v ((x : RatFunc F) : RatFunc.CompletionAtInfty F) = exp x.intDegree := by
  letI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  rw [RatFunc.valuedCompletionAtInfty.def]
  change Valued.extensionValuation (UniformSpace.Completion.coe' x) = exp x.intDegree
  rw [Valued.extensionValuation_apply_coe]
  exact RatFunc.inftyValuation_of_nonzero F hx

end ZagierHoffmanPositiveChar
