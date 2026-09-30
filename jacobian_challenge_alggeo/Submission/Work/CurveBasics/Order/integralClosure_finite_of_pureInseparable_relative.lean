import Mathlib
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.integralClosure_adjoin_finite_of_transcendental
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

open scoped IntermediateField.algebraAdjoinAdjoin in
open Work.CurveBasics in
/-- **The purely inseparable relative step of the finiteness of the integral closure of `k[h]`.**

`B = k[h]^int ⊆ K(C)` is the integral closure of `k[h]` in the function field; it is the
normalisation of the affine chart `𝔸¹ = Spec k[h]` inside `C`.  Given an intermediate field
`k(h) ⊆ M ⊆ K(C)` with `K(C)/M` purely inseparable and with the integral closure of `k[h]` in `M`
already a finite `k[h]`-module, the integral closure of `k[h]` in `K(C)` is finite as well.

The proof does not use the extra hypotheses: `K(C)/k(h)` is *always* finite dimensional when `h`
is transcendental (`Work.CurveBasics.Order.finiteDimensional_adjoin_functionField`), and the
integral closure of `k[x]` in a finite extension of `k(x)` is a finite `k[x]`-module
(`Work.CurveBasics.Order.integralClosure_adjoin_finite_of_transcendental`, the classical statement
that a finitely generated algebra over a field is Japanese, hence has finite normalisation). -/
theorem integralClosure_finite_of_pureInseparable_relative {k : Type*} [Field k] (C : Curve k)
    (h : C.functionField) (hh : Transcendental k h)
    (M : IntermediateField ↥(IntermediateField.adjoin k ({h} : Set C.functionField))
      C.functionField)
    [FiniteDimensional ↥M C.functionField]
    [Module.Finite (C.ordBase h) (integralClosure (C.ordBase h) ↥M)]
    (hpure : ∀ x : C.functionField, ∃ n : ℕ, x ^ ((ringChar k) ^ n) ∈ M) :
    Module.Finite (C.ordBase h) (C.ordClosure h) := by
  haveI := finiteDimensional_adjoin_functionField C hh
  exact integralClosure_adjoin_finite_of_transcendental h hh

end Work.CurveBasics.Order
