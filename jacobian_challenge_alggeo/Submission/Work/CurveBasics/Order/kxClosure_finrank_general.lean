import Mathlib
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Order.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Classical IntermediateField.algebraAdjoinAdjoin
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.CurveBasics.Order

open Work.CurveBasics in
/-- **The rank of the integral closure over `k[x]` is the degree of `K(C)` over `k(x)`.**

This is the separability-free version of `IsIntegralClosure.rank`: the only place the
separability hypothesis is used there is to obtain `Module.Free A C` and `IsNoetherian A C`
for the integral closure `C`.  Here `Module.Finite A C` is assumed and `A = k[x]` is a
PID and a domain, so `C` is torsion-free (it is a subalgebra of the field `K(C)`) and
therefore free over `A`.  The remaining ingredients -- `IsIntegralClosure.isLocalization`
(which needs only `Algebra.IsAlgebraic`) and the localization of a basis -- carry over
verbatim. -/
theorem kxClosure_finrank_general {k : Type*} [Field k] (C : Curve k) (x : C.functionField)
    (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField]
    [Module.Finite ↥(Algebra.adjoin k ({x} : Set C.functionField))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField)] :
    Module.finrank ↥(Algebra.adjoin k ({x} : Set C.functionField))
        ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField)
      = Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
          C.functionField := by
  haveI : Module.IsTorsionFree ↥(Algebra.adjoin k ({x} : Set C.functionField))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField) :=
    IsIntegralClosure.isTorsionFree (R := ↥(Algebra.adjoin k ({x} : Set C.functionField)))
      (B := C.functionField)
  haveI : Module.Free ↥(Algebra.adjoin k ({x} : Set C.functionField))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField) :=
    Module.free_of_finite_type_torsion_free'
  haveI : IsLocalization (Algebra.algebraMapSubmonoid
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField)
      (nonZeroDivisors ↥(Algebra.adjoin k ({x} : Set C.functionField)))) C.functionField :=
    IsIntegralClosure.isLocalization _ ↥(IntermediateField.adjoin k ({x} : Set C.functionField)) _ _
  let b := Module.Basis.localizationLocalization
      (↥(IntermediateField.adjoin k ({x} : Set C.functionField)))
      (nonZeroDivisors ↥(Algebra.adjoin k ({x} : Set C.functionField)))
      C.functionField
      (Module.Free.chooseBasis ↥(Algebra.adjoin k ({x} : Set C.functionField))
        ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField))
  rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis b]

end Work.CurveBasics.Order
