import Mathlib.NumberTheory.NumberField.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.QuadraticExtension

open Polynomial

theorem numberField_adjoinRoot_X_sq_sub_C
    {K : Type*} [Field K] [NumberField K] {a : K} (ha : a ≠ 0)
    [Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C a))] :
    NumberField (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C a)) := by
  let f : Polynomial K := Polynomial.X ^ 2 - Polynomial.C a
  have hf : f ≠ 0 := by
    intro h
    have hroot : Polynomial.X ^ 2 = Polynomial.C a := sub_eq_zero.mp h
    have ha' : a = 0 := by
      simpa using congrArg (fun p : Polynomial K => p.coeff 0) hroot.symm
    exact ha ha'
  have hfin : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf).finite
  exact @NumberField.of_module_finite K (AdjoinRoot f) _ _ _ _ hfin

end Commons.NumberTheory.QuadraticExtension