import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.QuadraticExtension

theorem finrank_adjoinRoot_X_sq_sub_C
    {K : Type*} [Field K] {a : K} (ha : a ≠ 0)
    [Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C a))] :
    Module.finrank K (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C a)) = 2 := by
  have _ : a ≠ 0 := ha
  let f : Polynomial K := Polynomial.X ^ 2 - Polynomial.C a
  have hf : f ≠ 0 := (Fact.out : Irreducible f).ne_zero
  rw [show Module.finrank K (AdjoinRoot f) = f.natDegree by
    simpa using (PowerBasis.finrank (AdjoinRoot.powerBasis hf))]
  simp [f]

end Commons.NumberTheory.QuadraticExtension