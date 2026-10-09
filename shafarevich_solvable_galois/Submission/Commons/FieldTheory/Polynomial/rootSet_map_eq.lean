import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Polynomial

lemma rootSet_map_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Polynomial K) :
    (p.map (algebraMap K L)).rootSet L = p.rootSet L := by
  classical
  simp only [Polynomial.rootSet, Polynomial.aroots_map]

end Commons.FieldTheory.Polynomial