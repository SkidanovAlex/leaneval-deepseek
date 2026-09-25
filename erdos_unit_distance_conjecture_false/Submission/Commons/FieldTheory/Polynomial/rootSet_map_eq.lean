import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Polynomial

lemma rootSet_map_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Polynomial K) :
    (p.map (algebraMap K L)).rootSet L = p.rootSet L := by
  classical
  simp only [Polynomial.rootSet, Polynomial.aroots_map]

end Commons.FieldTheory.Polynomial