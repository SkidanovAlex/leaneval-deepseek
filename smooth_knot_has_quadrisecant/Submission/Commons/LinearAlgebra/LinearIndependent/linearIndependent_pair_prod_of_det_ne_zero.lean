import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace Commons.LinearAlgebra.LinearIndependent

/-- Two vectors in the plane are linearly independent over ℝ whenever their
2-by-2 determinant (with the two vectors as rows) is nonzero. -/
lemma linearIndependent_pair_prod_of_det_ne_zero {u v : ℝ × ℝ}
    (hD : u.1 * v.2 - u.2 * v.1 ≠ 0) : LinearIndependent ℝ ![u, v] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hv
    have hv' : v = 0 := by simpa using hv
    apply hD
    subst v
    simp
  · intro a hu
    have hu' : a • v = u := by simpa using hu
    have hu1 : u.1 = a * v.1 := by
      simpa using congrArg Prod.fst hu'.symm
    have hu2 : u.2 = a * v.2 := by
      simpa using congrArg Prod.snd hu'.symm
    apply hD
    rw [hu1, hu2]
    ring

end Commons.LinearAlgebra.LinearIndependent