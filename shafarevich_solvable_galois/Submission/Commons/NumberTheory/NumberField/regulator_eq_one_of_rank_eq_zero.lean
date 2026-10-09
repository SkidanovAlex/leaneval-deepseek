import Mathlib.NumberTheory.NumberField.Units.Regulator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
open Matrix

namespace Commons.NumberTheory.NumberField

/-- For a number field `K` of unit rank `0` (i.e. whose unit group is finite), the regulator
`regulator K` equals `1`: the `ℤ`-lattice of units is trivial, so its covolume is the absolute
value of the determinant of a matrix with empty index type, which is `1`. -/
theorem regulator_eq_one_of_rank_eq_zero (K : Type*) [Field K] [NumberField K]
    (h : NumberField.Units.rank K = 0) : NumberField.Units.regulator K = 1 := by
  classical
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = 0 := by
    rw [show Fintype.card {w : InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K by
      simp [NumberField.Units.rank], h]
  rw [NumberField.Units.regulator_eq_det']
  rw [Matrix.det_eq_one_of_card_eq_zero hcard, abs_one]

end Commons.NumberTheory.NumberField