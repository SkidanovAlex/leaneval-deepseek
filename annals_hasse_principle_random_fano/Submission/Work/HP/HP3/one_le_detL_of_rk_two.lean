import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.detL_ge_one

namespace Work.HP.HP3

/-- The covolume `detL L` of a rank-`2` (indeed of any nonzero) integral lattice `L ⊆ ℤ^ι` is
at least `1`.  Suggested route: `Lat/detL_basis_gram.lean` gives `detL L = √(det G)` for the Gram
matrix of a `ℤ`-basis of `L`; the Gram matrix of independent integer vectors has integer entries
and is positive definite, so its determinant is a positive integer, hence `≥ 1`. -/
theorem one_le_detL_of_rk_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (h : rk L = 2) : 1 ≤ detL L :=
  Work.HP.Lat.detL_ge_one L

end Work.HP.HP3
