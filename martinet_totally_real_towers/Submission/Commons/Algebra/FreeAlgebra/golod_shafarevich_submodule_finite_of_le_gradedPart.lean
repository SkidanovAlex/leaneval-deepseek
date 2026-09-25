import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_relator_right_mul_finrank_le

namespace Commons.Algebra.FreeAlgebra

set_option linter.style.haveILetI false in
theorem golod_shafarevich_submodule_finite_of_le_gradedPart
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (n : ℕ) (A : Submodule K (FreeAlgebra K ι))
    (hA : A ≤ golodShafarevich_gradedPart K ι n) :
    Module.Finite K A := by
  haveI : Module.Finite K ↥(golodShafarevich_gradedPart K ι n) :=
    golodShafarevich_gradedPart_finiteDimensional (K := K) (ι := ι) n
  let e := Submodule.comapSubtypeEquivOfLe hA
  exact Module.Finite.equiv e

end Commons.Algebra.FreeAlgebra
