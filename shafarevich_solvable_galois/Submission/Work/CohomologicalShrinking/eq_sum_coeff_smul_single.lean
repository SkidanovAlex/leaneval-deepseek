import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking

theorem eq_sum_coeff_smul_single (p : ℕ) (G : Type*) [Group G] [Fintype G]
    (y : MonoidAlgebra (ZMod p) G) :
    y = ∑ g : G, (y.coeff g) • MonoidAlgebra.single g (1 : ZMod p) := by
  rw [← MonoidAlgebra.sum_coeff_single y]
  rw [Finsupp.sum_fintype y.coeff (fun g c => MonoidAlgebra.single g c)
        (fun i => MonoidAlgebra.single_zero i)]
  apply Finset.sum_congr rfl
  intro g _
  rw [MonoidAlgebra.smul_single]
  simp

end Work.CohomologicalShrinking
