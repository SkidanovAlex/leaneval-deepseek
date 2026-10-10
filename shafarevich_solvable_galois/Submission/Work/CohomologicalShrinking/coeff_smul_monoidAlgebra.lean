import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.ZMod.Defs
import Submission.Work.CohomologicalShrinking.Models
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking

/-- The coefficient at `z` of `g • y` (where `g` acts by left multiplication on the group
algebra `𝔽_p[G]`) equals the coefficient of `y` at `g⁻¹ * z`. -/
theorem coeff_smul_monoidAlgebra (p : ℕ) (G : Type*) [Group G] (g z : G)
    (y : MonoidAlgebra (ZMod p) G) :
    (g • y).coeff z = y.coeff (g⁻¹ * z) := by
  rw [smul_monoidAlgebra, MonoidAlgebra.coeff_single_mul_eq_mul_coeff (g⁻¹ * z) ?_, one_mul]
  intro m' _
  constructor
  · intro h; rw [← h, inv_mul_cancel_left]
  · intro h; rw [h, mul_inv_cancel_left]

end Work.CohomologicalShrinking
