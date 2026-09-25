import Mathlib
import Submission.Work.NN.Core.DbarCnPertAux

namespace Work.NN.Core

/-- `Bop A z` and `BopBar A z` are, although only `ℝ`-linear by construction, actually
`ℂ`-linear: their coordinates are `(Bop A z v) k = Σ_j v j * β k j z` and
`(BopBar A z v) k = Σ_j v j * conj (β k j z)`, i.e. complex matrix–vector products with the
scalar on the left of `v j`.  Hence scalar multiplication by a complex number is respected. -/
theorem Bop_map_smul {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (z v : Cn n) (c : ℂ) :
    Bop A z (c • v) = c • Bop A z v ∧ BopBar A z (c • v) = c • BopBar A z v := by
  constructor <;>
    · ext k
      simp only [Bop_apply, BopBar_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring

end Work.NN.Core
