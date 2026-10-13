import Mathlib
import Submission.Work.DSM2p.Basic

namespace Work.DSM2p

/-- If `x` lies in every power of the ideal `I`, then its image in the `I`-adic completion
`AdicCompletion I E` vanishes. -/
theorem adicCompletion_eq_zero_of_mem_pow {E : Type*} [CommRing E] (I : Ideal E) {x : E}
    (h : ∀ n : ℕ, x ∈ I ^ n) : AdicCompletion.of I E x = 0 := by
  ext n
  rw [AdicCompletion.of_apply]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (by rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact h n)

end Work.DSM2p
