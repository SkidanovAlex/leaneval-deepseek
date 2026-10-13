import Mathlib

namespace Work.DSM2p

theorem N4g_aeval_mem {C L : Type*} [CommRing C] [CommRing L] [Algebra C L]
    (U : Subring L) (hU : ∀ c : C, algebraMap C L c ∈ U)
    {a : L} (ha : a ∈ U) (g : Polynomial C) :
    Polynomial.aeval a g ∈ U := by
  rw [Polynomial.aeval_eq_sum_range]
  apply U.sum_mem
  intro i _
  rw [Algebra.smul_def]
  exact U.mul_mem (hU _) (U.pow_mem ha i)

end Work.DSM2p
