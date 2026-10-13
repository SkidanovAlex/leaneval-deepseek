import Mathlib

namespace Work.DSM2p

theorem N4c_mem_span_C_of_coeff_mem {C : Type*} [CommRing C] (ϖ : C) (H : Polynomial C)
    (h : ∀ n, H.coeff n ∈ Ideal.span {ϖ}) :
    H ∈ Ideal.span {Polynomial.C ϖ} := by
  rw [Ideal.mem_span_singleton]
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  exact Ideal.mem_span_singleton.mp (h i)

end Work.DSM2p
