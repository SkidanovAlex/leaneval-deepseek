import Mathlib.RingTheory.Ideal.Operations

namespace Commons.Algebra.Ideal

theorem mul_sup_span_eq_of_isCoprime {R : Type*} [CommRing R] {z m n : R}
    (hcop : IsCoprime m n) (hz : z ∣ m * n) :
    (Ideal.span {z} ⊔ Ideal.span {m}) * (Ideal.span {z} ⊔ Ideal.span {n}) = Ideal.span {z} := by
  have hspanm : Ideal.span {z} ⊔ Ideal.span {m} = Ideal.span ({z, m} : Set R) :=
    (Ideal.span_insert z ({m} : Set R)).symm
  have hspann : Ideal.span {z} ⊔ Ideal.span {n} = Ideal.span ({z, n} : Set R) :=
    (Ideal.span_insert z ({n} : Set R)).symm
  rw [hspanm, hspann, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact Ideal.mem_span_singleton.mpr (dvd_mul_right z z)
    · rw [h]; exact Ideal.mem_span_singleton.mpr (dvd_mul_right z n)
    · rw [h]; exact Ideal.mem_span_singleton.mpr (dvd_mul_left z m)
    · rw [h]; exact Ideal.mem_span_singleton.mpr hz
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, hab⟩ := hcop
    have hmem : a * (m * z) + b * (z * n) ∈
        Ideal.span ({z * z, z * n, m * z, m * n} : Set R) := by
      apply Ideal.add_mem
      · exact Ideal.mul_mem_left _ a (Ideal.subset_span (by simp))
      · exact Ideal.mul_mem_left _ b (Ideal.subset_span (by simp))
    have h1 : a * (m * z) + b * (z * n) = z := by
      rw [show a * (m * z) + b * (z * n) = (a * m + b * n) * z by ring, hab, one_mul]
    rwa [h1] at hmem

end Commons.Algebra.Ideal