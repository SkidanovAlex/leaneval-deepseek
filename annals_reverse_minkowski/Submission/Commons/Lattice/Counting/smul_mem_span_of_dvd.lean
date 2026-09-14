import Mathlib.LinearAlgebra.Span.Defs

namespace Commons.Lattice.Counting

theorem smul_mem_span_of_dvd {n r : ℕ} {v w : Fin r → Fin n → ℤ} (a : Fin r → ℤ)
    (hvw : ∀ i : Fin r, w i = a i • v i) {K : ℕ}
    (hdiv : ∀ i : Fin r, a i ∣ (K.factorial : ℤ)) (i : Fin r) :
    (K.factorial : ℤ) • v i ∈ Submodule.span ℤ (Set.range w) := by
  rcases hdiv i with ⟨c, hc⟩
  have hwi : w i ∈ Submodule.span ℤ (Set.range w) := by
    apply Submodule.mem_span.2
    intro p hp
    exact hp (Set.mem_range_self i)
  have hsmul : c • w i ∈ Submodule.span ℤ (Set.range w) := by
    exact Submodule.smul_mem (Submodule.span ℤ (Set.range w)) c hwi
  have hmain : (K.factorial : ℤ) • v i = c • w i := by
    calc
      (K.factorial : ℤ) • v i = (a i * c) • v i := by rw [hc]
      _ = c • (a i • v i) := by rw [mul_comm (a i) c, mul_smul]
      _ = c • w i := by rw [hvw i]
  rwa [hmain]

end Commons.Lattice.Counting