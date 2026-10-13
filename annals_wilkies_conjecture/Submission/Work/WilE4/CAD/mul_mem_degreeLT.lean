import Mathlib

namespace Work.WilE4.CAD

lemma mul_mem_degreeLT {m k : ℕ} {p c : Polynomial ℝ} (hp : p.natDegree + k = m)
    (hc : c ∈ Polynomial.degreeLT ℝ k) : p * c ∈ Polynomial.degreeLT ℝ m := by
  rw [Polynomial.mem_degreeLT] at hc ⊢
  rcases eq_or_ne c 0 with hc0 | hc0
  · simp [hc0]
  have hclt : c.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hc0).mpr hc
  rcases eq_or_ne p 0 with hp0 | hp0
  · simp [hp0]
  have hmul : (p * c).natDegree < m := by
    have h := Polynomial.natDegree_mul_le (p := p) (q := c)
    omega
  exact (Polynomial.natDegree_lt_iff_degree_lt (mul_ne_zero hp0 hc0)).mp hmul

end Work.WilE4.CAD
