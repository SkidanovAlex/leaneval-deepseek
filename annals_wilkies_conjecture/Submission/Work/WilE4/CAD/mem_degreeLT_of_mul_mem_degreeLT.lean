import Mathlib

namespace Work.WilE4.CAD

lemma mem_degreeLT_of_mul_mem_degreeLT {m k : ℕ} {p c : Polynomial ℝ} (hp : p ≠ 0)
    (hpk : p.natDegree + k = m) (hc : c ≠ 0) (h : p * c ∈ Polynomial.degreeLT ℝ m) :
    c ∈ Polynomial.degreeLT ℝ k := by
  rw [Polynomial.mem_degreeLT] at h ⊢
  rw [Polynomial.degree_eq_natDegree (mul_ne_zero hp hc), Polynomial.natDegree_mul hp hc] at h
  have hm : p.natDegree + c.natDegree < m := by exact_mod_cast h
  have hk : c.natDegree < k := by omega
  rw [Polynomial.degree_eq_natDegree hc]
  exact_mod_cast hk

end Work.WilE4.CAD
