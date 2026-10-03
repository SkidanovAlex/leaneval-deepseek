import Mathlib

namespace Work.KMTAreas.A7rand

/-- **Abel summation by parts.**  For complex sequences `d`, `w`,
`∑_{k<K} d_k w_k = (∑_{k<K} d_k) w_{K-1} + ∑_{k<K-1} (∑_{j≤k} d_j) (w_k - w_{k+1})`.

This is `Finset.sum_range_by_parts` (with `f = w`, `g = d`) after commuting the two
real/complex variables in the product and rewriting `(w_{k+1} - w_k) = -(w_k - w_{k+1})`. -/
theorem sum_range_abel (K : ℕ) (d w : ℕ → ℂ) :
    ∑ k ∈ Finset.range K, d k * w k
      = (∑ k ∈ Finset.range K, d k) * w (K - 1)
        + ∑ k ∈ Finset.range (K - 1), (∑ j ∈ Finset.range (k + 1), d j) * (w k - w (k + 1)) := by
  have h := Finset.sum_range_by_parts (f := w) (g := d) (n := K)
  simp only [smul_eq_mul] at h
  rw [show (∑ k ∈ Finset.range K, d k * w k) = ∑ k ∈ Finset.range K, w k * d k from
        Finset.sum_congr rfl (fun k _ => mul_comm (d k) (w k)), h]
  rw [mul_comm (∑ k ∈ Finset.range K, d k) (w (K - 1))]
  have hU : (∑ k ∈ Finset.range (K - 1), (∑ j ∈ Finset.range (k + 1), d j) * (w k - w (k + 1)))
      = - ∑ x ∈ Finset.range (K - 1), (w (x + 1) - w x) * ∑ i ∈ Finset.range (x + 1), d i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hU]
  ring

end Work.KMTAreas.A7rand
