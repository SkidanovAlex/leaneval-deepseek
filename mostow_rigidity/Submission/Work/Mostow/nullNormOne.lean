import Mathlib
import Submission.Work.Mostow.Hyper

namespace Work.Mostow

/-- A vector `z` of `ℝ^{Fin n ⊕ Fin 1}` whose time coordinate is non-zero and whose spatial
squared norm equals the square of its time coordinate gives a unit vector when the spatial
part is divided by the time coordinate.  (Equivalently: the spatial part of a null vector,
renormalised by its time coordinate, lies on the unit sphere.) -/
theorem nullNormOne {n : ℕ} (z : Fin n ⊕ Fin 1 → ℝ)
    (h : (∑ i : Fin n, z (Sum.inl i) ^ 2) = z (Sum.inr 0) ^ 2) (ht : z (Sum.inr 0) ≠ 0) :
    ‖(WithLp.toLp 2 (fun i : Fin n => z (Sum.inl i) / z (Sum.inr 0)) : Submission.Mostow.E n)‖ = 1 := by
  set c : ℝ := z (Sum.inr 0) with hc
  have hsq : ‖(WithLp.toLp 2 (fun i : Fin n => z (Sum.inl i) / c) :
      Submission.Mostow.E n)‖ ^ 2 = 1 := by
    rw [Submission.Mostow.Hyper.norm_sq_eq_sum]
    simp only [← sq]
    rw [show (∑ x, (z (Sum.inl x) / c) ^ 2) = (∑ x, z (Sum.inl x) ^ 2) / c ^ 2 from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ => by rw [div_pow],
      h, div_self (pow_ne_zero 2 ht)]
  have hnn : (0 : ℝ) ≤ ‖(WithLp.toLp 2 fun i => z (Sum.inl i) / c : Submission.Mostow.E n)‖ :=
    norm_nonneg _
  rcases sq_eq_one_iff.mp hsq with h' | h'
  · exact h'
  · linarith

end Work.Mostow
