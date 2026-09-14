import Mathlib

namespace Commons.Topology.Metric

/-- Changing the `b`-th coordinate of `w : Fin N → E` by subtracting the two
corresponding modified functions leaves a vector supported only at `b`. -/
private lemma update_sub_update {E : Type*} [AddCommGroup E] {N : ℕ}
    (w : Fin N → E) (b : Fin N) (a a' : E) :
    Function.update w b a - Function.update w b a' = Pi.single b (a - a') := by
  funext i
  simp only [Pi.sub_apply, Function.update_apply, Pi.single_apply]
  by_cases h : i = b <;> simp [h]

/-- In `EuclideanSpace E (Fin N)`, changing a single coordinate does not change the distance:
`dist (Function.update w b a) (Function.update w b a') = dist a a'`. -/
theorem dist_toLp_update {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (w : Fin N → E) (b : Fin N) (a a' : E) :
    dist (WithLp.toLp 2 (Function.update w b a) : EuclideanSpace E (Fin N))
      (WithLp.toLp 2 (Function.update w b a')) = dist a a' := by
  rw [dist_eq_norm, dist_eq_norm, ← WithLp.toLp_sub]
  rw [update_sub_update, PiLp.toLp_single, PiLp.norm_single]

end Commons.Topology.Metric
