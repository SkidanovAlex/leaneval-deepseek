import Mathlib

namespace Work.KMTAreas.Khintchine

/-- For any finite index type and any seminormed additive commutative group `E`, the sum of the
`p`-th powers of the `ℝ≥0∞`-norms of the values `f i` equals `ofReal` of the sum of the `p`-th
powers of the real norms, for `p > 0`.

This is the bridge between the real-valued `ℓ^p`-sum `∑ ‖f i‖ ^ p` and its `ℝ≥0∞`-valued
counterpart `∑ ‖f i‖ₑ ^ p` used throughout the layer-cake/Lp bookkeeping. -/
lemma sum_enorm_rpow {ι : Type*} [Fintype ι] {E : Type*} [SeminormedAddCommGroup E]
    (f : ι → E) {p : ℝ} (hp : 0 < p) :
    (∑ i, ‖f i‖ₑ ^ p) = ENNReal.ofReal (∑ i, ‖f i‖ ^ p) := by
  rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := fun i => ‖f i‖ ^ p)
    (fun i _ => Real.rpow_nonneg (norm_nonneg _) p)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]

end Work.KMTAreas.Khintchine
