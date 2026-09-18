import Mathlib.NumberTheory.WellApproximable

namespace Commons.NumberTheory.DuffinSchaeffer

open Set Filter Function Metric MeasureTheory

private lemma gcd_eq_natGcd (m n : ℕ) : gcd m n = m.gcd n := by
  unfold instGCDMonoidNat
  rfl

theorem approxAddOrderOf_eq_biUnion_ball (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    approxAddOrderOf UnitAddCircle q δ =
      ⋃ m ∈ (Finset.range q).filter (fun m : ℕ => m.gcd q = 1),
        Metric.ball (↑((m : ℝ) / (q : ℝ)) : UnitAddCircle) δ := by
  ext x
  rw [UnitAddCircle.mem_approxAddOrderOf_iff hq]
  simp [Finset.mem_filter, and_assoc, dist_eq_norm, gcd_eq_natGcd]

end Commons.NumberTheory.DuffinSchaeffer