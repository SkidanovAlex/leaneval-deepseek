import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Metrizable.Uniformity

namespace Commons.Analysis.InfiniteSum

/-- The sum over `ℤ` of a summable odd real sequence is zero. -/
theorem tsum_int_eq_zero_of_odd {q : ℤ → ℝ} (h : ∀ n, q (-n) = -q n) (hs : Summable q) :
    ∑' n : ℤ, q n = 0 := by
  have h1 : ∑' n : ℤ, q (-n) = ∑' n : ℤ, q n := (Equiv.neg ℤ).tsum_eq q
  have h2 : ∑' n : ℤ, q (-n) = -∑' n : ℤ, q n := by
    rw [funext h, tsum_neg]
  have hfix : ∑' n : ℤ, q n = -∑' n : ℤ, q n := h1.symm.trans h2
  have _ := hs
  linarith

end Commons.Analysis.InfiniteSum