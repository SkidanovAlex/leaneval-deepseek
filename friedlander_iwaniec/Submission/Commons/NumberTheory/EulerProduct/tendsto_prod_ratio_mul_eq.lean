import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Metrizable.Uniformity

namespace Commons.NumberTheory.EulerProduct

theorem tendsto_prod_ratio_mul_eq {g gtil : ℕ → ℝ} {H Htil G : ℝ}
    (hHtil : Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - gtil p) / (1 - 1 / (p : ℝ))) Filter.atTop (nhds Htil))
    (hG : Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - g (p ^ 2))) Filter.atTop (nhds G))
    (hH : Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - g p) / (1 - 1 / (p : ℝ))) Filter.atTop (nhds H))
    (hpt : ∀ p : ℕ, p.Prime → (1 - gtil p) / (1 - 1 / (p : ℝ)) * (1 - g (p ^ 2)) = (1 - g p) / (1 - 1 / (p : ℝ))) :
    Htil * G = H := by
  have hprod : ∀ N : ℕ,
      (∏ p ∈ Nat.primesBelow N, (1 - gtil p) / (1 - 1 / (p : ℝ))) * (∏ p ∈ Nat.primesBelow N, (1 - g (p ^ 2)))
        = ∏ p ∈ Nat.primesBelow N, (1 - g p) / (1 - 1 / (p : ℝ)) := by
    intro N
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact hpt p (Nat.mem_primesBelow.mp hp).2
  have heq : (fun N : ℕ => (∏ p ∈ Nat.primesBelow N, (1 - gtil p) / (1 - 1 / (p : ℝ))) * (∏ p ∈ Nat.primesBelow N, (1 - g (p ^ 2))))
      = (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - g p) / (1 - 1 / (p : ℝ))) := funext hprod
  have hlim := hHtil.mul hG
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim hH

end Commons.NumberTheory.EulerProduct