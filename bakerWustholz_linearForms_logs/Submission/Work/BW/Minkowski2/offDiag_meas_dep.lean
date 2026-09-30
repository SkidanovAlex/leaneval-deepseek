import Mathlib
import Submission.Work.BW.Minkowski2.centroidDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open scoped BigOperators

theorem offDiag_meas_dep {d : ℕ} (lam : Fin (d+1) → ℝ)
    (c : Fin d → (Fin d → ℝ) → (Fin d → ℝ))
    (hcmeas : ∀ i, Measurable (c i))
    (hcdep : ∀ (i : Fin d) (x y : Fin d → ℝ), (∀ m, i ≤ m → x m = y m) → c i x = c i y)
    (m : Fin d) :
    Measurable (offDiag lam c m) ∧
    (∀ x y : Fin d → ℝ, (∀ j : Fin d, m < j → x j = y j) →
      offDiag lam c m x = offDiag lam c m y) := by
  constructor
  · -- Measurability: a finite sum of measurable terms.
    unfold offDiag
    apply Finset.measurable_sum
    intro i _
    exact Measurable.const_mul ((measurable_pi_apply m).comp (hcmeas i)) _
  · -- Dependence only on coordinates `j > m`.
    intro x y hxy
    unfold offDiag
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter] at hi
    rw [hcdep i x y]
    intro k hk
    exact hxy k (lt_of_lt_of_le (not_le.mp hi.2) hk)

end Work.BW.Minkowski2
