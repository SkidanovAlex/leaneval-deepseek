import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Complex

open scoped BigOperators

theorem abs_sum_unit_le_sqrt (N : ℕ) (a z : Fin N → ℂ) (hz : ∀ i : Fin N, ‖z i‖ = 1) :
    ‖∑ i : Fin N, a i * z i‖ ≤
      Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * Real.sqrt (N : ℝ) := by
  -- Triangle inequality: ‖∑ aᵢ zᵢ‖ ≤ ∑ ‖aᵢ‖, since ‖zᵢ‖ = 1.
  have htri : ‖∑ i : Fin N, a i * z i‖ ≤ ∑ i : Fin N, ‖a i‖ := by
    calc
      ‖∑ i : Fin N, a i * z i‖ = ‖∑ i ∈ (Finset.univ : Finset (Fin N)), a i * z i‖ := by simp
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin N)), ‖a i * z i‖ := by
        exact norm_sum_le (Finset.univ : Finset (Fin N)) (fun i : Fin N => a i * z i)
      _ = ∑ i ∈ (Finset.univ : Finset (Fin N)), ‖a i‖ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [norm_mul, hz i, mul_one]
      _ = ∑ i : Fin N, ‖a i‖ := by simp
  -- Cauchy-Schwarz: (∑ ‖aᵢ‖)² ≤ (∑ ‖aᵢ‖²) * N.
  have hcs : (∑ i : Fin N, ‖a i‖) ^ 2 ≤ (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) := by
    calc
      (∑ i : Fin N, ‖a i‖) ^ 2 = (∑ i ∈ (Finset.univ : Finset (Fin N)), ‖a i‖ * (1 : ℝ)) ^ 2 := by simp
      _ ≤ (∑ i ∈ (Finset.univ : Finset (Fin N)), ‖a i‖ ^ 2) *
          (∑ i ∈ (Finset.univ : Finset (Fin N)), (1 : ℝ) ^ 2) := by
        exact Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin N)))
          (f := fun i : Fin N => ‖a i‖) (g := fun _ : Fin N => (1 : ℝ))
      _ = (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) := by simp
  let A : ℝ := ∑ i : Fin N, ‖a i‖ ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖a i‖)
  have hsum_nonneg : 0 ≤ ∑ i : Fin N, ‖a i‖ := by
    exact Finset.sum_nonneg (fun i _ => norm_nonneg (a i))
  have hle : ∑ i : Fin N, ‖a i‖ ≤ Real.sqrt (A * (N : ℝ)) := by
    rw [Real.le_sqrt hsum_nonneg (mul_nonneg hA (by positivity))]
    simpa [A] using hcs
  calc
    ‖∑ i : Fin N, a i * z i‖ ≤ ∑ i : Fin N, ‖a i‖ := htri
    _ ≤ Real.sqrt (A * (N : ℝ)) := hle
    _ = Real.sqrt A * Real.sqrt (N : ℝ) := by rw [Real.sqrt_mul hA]
    _ = Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * Real.sqrt (N : ℝ) := by simp [A]

end Commons.Analysis.Complex