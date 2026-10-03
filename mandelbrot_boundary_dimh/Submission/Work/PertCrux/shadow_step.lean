import Mathlib

namespace Work.PertCrux

/-- One step of the geometric propagation of an orbit error.  If `K ≥ 1`, `δ ≥ 0`,
`e ≤ K^j (η + j δ)` and `e' ≤ δ + K e`, then `e' ≤ K^(j+1) (η + (j+1) δ)`. -/
theorem shadow_step {K η δ e e' : ℝ} {j : ℕ} (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (he : e ≤ K ^ j * (η + (j : ℝ) * δ)) (hrec : e' ≤ δ + K * e) :
    e' ≤ K ^ (j + 1) * (η + ((j + 1 : ℕ) : ℝ) * δ) := by
  have hK1 : K ^ (j + 1) ≥ 1 := one_le_pow₀ hK
  -- propagate the error through one iteration
  have hKe : K * e ≤ K ^ (j + 1) * (η + (j : ℝ) * δ) := by
    calc K * e ≤ K * (K ^ j * (η + (j : ℝ) * δ)) := by
            exact mul_le_mul_of_nonneg_left he (by linarith)
      _ = K ^ (j + 1) * (η + (j : ℝ) * δ) := by rw [pow_succ]; ring
  -- the fresh increment δ is dominated by its geometric amplification
  have hδle : δ ≤ K ^ (j + 1) * δ := by
    calc δ = 1 * δ := by ring
      _ ≤ K ^ (j + 1) * δ := by exact mul_le_mul_of_nonneg_right hK1 hδ
  calc e' ≤ δ + K * e := hrec
    _ ≤ K ^ (j + 1) * δ + K ^ (j + 1) * (η + (j : ℝ) * δ) := by linarith
    _ = K ^ (j + 1) * (η + ((j + 1 : ℕ) : ℝ) * δ) := by push_cast; ring

end Work.PertCrux
