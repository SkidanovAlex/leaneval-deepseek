import Mathlib

namespace Work.WilE2

theorem norm_sub_le_grid {n : ℕ} {M : ℝ} (hM : 0 ≤ M) {N : ℕ} (hN : 0 < N)
    (v : Fin n → Fin N) (x y : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (-M + 2 * M * (v i : ℝ) / N) (-M + 2 * M * ((v i : ℝ) + 1) / N))
    (hy : ∀ i, y i ∈ Set.Icc (-M + 2 * M * (v i : ℝ) / N) (-M + 2 * M * ((v i : ℝ) + 1) / N)) :
    ‖y - x‖ ≤ 2 * M / N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hCnonneg : 0 ≤ 2 * M / (N : ℝ) := by positivity
  refine (pi_norm_le_iff_of_nonneg hCnonneg).mpr (fun i => ?_)
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  constructor
  · have h1 := (hx i).1
    have h2 := (hy i).2
    have : 2 * M * ((v i : ℝ) + 1) / N - 2 * M * (v i : ℝ) / N = 2 * M / N := by
      field_simp; ring
    linarith [h1, h2]
  · have h1 := (hy i).1
    have h2 := (hx i).2
    have : 2 * M * ((v i : ℝ) + 1) / N - 2 * M * (v i : ℝ) / N = 2 * M / N := by
      field_simp; ring
    linarith [h1, h2]

end Work.WilE2
