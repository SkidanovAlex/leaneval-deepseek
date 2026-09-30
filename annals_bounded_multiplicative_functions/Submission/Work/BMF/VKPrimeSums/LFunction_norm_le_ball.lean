import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKPrimeSums

/-- Any point `w` with `Re w ≥ 1/2` and `‖w‖ ≤ |t| + 4` (with `4 ≤ |t|`) is dominated by the
polynomial bound `2 N ‖w‖ / Re w ≤ 4 N (|t| + 4)` from the right half-plane estimate. -/
lemma LFunction_norm_le_ball {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {t : ℝ} (ht : 4 ≤ |t|) {w : ℂ} (hre : 1 / 2 ≤ w.re) (hnorm : ‖w‖ ≤ |t| + 4) :
    ‖DirichletCharacter.LFunction χ w‖ ≤ 4 * (N : ℝ) * (|t| + 4) := by
  have hwre : 0 < w.re := lt_of_lt_of_le (by norm_num) hre
  have hmain : ‖DirichletCharacter.LFunction χ w‖ ≤ 2 * (N : ℝ) * ‖w‖ / w.re :=
    Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane χ hχ hwre
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hstep : 2 * (N : ℝ) * ‖w‖ / w.re ≤ 4 * (N : ℝ) * ‖w‖ := by
    rw [div_le_iff₀ hwre]
    have h1 : (2 : ℝ) ≤ 4 * w.re := by linarith
    nlinarith [h1, hN, norm_nonneg w, mul_nonneg hN (norm_nonneg w)]
  have hwbound : (N : ℝ) * ‖w‖ ≤ (N : ℝ) * (|t| + 4) :=
    mul_le_mul_of_nonneg_left hnorm hN
  calc ‖DirichletCharacter.LFunction χ w‖ ≤ 2 * (N : ℝ) * ‖w‖ / w.re := hmain
    _ ≤ 4 * (N : ℝ) * ‖w‖ := hstep
    _ = 4 * ((N : ℝ) * ‖w‖) := by ring
    _ ≤ 4 * ((N : ℝ) * (|t| + 4)) := by linarith
    _ = 4 * (N : ℝ) * (|t| + 4) := by ring

end Work.BMF.VKPrimeSums
