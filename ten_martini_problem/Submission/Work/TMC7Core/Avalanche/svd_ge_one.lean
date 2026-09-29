import Mathlib
import Submission.Work.Avalanche.svd

namespace Work.TMC7Core.Avalanche

open Matrix

/-- The `2×2` swap matrix `!![0,1;1,0]`. -/
private def sw : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The swap matrix is self-adjoint. -/
private lemma sw_conjTranspose : sw.conjTranspose = sw := by
  unfold sw
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-- The swap matrix is an involution. -/
private lemma sw_mul_self : sw * sw = 1 := by
  unfold sw
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugating a diagonal matrix by the swap matrix exchanges its two diagonal entries. -/
private lemma sw_diagonal (x y : ℂ) :
    sw * Matrix.diagonal ![x, y] * sw = Matrix.diagonal ![y, x] := by
  unfold sw
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul_diagonal]

/-- **Sorted singular value decomposition for `SL₂(ℂ)`.**  A `2×2` complex matrix of
determinant one admits a singular value decomposition `X = U · diag(a, a⁻¹) · Vᴴ` in which the
first diagonal entry `a` is the *larger* singular value, hence `a ≥ 1`. -/
lemma svd_ge_one (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.det = 1) :
    ∃ (U V : Matrix (Fin 2) (Fin 2) ℂ) (a : ℝ),
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      V.conjTranspose * V = 1 ∧ V * V.conjTranspose = 1 ∧
      1 ≤ a ∧ X = U * Matrix.diagonal ![((a : ℝ) : ℂ), ((a⁻¹ : ℝ) : ℂ)] * V.conjTranspose := by
  obtain ⟨U, V, a, b, hU1, hU2, hV1, hV2, ha, hb, hab, hXd⟩ := Work.Avalanche.svd X hX
  rcases le_total a b with hle | hle
  · -- `a ≤ b`: exchange the two diagonal entries by conjugating with the swap matrix
    have hb1 : 1 ≤ b := by
      have h2 : a * b ≤ b * b := mul_le_mul_of_nonneg_right hle (le_of_lt hb)
      nlinarith [h2, hab, hb]
    have hbinv : b⁻¹ = a := inv_eq_of_mul_eq_one_left hab
    have hd : Matrix.diagonal ![((b : ℝ) : ℂ), ((b⁻¹ : ℝ) : ℂ)] =
        Matrix.diagonal ![((b : ℝ) : ℂ), ((a : ℝ) : ℂ)] := by
      congr 1
      funext i
      fin_cases i <;> simp [hbinv]
    have hsd : sw * Matrix.diagonal ![((b : ℝ) : ℂ), ((a : ℝ) : ℂ)] * sw =
        Matrix.diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] := sw_diagonal _ _
    refine ⟨U * sw, V * sw, b, ?_, ?_, ?_, ?_, hb1, ?_⟩
    · rw [Matrix.conjTranspose_mul, sw_conjTranspose]
      calc sw * Uᴴ * (U * sw) = sw * (Uᴴ * U) * sw := by noncomm_ring
        _ = 1 := by rw [hU1]; simp [sw_mul_self]
    · rw [Matrix.conjTranspose_mul, sw_conjTranspose]
      calc U * sw * (sw * Uᴴ) = U * (sw * sw) * Uᴴ := by noncomm_ring
        _ = 1 := by rw [sw_mul_self]; simp [hU2]
    · rw [Matrix.conjTranspose_mul, sw_conjTranspose]
      calc sw * Vᴴ * (V * sw) = sw * (Vᴴ * V) * sw := by noncomm_ring
        _ = 1 := by rw [hV1]; simp [sw_mul_self]
    · rw [Matrix.conjTranspose_mul, sw_conjTranspose]
      calc V * sw * (sw * Vᴴ) = V * (sw * sw) * Vᴴ := by noncomm_ring
        _ = 1 := by rw [sw_mul_self]; simp [hV2]
    · have hXeq : X = U * sw * Matrix.diagonal ![((b : ℝ) : ℂ), ((a : ℝ) : ℂ)] * (V * sw)ᴴ := by
        calc X = U * Matrix.diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] * Vᴴ := hXd
          _ = U * (sw * Matrix.diagonal ![((b : ℝ) : ℂ), ((a : ℝ) : ℂ)] * sw) * Vᴴ := by
                rw [hsd]
          _ = U * sw * Matrix.diagonal ![((b : ℝ) : ℂ), ((a : ℝ) : ℂ)] * (V * sw)ᴴ := by
                rw [Matrix.conjTranspose_mul, sw_conjTranspose]
                noncomm_ring
      rw [hd]
      exact hXeq
  · -- `b ≤ a`: the first singular value is already the larger one
    have ha1 : 1 ≤ a := by
      have h2 : b * a ≤ a * a := mul_le_mul_of_nonneg_right hle (le_of_lt ha)
      nlinarith [h2, hab, ha]
    have hainv : a⁻¹ = b := inv_eq_of_mul_eq_one_right hab
    have hd : Matrix.diagonal ![((a : ℝ) : ℂ), ((a⁻¹ : ℝ) : ℂ)] =
        Matrix.diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] := by
      congr 1
      funext i
      fin_cases i <;> simp [hainv]
    exact ⟨U, V, a, hU1, hU2, hV1, hV2, ha1, by rw [hd]; exact hXd⟩

end Work.TMC7Core.Avalanche
