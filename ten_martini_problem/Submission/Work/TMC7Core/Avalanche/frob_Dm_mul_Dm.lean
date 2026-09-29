import Mathlib
import Submission.Work.TMC7Core.Avalanche.dframe
import Submission.Work.TMC7Core.Cocycle

/-!
# The Frobenius norm of `Dm s' · W · Dm s` for a unitary `W`

For a unitary `2×2` matrix `W` (`Wᴴ W = 1`, `W Wᴴ = 1`) and real `s, s'`, the product of the
two diagonal scalings with `W` has squared Frobenius norm

  `‖Dm s' · W · Dm s‖² = s'² s² |W₀₀|² + (1 - |W₀₀|²)(s'² (s²)⁻¹ + (s'²)⁻¹ s²) + |W₀₀|² (s²)⁻¹ (s'²)⁻¹`,

i.e. it is governed by the single number `|W₀₀|²`.  This is the elementary "geometric" input of
the avalanche principle: `Dm s' · W · Dm s` has entries `s' s W₀₀`, `s' s⁻¹ W₀₁`,
`(s')⁻¹ s W₁₀`, `(s')⁻¹ s⁻¹ W₁₁`, and unitarity of `W` supplies
`|W₀₁|² = |W₁₀|² = 1 - |W₀₀|²` and `|W₁₁|² = |W₀₀|²`.
-/

open Matrix

namespace Work.TMC7Core.Avalanche

/-- `‖(r : ℂ) * z‖² = r² ‖z‖²` for real `r`. -/
theorem norm_sq_ofReal_mul (r : ℝ) (z : ℂ) : ‖((r : ℝ) : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  ring

/-- The columns of a unitary matrix are unit vectors: `‖W₀ⱼ‖² + ‖W₁ⱼ‖² = 1`. -/
theorem unitary_col_norm_sq (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W.conjTranspose * W = 1)
    (j : Fin 2) : ‖W 0 j‖ ^ 2 + ‖W 1 j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun hW j) j
  rw [Matrix.mul_apply] at h
  simp only [Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Complex.star_def, RCLike.conj_mul] at h
  have h2 : ((‖W 0 j‖ ^ 2 + ‖W 1 j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    simpa using h
  exact Complex.ofReal_inj.mp h2

/-- The rows of a unitary matrix are unit vectors: `‖Wᵢ₀‖² + ‖Wᵢ₁‖² = 1`. -/
theorem unitary_row_norm_sq (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W * W.conjTranspose = 1)
    (i : Fin 2) : ‖W i 0‖ ^ 2 + ‖W i 1‖ ^ 2 = 1 := by
  have h := congrFun (congrFun hW i) i
  rw [Matrix.mul_apply] at h
  simp only [Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Complex.star_def, RCLike.mul_conj] at h
  have h2 : ((‖W i 0‖ ^ 2 + ‖W i 1‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    simpa using h
  exact Complex.ofReal_inj.mp h2

/-- **The squared Frobenius norm of `Dm s' · W · Dm s` for unitary `W`.** -/
theorem frob_Dm_mul_Dm (s s' : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W.conjTranspose * W = 1) (hW' : W * W.conjTranspose = 1) :
    frob (Dm s' * W * Dm s) ^ 2
      = s' ^ 2 * s ^ 2 * ‖W 0 0‖ ^ 2
        + (1 - ‖W 0 0‖ ^ 2) * (s' ^ 2 * (s ^ 2)⁻¹ + (s' ^ 2)⁻¹ * s ^ 2)
        + ‖W 0 0‖ ^ 2 * ((s ^ 2)⁻¹ * (s' ^ 2)⁻¹) := by
  -- unitarity of `W` in terms of the four entries
  have hcol0 := unitary_col_norm_sq W hW 0
  have hcol1 := unitary_col_norm_sq W hW 1
  have hrow0 := unitary_row_norm_sq W hW' 0
  have hn01 : ‖W 0 1‖ ^ 2 = 1 - ‖W 0 0‖ ^ 2 := by linarith
  have hn10 : ‖W 1 0‖ ^ 2 = 1 - ‖W 0 0‖ ^ 2 := by linarith
  have hn11 : ‖W 1 1‖ ^ 2 = ‖W 0 0‖ ^ 2 := by linarith
  -- the entries of `Dm s' · W · Dm s`
  have e00 : (Dm s' * W * Dm s) 0 0 = (((s * s' : ℝ)) : ℂ) * W 0 0 := by
    simp [Dm, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e01 : (Dm s' * W * Dm s) 0 1 = (((s' * s⁻¹ : ℝ)) : ℂ) * W 0 1 := by
    simp [Dm, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e10 : (Dm s' * W * Dm s) 1 0 = ((((s')⁻¹ * s : ℝ)) : ℂ) * W 1 0 := by
    simp [Dm, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e11 : (Dm s' * W * Dm s) 1 1 = ((((s')⁻¹ * s⁻¹ : ℝ)) : ℂ) * W 1 1 := by
    simp [Dm, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [frob_sq, e00, e01, e10, e11]
  simp only [norm_sq_ofReal_mul]
  rw [hn01, hn10, hn11]
  rw [show (s * s') ^ 2 = s ^ 2 * s' ^ 2 by ring,
      show (s' * s⁻¹) ^ 2 = s' ^ 2 * (s ^ 2)⁻¹ by rw [mul_pow, inv_pow],
      show ((s')⁻¹ * s) ^ 2 = (s' ^ 2)⁻¹ * s ^ 2 by rw [mul_pow, inv_pow],
      show ((s')⁻¹ * s⁻¹) ^ 2 = (s ^ 2)⁻¹ * (s' ^ 2)⁻¹ by
        rw [mul_pow]
        simp only [inv_pow]
        exact mul_comm _ _]
  ring

end Work.TMC7Core.Avalanche
