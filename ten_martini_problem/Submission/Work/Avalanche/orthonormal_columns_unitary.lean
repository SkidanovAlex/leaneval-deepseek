import Mathlib

/-!
# Polar/QR decomposition: a matrix with `Yᴴ * Y = diagonal d` is `U * diagonal √d` with `U` unitary

If `Y : Matrix n n ℂ` is square and `Y.conjTranspose * Y = diagonal d` for a strictly positive
real function `d`, then `Y = U * diagonal (fun i => √(d i))` for a unitary matrix `U`.  The
unitary factor is `U = Y * diagonal (fun i => 1 / √(d i))`.
-/

namespace Work.Avalanche

/-- The complex conjugate of a real number cast into `ℂ` is itself. -/
private lemma star_ofReal (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by simp

lemma orthonormal_columns_unitary
    {n : Type*} [Fintype n] [DecidableEq n]
    (Y : Matrix n n ℂ) (d : n → ℝ) (hd : ∀ i, 0 < d i)
    (h : Y.conjTranspose * Y = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) :
    ∃ U : Matrix n n ℂ, U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      Y = U * Matrix.diagonal (fun i => ((Real.sqrt (d i) : ℝ) : ℂ)) := by
  -- Entrywise identity: `star (1/√d) * d * (1/√d) = 1`.
  have key : ∀ i, star (((1 / Real.sqrt (d i) : ℝ) : ℂ)) * (((d i : ℝ) : ℂ)) *
      (((1 / Real.sqrt (d i) : ℝ) : ℂ)) = 1 := fun i => by
    have hne : d i ≠ 0 := ne_of_gt (hd i)
    have hreal : ((1 / Real.sqrt (d i))^2 * d i : ℝ) = 1 := by
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt (hd i)), one_div, inv_mul_cancel₀ hne]
    calc star (((1 / Real.sqrt (d i) : ℝ) : ℂ)) * (((d i : ℝ) : ℂ)) *
            (((1 / Real.sqrt (d i) : ℝ) : ℂ))
        = (((1 / Real.sqrt (d i))^2 * d i : ℝ) : ℂ) := by
          rw [star_ofReal]; push_cast; ring
      _ = 1 := by rw [hreal]; norm_num
  -- The unitary factor.
  have h1 : (Y * Matrix.diagonal (fun i => ((1 / Real.sqrt (d i) : ℝ) : ℂ))).conjTranspose *
      (Y * Matrix.diagonal (fun i => ((1 / Real.sqrt (d i) : ℝ) : ℂ))) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
    rw [show (Matrix.diagonal (star fun i => ((1 / Real.sqrt (d i) : ℝ) : ℂ)) * Y.conjTranspose) *
          (Y * Matrix.diagonal (fun i => ((1 / Real.sqrt (d i) : ℝ) : ℂ)))
        = Matrix.diagonal (star fun i => ((1 / Real.sqrt (d i) : ℝ) : ℂ)) * (Y.conjTranspose * Y) *
          Matrix.diagonal (fun i => ((1 / Real.sqrt (d i) : ℝ) : ℂ)) from by noncomm_ring]
    rw [h, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    exact key i
  refine ⟨Y * Matrix.diagonal (fun i => ((1 / Real.sqrt (d i) : ℝ) : ℂ)), h1, ?_, ?_⟩
  · -- a square matrix with `Uᴴ * U = 1` also satisfies `U * Uᴴ = 1`
    exact mul_eq_one_comm.mp h1
  · -- `Y * diagonal (1/√d) * diagonal √d = Y`
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => ((1 / Real.sqrt (d i) : ℝ) : ℂ) * ((Real.sqrt (d i) : ℝ) : ℂ)) =
          (fun _ => (1 : ℂ)) from by
      funext i
      have hsne : Real.sqrt (d i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hd i))
      have hreal : ((1 / Real.sqrt (d i)) * Real.sqrt (d i) : ℝ) = 1 := by
        rw [one_div, inv_mul_cancel₀ hsne]
      calc ((1 / Real.sqrt (d i) : ℝ) : ℂ) * ((Real.sqrt (d i) : ℝ) : ℂ)
          = (((1 / Real.sqrt (d i)) * Real.sqrt (d i) : ℝ) : ℂ) := by push_cast; ring
        _ = 1 := by rw [hreal]; norm_num]
    rw [Matrix.diagonal_one, Matrix.mul_one]

end Work.Avalanche
