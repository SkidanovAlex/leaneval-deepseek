import Mathlib
import Submission.Work.TMC7Core.Avalanche.dframe

/-!
# Invariance of the Frobenius norm under a left isometry

If `W` is a `2×2` complex matrix with orthonormal columns, i.e. `Wᴴ * W = 1`, then left
multiplication by `W` preserves the Frobenius norm `frob`.

The proof identifies `frob A ^ 2` with the real part of `tr (Aᴴ * A)`; the isometry
condition makes `(W * M)ᴴ * (W * M) = Mᴴ * M`.
-/

open Matrix

namespace Work.TMC7Core.Avalanche

/-- `star z * z = (normSq z : ℂ)`. -/
lemma star_mul_self_eq_ofReal_normSq (z : ℂ) : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj]

/-- The real part of `star z * z` is the square of the norm of `z`. -/
lemma re_star_mul_self (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [star_mul_self_eq_ofReal_normSq, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The Frobenius norm `frob` squared equals `re (tr (Aᴴ * A))`. -/
lemma frob_sq_eq_re_trace (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Work.TMC7Core.frob A ^ 2 = ((Aᴴ * A).trace).re := by
  rw [Work.TMC7Core.frob, Real.sq_sqrt (by positivity)]
  rw [Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.add_re]
  rw [re_star_mul_self, re_star_mul_self, re_star_mul_self, re_star_mul_self]
  ring

/-- A left isometry preserves the Gram matrix `Aᴴ * A`. -/
lemma conjTranspose_mul_self_of_isometry (W M : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose * W = 1) : (W * M)ᴴ * (W * M) = Mᴴ * M := by
  rw [Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ W M, hW, Matrix.one_mul]

theorem frob_unitary (W M : Matrix (Fin 2) (Fin 2) ℂ) (hW : W.conjTranspose * W = 1) :
    frob (W * M) = frob M := by
  have hgram : (W * M)ᴴ * (W * M) = Mᴴ * M := conjTranspose_mul_self_of_isometry W M hW
  have hsq : frob (W * M) ^ 2 = frob M ^ 2 := by
    rw [frob_sq_eq_re_trace, frob_sq_eq_re_trace, hgram]
  have h1 : 0 ≤ frob (W * M) := Real.sqrt_nonneg _
  have h2 : 0 ≤ frob M := Real.sqrt_nonneg _
  rw [← Real.sqrt_sq h1, hsq, Real.sqrt_sq h2]

end Work.TMC7Core.Avalanche
