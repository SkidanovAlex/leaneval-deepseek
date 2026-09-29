import Mathlib
import Submission.Work.TMC7Core.Avalanche.dframe

/-!
# `TMC7Core.Avalanche.chain_gram`

The Gram matrix `G k = N k · (N k)ᴴ` of the truncated ordered product `N k` of the abstract
chain `(D j, W j)` (see `dframe`) is Hermitian, its trace is the square of the Frobenius norm
of `N k`, and its determinant is `1` whenever the scalars `s j` are nonzero and the `W j` are
unitary.

The determinant statement is where the unitarity of the `W j` is used: a unitary `2×2` matrix
has `|det| = 1`, so `det (N k) = ∏_{j<k} det (W j)` has modulus `1`, and
`det (N k · (N k)ᴴ) = det (N k) · conj (det (N k)) = |det (N k)|² = 1`.

The Frobenius norm `frob` is the `2×2` one hard coded in `Work.TMC7Core.Defs`:
`frob A = √(‖A 0 0‖² + ‖A 0 1‖² + ‖A 1 0‖² + ‖A 1 1‖²)`.
-/

open Matrix

noncomputable section

namespace Work.TMC7Core.Avalanche

/-! ## The scalar factors `Dm s = diag (s, s⁻¹)` -/

/-- `det (Dm s) = 1` for `s ≠ 0`. -/
lemma det_Dm (s : ℝ) (hs : s ≠ 0) : (Dm s).det = 1 := by
  rw [Dm, Matrix.det_diagonal]
  simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.ofReal_inv]
  exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs)

/-- `‖det (Dm s)‖ = 1` for `s ≠ 0`. -/
lemma norm_det_Dm (s : ℝ) (hs : s ≠ 0) : ‖(Dm s).det‖ = 1 := by
  rw [det_Dm s hs, norm_one]

/-! ## Unitary matrices have determinant of modulus one -/

/-- A unitary `2×2` complex matrix (`W · Wᴴ = 1`) has `‖det W‖ = 1`. -/
lemma norm_det_unitary (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W * Wᴴ = 1) :
    ‖W.det‖ = 1 := by
  have h1 : W.det * star W.det = 1 := by
    have h := congrArg Matrix.det hW
    rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  have h2 : ((‖W.det‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h1, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : ‖W.det‖ ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg W.det]

/-! ## The determinant of the chain product -/

/-- If the scalars `s j` (`j ≤ k`) are nonzero and the `W j` (`j < k`) are unitary, then
`‖det (Nmat s W k)‖ = 1`. -/
lemma norm_det_Nmat (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ k, (∀ j, j ≤ k → s j ≠ 0) → (∀ j, j < k → W j * (W j)ᴴ = 1) →
      ‖(Nmat s W k).det‖ = 1 := by
  intro k
  induction k with
  | zero =>
      intro hs hW
      show ‖(Dm (s 0)).det‖ = 1
      exact norm_det_Dm _ (hs 0 (le_refl 0))
  | succ k ih =>
      intro hs hW
      rw [Nmat_succ, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul]
      rw [norm_det_Dm _ (hs (k + 1) (le_refl _)),
        norm_det_unitary _ (hW k (Nat.lt_succ_self k)),
        ih (fun j hj => hs j (le_trans hj (Nat.le_succ k)))
          (fun j hj => hW j (lt_trans hj (Nat.lt_succ_self k)))]
      ring

/-! ## Gram matrices of a `2×2` matrix -/

/-- For the hard coded `frob`, `frob N ^ 2 = trace (N · Nᴴ)`. -/
lemma frob_sq_trace_gram (N : Matrix (Fin 2) (Fin 2) ℂ) :
    ((frob N ^ 2 : ℝ) : ℂ) = (N * Nᴴ).trace := by
  have h : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hf : frob N ^ 2 = ‖N 0 0‖ ^ 2 + ‖N 0 1‖ ^ 2 + ‖N 1 0‖ ^ 2 + ‖N 1 1‖ ^ 2 := by
    rw [frob, Real.sq_sqrt (by positivity)]
  rw [hf]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.isValue]
  rw [h, h, h, h]
  push_cast
  ring

/-- The Gram matrix `N · Nᴴ` is Hermitian. -/
lemma conjT_gram (N : Matrix (Fin 2) (Fin 2) ℂ) : (N * Nᴴ)ᴴ = N * Nᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-! ## The main statement -/

theorem chain_gram (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hσ : ∀ j, j ≤ k → 0 < s j)
    (hW : ∀ j, j < k → (W j).conjTranspose * W j = 1 ∧ W j * (W j).conjTranspose = 1) :
    (Gmat s W k).conjTranspose = Gmat s W k ∧
      frob (Nmat s W k) ^ 2 = (Gmat s W k).trace ∧
      (Gmat s W k).det = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · show (Nmat s W k * (Nmat s W k)ᴴ)ᴴ = Nmat s W k * (Nmat s W k)ᴴ
    exact conjT_gram _
  · show ((frob (Nmat s W k) : ℂ)) ^ 2 = (Nmat s W k * (Nmat s W k)ᴴ).trace
    rw [← Complex.ofReal_pow]
    exact frob_sq_trace_gram _
  · show (Nmat s W k * (Nmat s W k)ᴴ).det = 1
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    have key : ((‖(Nmat s W k).det‖ ^ 2 : ℝ) : ℂ)
        = (Nmat s W k).det * star (Nmat s W k).det := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← key,
      norm_det_Nmat s W k (fun j hj => ne_of_gt (hσ j hj)) (fun j hj => (hW j hj).2)]
    norm_num

end Work.TMC7Core.Avalanche
