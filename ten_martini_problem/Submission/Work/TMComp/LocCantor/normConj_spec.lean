import Mathlib
import Submission.Work.TMComp.LocCantor.Defs

/-!
# C17 (`P_LocCantor`) — the normalised conjugacy has determinant one and conjugates
the cocycle to the rotation `R_{-σθ}`

For a matrix-valued function `A` with constant determinant `d ≠ 0` satisfying

  `A(x+α) = S(x) · A(x) · R_θ`   (`S = S_{λ,E}` the transfer matrix, `R_θ = rot θ`),

the scaled adjugate `B(x) = normConj A σ x = (√|det A(x)|)⁻¹ • (A(x)·diag(1,σ)).adjugate`
has determinant `1` and satisfies

  `B(x+α) · S(x) = R_{-σθ} · B(x)`,

provided `σ = ±1` and `σ d = |d|` (i.e. `σ` is the sign of `d`).

The proof is elementary `2 × 2` matrix algebra:
* `det (A(x)·diag(1,σ)) = d σ = |d|` and `det (adj M) = det M` for `2 × 2` matrices, so
  `det B(x) = (√|d|)⁻² |d| = 1`;
* `det S(x) = 1` follows from `det A(x+α) = det S(x) · d · 1 = d` and `d ≠ 0`;
* `adj` is antimultiplicative, `adj S · S = det S • 1 = 1`, and
  `adj(diag(1,σ)) · adj(R_θ) = R_{-σθ} · adj(diag(1,σ))` — the only place where `σ = ±1`
  and the sign convention enter.
-/

noncomputable section

namespace Work.TMComp.LocCantor

open Work.TMContract

/-- `adj` is antimultiplicative: the adjugate of a product of four `2 × 2` matrices. -/
theorem adjugate_mul_four (M N P Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (M * N * P * Q).adjugate = Q.adjugate * P.adjugate * N.adjugate * M.adjugate := by
  simp only [Matrix.adjugate_mul_distrib]
  noncomm_ring

/-- The adjugate of the rotation matrix `R_θ` is `R_{-θ}`. -/
theorem adjugate_rot (θ : ℝ) :
    (Work.TMContract.rot θ).adjugate = Work.TMContract.rot (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Work.TMContract.rot, Real.cos_neg, Real.sin_neg]

/-- The adjugate of `diag(1,σ)` is `diag(σ,1)`. -/
theorem adjugate_sgnMat (σ : ℝ) :
    (Work.TMComp.sgnMat σ).adjugate = !![σ, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Work.TMComp.sgnMat]

/-- The key rotational identity: `adj(diag(1,σ)) · adj(R_θ) = R_{-σθ} · adj(diag(1,σ))`
for `σ = ±1`.  (Both sides equal `!![cos 2πθ, sin 2πθ; -σ sin 2πθ, σ cos 2πθ]`.) -/
theorem adjugate_sgnMat_mul_adjugate_rot {σ θ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    (Work.TMComp.sgnMat σ).adjugate * (Work.TMContract.rot θ).adjugate
      = Work.TMContract.rot (-(σ * θ)) * (Work.TMComp.sgnMat σ).adjugate := by
  rcases hσ with h | h
  · subst h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
        Work.TMComp.sgnMat, Work.TMContract.rot]
  · subst h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
        Work.TMComp.sgnMat, Work.TMContract.rot]

/-- `det diag(1,σ) = σ`. -/
theorem det_sgnMat (σ : ℝ) : (Work.TMComp.sgnMat σ).det = σ := by
  simp [Matrix.det_fin_two, Work.TMComp.sgnMat]

/-- `det R_θ = 1`. -/
theorem det_rot (θ : ℝ) : (Work.TMContract.rot θ).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [Work.TMContract.rot]
  nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * θ)]

/-- Core algebraic step: if `A' = S · A · R_θ` with `det S = 1`, `σ = ±1`, then conjugating
`S` by the `σ`-scaled adjugate is the rotation `R_{-σθ}`. -/
theorem adjugate_mul_sgnMat_mul (A A' S : Matrix (Fin 2) (Fin 2) ℝ) {σ θ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hSA : A' = S * A * Work.TMContract.rot θ) (hSdet : S.det = 1) :
    (A' * Work.TMComp.sgnMat σ).adjugate * S
      = Work.TMContract.rot (-(σ * θ)) * (A * Work.TMComp.sgnMat σ).adjugate := by
  subst hSA
  rw [adjugate_mul_four, Matrix.adjugate_mul_distrib]
  rw [Matrix.mul_assoc, Matrix.adjugate_mul S, hSdet, one_smul, Matrix.mul_one]
  rw [adjugate_sgnMat_mul_adjugate_rot hσ, Matrix.mul_assoc]

theorem normConj_spec {A S : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {α θ σ d : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hrel : ∀ x, A (x + α) = S x * A x * Work.TMContract.rot θ) (hdet : ∀ x, (A x).det = d) (hd : d ≠ 0)
    (hσd : σ * d = |d|) :
    (∀ x, (Work.TMComp.normConj A σ x).det = 1) ∧
      (∀ x, Work.TMComp.normConj A σ (x + α) * S x
        = Work.TMContract.rot (-(σ * θ)) * Work.TMComp.normConj A σ x) := by
  have hsqrt_ne : Real.sqrt |d| ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    exact abs_pos.mpr hd
  have hdsq : Real.sqrt |d| * Real.sqrt |d| = |d| := by
    rw [← sq (Real.sqrt |d|), Real.sq_sqrt (abs_nonneg d)]
  have hsd : σ * d = Real.sqrt |d| * Real.sqrt |d| := by
    rw [hσd]; exact hdsq.symm
  have hk : (Real.sqrt |d|)⁻¹ * (Real.sqrt |d|)⁻¹ * (σ * d) = 1 := by
    rw [hsd,
      show (Real.sqrt |d|)⁻¹ * (Real.sqrt |d|)⁻¹ * (Real.sqrt |d| * Real.sqrt |d|)
        = ((Real.sqrt |d|)⁻¹ * Real.sqrt |d|) * ((Real.sqrt |d|)⁻¹ * Real.sqrt |d|) by ring,
      inv_mul_cancel₀ hsqrt_ne, one_mul]
  constructor
  · intro x
    have h1 : (Work.TMComp.normConj A σ x).det
        = ((Real.sqrt |(A x).det|)⁻¹)^2 * (A x * Work.TMComp.sgnMat σ).det := by
      simp only [Work.TMComp.normConj, Matrix.det_smul, Matrix.det_adjugate]
      norm_num
    rw [h1, Matrix.det_mul, hdet x, det_sgnMat, sq, mul_comm d σ, hk]
  · intro x
    -- `det S(x) = 1`, from `det A(x+α) = det S(x) · d · 1 = d`
    have hSdet : (S x).det = 1 := by
      have h := hdet (x + α)
      simp only [hrel x, Matrix.det_mul, hdet x, det_rot, mul_one] at h
      exact mul_right_cancel₀ hd (by simpa using h)
    have hnorm1 : Work.TMComp.normConj A σ (x + α)
        = (Real.sqrt |d|)⁻¹ • ((S x * A x * Work.TMContract.rot θ) * Work.TMComp.sgnMat σ).adjugate := by
      simp only [Work.TMComp.normConj]
      rw [hdet (x + α), hrel x]
    have hnorm2 : Work.TMComp.normConj A σ x
        = (Real.sqrt |d|)⁻¹ • (A x * Work.TMComp.sgnMat σ).adjugate := by
      simp only [Work.TMComp.normConj]
      rw [hdet x]
    rw [hnorm1, hnorm2, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    exact adjugate_mul_sgnMat_mul (A x) (S x * A x * Work.TMContract.rot θ) (S x) hσ rfl hSdet

end Work.TMComp.LocCantor
