import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one

/-!
# TMC7Core.Avalanche.rift : the exact rift formula in dimension two

For `X, Y ∈ SL₂(ℂ)` the *rift* is
`R(X,Y) = ‖X Y‖_F / (‖X‖_F ‖Y‖_F) ∈ (0,1]`.

Writing `X = U · diag(α, α⁻¹) · Vᴴ` and `Y = P · diag(β, β⁻¹) · Qᴴ` with `α, β ≥ 1`
(singular value decompositions) and `q = |(Vᴴ * P) 0 0|²`, one has the exact formula

  `R(X,Y)² = (q(α⁴β⁴+1) + (1-q)(α⁴+β⁴)) / ((α⁴+1)(β⁴+1))`.

Everything rests on `frob A ^ 2 = ((A * Aᴴ).trace).re` and unitary invariance of `frob`,
after which only a diagonal-times-unitary-times-diagonal expansion is needed.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

namespace Work.TMC7Core.Avalanche

/-- `frob A ^ 2 = ((A * Aᴴ).trace).re`. -/
theorem frob_sq_eq_trace_re (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ((A * Aᴴ).trace).re = frob A ^ 2 := by
  have hcc : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := by
    intro z
    rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  rw [frob_sq, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Fin.sum_univ_two]
  simp only [Complex.add_re, hcc]
  ring

/-- `frob (U * M * Vᴴ) = frob M` when `U` and `V` are unitary. -/
theorem frob_conjTranspose_unitary (U V M : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    frob (U * M * Vᴴ) = frob M := by
  have htr : ((U * M * Vᴴ) * (U * M * Vᴴ)ᴴ).trace = (M * Mᴴ).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show U * M * Vᴴ * (V * (Mᴴ * Uᴴ)) = U * M * (Vᴴ * V) * (Mᴴ * Uᴴ) by noncomm_ring, hV,
      mul_one]
    rw [show U * M * (Mᴴ * Uᴴ) = U * (M * Mᴴ) * Uᴴ by noncomm_ring, Matrix.trace_mul_cycle]
    rw [show Uᴴ * U * (M * Mᴴ) = M * Mᴴ by rw [hU, one_mul]]
  have hsq : frob (U * M * Vᴴ) ^ 2 = frob M ^ 2 := by
    rw [← frob_sq_eq_trace_re, htr, frob_sq_eq_trace_re]
  nlinarith [hsq, frob_nonneg (U * M * Vᴴ), frob_nonneg M]


/-- Left unitary invariance of `frob`: `frob (U * M) = frob M` for `Uᴴ * U = 1`. -/
theorem frob_mul_unitary (U M : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    frob (U * M) = frob M := by
  have htr : ((U * M) * (U * M)ᴴ).trace = (M * Mᴴ).trace := by
    rw [Matrix.conjTranspose_mul,
      show U * M * (Mᴴ * Uᴴ) = U * (M * Mᴴ) * Uᴴ by noncomm_ring, Matrix.trace_mul_cycle,
      show Uᴴ * U * (M * Mᴴ) = M * Mᴴ by rw [hU, one_mul]]
  have hsq : frob (U * M) ^ 2 = frob M ^ 2 := by
    rw [← frob_sq_eq_trace_re, htr, frob_sq_eq_trace_re]
  nlinarith [hsq, frob_nonneg (U * M), frob_nonneg M]

/-- Right unitary invariance of `frob`: `frob (M * U) = frob M` for `U * Uᴴ = 1`. -/
theorem frob_mul_of_unitary (M U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U * Uᴴ = 1) :
    frob (M * U) = frob M := by
  have htr : ((M * U) * (M * U)ᴴ).trace = (M * Mᴴ).trace := by
    rw [Matrix.conjTranspose_mul, show M * U * (Uᴴ * Mᴴ) = M * (U * Uᴴ) * Mᴴ by noncomm_ring, hU,
      show M * 1 * Mᴴ = M * Mᴴ by rw [mul_one]]
  have hsq : frob (M * U) ^ 2 = frob M ^ 2 := by
    rw [← frob_sq_eq_trace_re, htr, frob_sq_eq_trace_re]
  nlinarith [hsq, frob_nonneg (M * U), frob_nonneg M]

/-! ## 3. Complex norms of real scalars -/

theorem norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
    ring
  nlinarith [norm_nonneg (r : ℂ), abs_nonneg r]

/-! ## 4. Real part of a diagonal entry of `M * Mᴴ` -/

theorem re_mul_star (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem re_mul_conjTranspose_diag (M : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    ((M * Mᴴ) i i).re = ∑ j, ‖M i j‖ ^ 2 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.add_re, re_mul_star]

/-! ## 5. Diagonal matrices -/

/-- `(diag d * R * diag e) i j = d i * R i j * e j`. -/
theorem diagonal_mul_mul_diagonal_apply (d e : Fin 2 → ℂ) (R : Matrix (Fin 2) (Fin 2) ℂ)
    (i j : Fin 2) : (diagonal d * R * diagonal e) i j = d i * R i j * e j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- `frob (diag(α, α⁻¹)) ^ 2 = α ^ 2 + (α ^ 2)⁻¹` for `α > 0`. -/
theorem frob_diagonal_sq {α : ℝ} (hα : 0 < α) :
    frob (diagonal ![((α : ℝ) : ℂ), ((α⁻¹ : ℝ) : ℂ)]) ^ 2 = α ^ 2 + (α ^ 2)⁻¹ := by
  have h1 : ‖(((α : ℝ) : ℂ))‖ = α := by rw [norm_ofReal, abs_of_pos hα]
  have h2 : ‖(((α⁻¹ : ℝ) : ℂ))‖ = α⁻¹ := by rw [norm_ofReal, abs_of_pos (inv_pos.mpr hα)]
  simp only [frob_sq, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
    Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
  simp only [Fin.isValue, cons_val_zero, cons_val_one, h1, h2, norm_zero]
  ring

/-- Expansion of `frob (diag(α,α⁻¹) * R * diag(β,β⁻¹)) ^ 2` for `α, β > 0`. -/
theorem frob_diag_mul_diag_sq (R : Matrix (Fin 2) (Fin 2) ℂ) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    frob (diagonal ![((α : ℝ) : ℂ), ((α⁻¹ : ℝ) : ℂ)] * R
      * diagonal ![((β : ℝ) : ℂ), ((β⁻¹ : ℝ) : ℂ)]) ^ 2
      = ‖R 0 0‖ ^ 2 * α ^ 2 * β ^ 2 + ‖R 0 1‖ ^ 2 * α ^ 2 * (β ^ 2)⁻¹
        + ‖R 1 0‖ ^ 2 * (α ^ 2)⁻¹ * β ^ 2 + ‖R 1 1‖ ^ 2 * (α ^ 2)⁻¹ * (β ^ 2)⁻¹ := by
  have h1 : ‖(((α : ℝ) : ℂ))‖ = α := by rw [norm_ofReal, abs_of_pos hα]
  have h2 : ‖(((α⁻¹ : ℝ) : ℂ))‖ = α⁻¹ := by rw [norm_ofReal, abs_of_pos (inv_pos.mpr hα)]
  have h3 : ‖(((β : ℝ) : ℂ))‖ = β := by rw [norm_ofReal, abs_of_pos hβ]
  have h4 : ‖(((β⁻¹ : ℝ) : ℂ))‖ = β⁻¹ := by rw [norm_ofReal, abs_of_pos (inv_pos.mpr hβ)]
  simp only [frob_sq, diagonal_mul_mul_diagonal_apply, norm_mul, mul_pow]
  simp only [Fin.isValue, cons_val_zero, cons_val_one, h1, h2, h3, h4]
  ring

/-! ## 6. Unitary `2×2` matrices -/

/-- For a unitary `R` the four entry moduli are determined by `q = ‖R 0 0‖ ^ 2`:
`‖R 1 1‖ ^ 2 = q` and `‖R 0 1‖ ^ 2 = ‖R 1 0‖ ^ 2 = 1 - q`. -/
theorem unitary_entries (R : Matrix (Fin 2) (Fin 2) ℂ) (hR : Rᴴ * R = 1) (hR' : R * Rᴴ = 1) :
    ‖R 1 1‖ ^ 2 = ‖R 0 0‖ ^ 2 ∧ ‖R 0 1‖ ^ 2 = 1 - ‖R 0 0‖ ^ 2
      ∧ ‖R 1 0‖ ^ 2 = 1 - ‖R 0 0‖ ^ 2 := by
  have key : ∀ i : Fin 2, ((Rᴴ * R) i i).re = ∑ j, ‖R j i‖ ^ 2 := by
    intro i
    have h := re_mul_conjTranspose_diag Rᴴ i
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [h]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.conjTranspose_apply, norm_star]
  have e00 : ((R * Rᴴ) (0 : Fin 2) 0).re = 1 := by rw [hR']; norm_num
  have f00 : ((Rᴴ * R) (0 : Fin 2) 0).re = 1 := by rw [hR]; norm_num
  have f11 : ((Rᴴ * R) (1 : Fin 2) 1).re = 1 := by rw [hR]; norm_num
  rw [re_mul_conjTranspose_diag] at e00
  rw [key] at f00 f11
  simp only [Fin.sum_univ_two] at e00 f00 f11
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ## 7. The rift formula -/

/-- **The rift formula.**  For unitary `R` and `α, β > 0`,
`R(diag(α,α⁻¹) · R · diag(β,β⁻¹))² = (q(α⁴β⁴+1) + (1-q)(α⁴+β⁴))/((α⁴+1)(β⁴+1))`
with `q = ‖R 0 0‖²`. -/
theorem rift_formula (R : Matrix (Fin 2) (Fin 2) ℂ) (hR : Rᴴ * R = 1) (hR' : R * Rᴴ = 1)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    frob (diagonal ![((α : ℝ) : ℂ), ((α⁻¹ : ℝ) : ℂ)] * R
        * diagonal ![((β : ℝ) : ℂ), ((β⁻¹ : ℝ) : ℂ)]) ^ 2
      / (frob (diagonal ![((α : ℝ) : ℂ), ((α⁻¹ : ℝ) : ℂ)]) ^ 2
        * frob (diagonal ![((β : ℝ) : ℂ), ((β⁻¹ : ℝ) : ℂ)]) ^ 2)
      = (‖R 0 0‖ ^ 2 * (α ^ 4 * β ^ 4 + 1) + (1 - ‖R 0 0‖ ^ 2) * (α ^ 4 + β ^ 4))
        / ((α ^ 4 + 1) * (β ^ 4 + 1)) := by
  obtain ⟨e11, e01, e10⟩ := unitary_entries R hR hR'
  rw [frob_diag_mul_diag_sq R hα hβ, frob_diagonal_sq hα, frob_diagonal_sq hβ, e11, e10, e01]
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  field_simp
  ring

/-- **Rift formula, SVD form.**  If `X = U · diag(α,α⁻¹) · Vᴴ` and `Y = P · diag(β,β⁻¹) · Qᴴ`
with `U, V, P, Q` unitary, then

`R(X,Y)² = (q(α⁴β⁴+1) + (1-q)(α⁴+β⁴)) / ((α⁴+1)(β⁴+1))`,   `q = ‖(Vᴴ * P) 0 0‖²`. -/
theorem rift_formula_svd (X Y U V P Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1)
    (hV' : V * Vᴴ = 1) (hP' : P * Pᴴ = 1) (_hQ' : Q * Qᴴ = 1)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hXd : X = U * diagonal ![((α : ℝ) : ℂ), ((α⁻¹ : ℝ) : ℂ)] * Vᴴ)
    (hYd : Y = P * diagonal ![((β : ℝ) : ℂ), ((β⁻¹ : ℝ) : ℂ)] * Qᴴ) :
    frob (X * Y) ^ 2 / (frob X ^ 2 * frob Y ^ 2)
      = (‖(Vᴴ * P) 0 0‖ ^ 2 * (α ^ 4 * β ^ 4 + 1) + (1 - ‖(Vᴴ * P) 0 0‖ ^ 2) * (α ^ 4 + β ^ 4))
        / ((α ^ 4 + 1) * (β ^ 4 + 1)) := by
  have hR : (Vᴴ * P)ᴴ * (Vᴴ * P) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      show Pᴴ * V * (Vᴴ * P) = Pᴴ * (V * Vᴴ) * P by noncomm_ring, hV',
      show Pᴴ * 1 * P = Pᴴ * P by rw [mul_one], hP]
  have hR' : (Vᴴ * P) * (Vᴴ * P)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      show Vᴴ * P * (Pᴴ * V) = Vᴴ * (P * Pᴴ) * V by noncomm_ring, hP',
      show Vᴴ * 1 * V = Vᴴ * V by rw [mul_one], hV]
  have hQr : Qᴴ * (Qᴴ)ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hQ
  have hVr : Vᴴ * (Vᴴ)ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hV
  have hXY : X * Y = U * (diagonal ![((α : ℝ) : ℂ), ((α⁻¹ : ℝ) : ℂ)] * (Vᴴ * P)
      * diagonal ![((β : ℝ) : ℂ), ((β⁻¹ : ℝ) : ℂ)]) * Qᴴ := by
    rw [hXd, hYd]; noncomm_ring
  have hXY' : frob (X * Y) = frob (diagonal ![((α : ℝ) : ℂ), ((α⁻¹ : ℝ) : ℂ)] * (Vᴴ * P)
      * diagonal ![((β : ℝ) : ℂ), ((β⁻¹ : ℝ) : ℂ)]) := by
    rw [hXY, mul_assoc, frob_mul_unitary U _ hU]
    exact frob_mul_of_unitary _ Qᴴ hQr
  have hX' : frob X = frob (diagonal ![((α : ℝ) : ℂ), ((α⁻¹ : ℝ) : ℂ)]) := by
    rw [hXd, mul_assoc, frob_mul_unitary U _ hU]
    exact frob_mul_of_unitary _ Vᴴ hVr
  have hY' : frob Y = frob (diagonal ![((β : ℝ) : ℂ), ((β⁻¹ : ℝ) : ℂ)]) := by
    rw [hYd, mul_assoc, frob_mul_unitary P _ hP]
    exact frob_mul_of_unitary _ Qᴴ hQr
  rw [hXY', hX', hY', rift_formula (Vᴴ * P) hR hR' hα hβ]

/-! ## 8. Elementary (SVD-free) rift bounds -/

theorem frob_pos_of_det_one {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M.det = 1) : 0 < frob M :=
  lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    (Cocycle.frob_sqrt_two_le_of_det_one h)

/-- `frob M.adjugate = frob M`. -/
theorem frob_adjugate (M : Matrix (Fin 2) (Fin 2) ℂ) : frob M.adjugate = frob M := by
  have hadj : M.adjugate = !![(M 1 1), -(M 0 1); -(M 1 0), (M 0 0)] := Matrix.adjugate_fin_two M
  have h : frob M.adjugate ^ 2 = frob M ^ 2 := by
    rw [hadj]
    simp only [frob_sq]
    norm_num
    ring
  nlinarith [h, frob_nonneg M.adjugate, frob_nonneg M]

/-- If `M.det = 1` then `frob Q ≤ frob M * frob (M * Q)`, i.e. `Q = M.adjugate * (M * Q)`. -/
theorem frob_le_frob_mul_frob_mul (M Q : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1) :
    frob Q ≤ frob M * frob (M * Q) := by
  have h2 : frob Q = frob (M.adjugate * (M * Q)) := by
    congr 1
    rw [← mul_assoc, Matrix.adjugate_mul, hM, one_smul, one_mul]
  rw [h2]
  calc frob (M.adjugate * (M * Q)) ≤ frob M.adjugate * frob (M * Q) := Cocycle.frob_mul_le _ _
    _ = frob M * frob (M * Q) := by rw [frob_adjugate]

/-- If `Q.det = 1` then `frob M ≤ frob (M * Q) * frob Q`, i.e. `M = (M * Q) * Q.adjugate`. -/
theorem frob_le_frob_mul_frob_mul' (M Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : Q.det = 1) :
    frob M ≤ frob (M * Q) * frob Q := by
  have h2 : frob M = frob ((M * Q) * Q.adjugate) := by
    congr 1
    rw [mul_assoc, Matrix.mul_adjugate, hQ, one_smul, mul_one]
  rw [h2]
  calc frob ((M * Q) * Q.adjugate) ≤ frob (M * Q) * frob Q.adjugate := Cocycle.frob_mul_le _ _
    _ = frob (M * Q) * frob Q := by rw [frob_adjugate]

/-- `1 / ‖X‖_F⁴ ≤ R(X,Y)² = ‖XY‖_F² / (‖X‖_F² ‖Y‖_F²)` for `X, Y ∈ SL₂(ℂ)`. -/
theorem rift_ge_inv_frob_left (X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.det = 1) (hY : Y.det = 1) :
    1 / frob X ^ 4 ≤ frob (X * Y) ^ 2 / (frob X ^ 2 * frob Y ^ 2) := by
  have hb := frob_le_frob_mul_frob_mul X Y hX
  have hXp : 0 < frob X := frob_pos_of_det_one hX
  have hYp : 0 < frob Y := frob_pos_of_det_one hY
  have hXYp : 0 < frob (X * Y) := frob_pos_of_det_one (by rw [Matrix.det_mul, hX, hY, one_mul])
  field_simp
  nlinarith [hb, hXp, hYp, hXYp]

/-- `1 / ‖Y‖_F⁴ ≤ R(X,Y)²` for `X, Y ∈ SL₂(ℂ)`. -/
theorem rift_ge_inv_frob_right (X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.det = 1) (hY : Y.det = 1) :
    1 / frob Y ^ 4 ≤ frob (X * Y) ^ 2 / (frob X ^ 2 * frob Y ^ 2) := by
  have hb := frob_le_frob_mul_frob_mul' X Y hY
  have hXp : 0 < frob X := frob_pos_of_det_one hX
  have hYp : 0 < frob Y := frob_pos_of_det_one hY
  have hXYp : 0 < frob (X * Y) := frob_pos_of_det_one (by rw [Matrix.det_mul, hX, hY, one_mul])
  field_simp
  nlinarith [hb, hXp, hYp, hXYp]

/-! ## 9. Consequences of a singular decomposition

Given the factorization `X = U · diag(a,b) · Vᴴ` with `U, V` unitary and `a b = 1` (so
`a, b` are the singular values of `X`), we record the Frobenius identity
`‖X‖_F² = a² + b²` and the resulting order bounds on `max a b = ‖X‖_op`. -/

/-- `frob (diagonal ![a, b]) ^ 2 = a ^ 2 + b ^ 2` (no positivity needed). -/
theorem frob_diagonal_sq' (a b : ℝ) :
    frob (diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)]) ^ 2 = a ^ 2 + b ^ 2 := by
  simp only [frob_sq, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
    Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0), Fin.isValue, cons_val_zero,
    cons_val_one, norm_zero]
  rw [norm_ofReal, norm_ofReal, sq_abs, sq_abs]
  ring

/-- `‖X‖_F² = a² + b²` when `X = U · diag(a,b) · Vᴴ` with `U, V` unitary. -/
theorem frob_eq_of_svd (X U V : Matrix (Fin 2) (Fin 2) ℂ) {a b : ℝ}
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hX : X = U * diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] * Vᴴ) :
    frob X ^ 2 = a ^ 2 + b ^ 2 := by
  rw [hX, mul_assoc, frob_mul_unitary U _ hU,
    show frob (diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)] * Vᴴ)
        = frob (diagonal ![((a : ℝ) : ℂ), ((b : ℝ) : ℂ)]) from
      frob_mul_of_unitary _ Vᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact hV)]
  exact frob_diagonal_sq' a b

/-- Arithmetic consequences of `a b = 1`, `a, b > 0`, `a² + b² = t`: the larger of `a, b` is
the operator norm of `X` and lies in `[√(t/2), √t]`, the smaller is its inverse, and both
are bounded by `1` on the appropriate side. -/
theorem svd_bounds {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1)
    (ht : a ^ 2 + b ^ 2 = t) :
    1 ≤ max a b ∧ min a b ≤ 1 ∧ max a b * min a b = 1 ∧ max a b ≤ Real.sqrt t
      ∧ Real.sqrt t ≤ Real.sqrt 2 * max a b := by
  have hmax : 0 < max a b := lt_of_lt_of_le ha (le_max_left a b)
  have h1 : 1 ≤ max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; nlinarith [hab, ha, hb, h]
    · rw [max_eq_left h]; nlinarith [hab, ha, hb, h]
  have hmin' : min a b = 1 / max a b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h, eq_div_iff (ne_of_gt hb)]; exact hab
    · rw [min_eq_right h, max_eq_left h, eq_div_iff (ne_of_gt ha)]; linarith [hab]
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · rw [hmin', div_le_one hmax]; exact h1
  · rw [hmin', mul_one_div, div_self (ne_of_gt hmax)]
  · have hle : max a b ^ 2 ≤ t := by
      rcases le_total a b with h | h
      · rw [max_eq_right h]; nlinarith [ht]
      · rw [max_eq_left h]; nlinarith [ht]
    rw [← Real.sqrt_sq (le_of_lt hmax)]
    exact Real.sqrt_le_sqrt hle
  · have h2 : a ^ 2 + b ^ 2 ≤ 2 * max a b ^ 2 := by
      nlinarith [le_max_left a b, le_max_right a b, sq_nonneg a, sq_nonneg b, hmax]
    calc Real.sqrt t = Real.sqrt (a ^ 2 + b ^ 2) := by rw [← ht]
      _ ≤ Real.sqrt (2 * max a b ^ 2) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt 2 * max a b := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (le_of_lt hmax)]

end Work.TMC7Core.Avalanche
