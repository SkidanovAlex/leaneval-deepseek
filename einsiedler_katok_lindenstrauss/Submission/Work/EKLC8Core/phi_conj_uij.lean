import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

open scoped Matrix

/-!
# The conjugation action of the flow `φ_τ = diag(e^{-τ}, e^{τ}, 1)` on the root groups `U_ij`

This file proves

`φ_τ · u_ij(s) · φ_τ⁻¹ = u_ij(e^{(t_i - t_j)τ} s)`,  `t = (-1,1,0)`,

i.e. that the flow expands the entry `(i,j)` by the factor `e^{(t_i-t_j)τ}`.

The proof is a direct 3×3 matrix computation.  Since `φ_τ` is diagonal, the identity is
proved in the equivalent form `φ_τ · u_ij(s) = u_ij(e^{(t_i-t_j)τ} s) · φ_τ`, which avoids
having to identify the inverse of an element of `SL₃(ℝ)` (Mathlib defines it as an
adjugate) with `φ_{-τ}`.

The `private` helpers below are local matrix bookkeeping:
`diagonal_mul_single`/`single_mul_diagonal` compute `diagonal d * single i j c` and
`single i j c * diagonal d`, and `phi_uij_coe` writes `φ_τ` as an explicit diagonal matrix.
-/

/-- `diag(d) * (c · E_{ij}) = (d i * c) · E_{ij}`. -/
private lemma diagonal_mul_single (d : Fin 3 → ℝ) (i j : Fin 3) (c : ℝ) :
    Matrix.diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext k l
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply, mul_ite, mul_zero]
  by_cases hkl : i = k ∧ j = l
  · obtain ⟨hk, hl⟩ := hkl; subst hk; subst hl; simp
  · rw [if_neg hkl, if_neg hkl]

/-- `(c · E_{ij}) * diag(d) = (c * d j) · E_{ij}`. -/
private lemma single_mul_diagonal (d : Fin 3 → ℝ) (i j : Fin 3) (c : ℝ) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.single i j (c * d j) := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply, ite_mul, zero_mul]
  by_cases hkl : i = k ∧ j = l
  · obtain ⟨hk, hl⟩ := hkl; subst hk; subst hl; simp
  · rw [if_neg hkl, if_neg hkl]

/-- `φ_τ` is the diagonal matrix with diagonal entries `e^{t_i τ}`. -/
private lemma phi_uij_coe (τ : ℝ) :
    (phi τ : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.diagonal (fun i => Real.exp (flowExp i * τ)) := by
  show Matrix.diagonal (fun i => Real.exp ((τ • flowExp) i - (∑ j, (τ • flowExp) j) / 3)) = _
  congr 1
  funext i
  have hsum : (∑ j : Fin 3, flowExp j) = 0 := by simp [flowExp, Fin.sum_univ_three]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, hsum, mul_zero, zero_div, sub_zero]
  congr 1
  ring

/-- The matrix identity `φ_τ · u_ij(s) = u_ij(e^{(t_i-t_j)τ} s) · φ_τ`. -/
private lemma phi_mul_transvection_coe (τ s : ℝ) {i j : Fin 3} (h : i ≠ j) :
    (phi τ : Matrix (Fin 3) (Fin 3) ℝ) *
        ((Matrix.SpecialLinearGroup.transvection h s) : Matrix (Fin 3) (Fin 3) ℝ)
      = ((Matrix.SpecialLinearGroup.transvection h (Real.exp ((flowExp i - flowExp j) * τ) * s))
          : Matrix (Fin 3) (Fin 3) ℝ) * (phi τ : Matrix (Fin 3) (Fin 3) ℝ) := by
  have key : Real.exp ((flowExp i - flowExp j) * τ) * Real.exp (flowExp j * τ)
      = Real.exp (flowExp i * τ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hd : Real.exp (flowExp i * τ) * s
      = Real.exp ((flowExp i - flowExp j) * τ) * s * Real.exp (flowExp j * τ) := by
    rw [← key]; ring
  rw [phi_uij_coe]
  simp only [Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      diagonal_mul_single, single_mul_diagonal, hd]

theorem phi_conj_uij (τ s : ℝ) {i j : Fin 3} (h : i ≠ j) :
    phi τ * uij h s * (phi τ)⁻¹ = uij h (Real.exp ((flowExp i - flowExp j) * τ) * s) := by
  have key : phi τ * uij h s
      = uij h (Real.exp ((flowExp i - flowExp j) * τ) * s) * phi τ := by
    apply Matrix.SpecialLinearGroup.ext
    intro k l
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact congrFun (congrFun (phi_mul_transvection_coe τ s h) k) l
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

end Work.EKLC8Core
