import Mathlib
import Submission.Work.Modular.GroupAlgebra

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra

set_option linter.unnecessarySeqFocus false

/-- If the `i`-th row of `A` is zero then so is the `i`-th row of `A * M`. -/
private lemma idealIRow_mul_row_eq_zero {A M : Matrix (Fin 6) (Fin 6) ℂ} {i : Fin 6}
    (h : A i = 0) : (A * M) i = 0 := by
  funext j
  simp [Matrix.mul_apply, congr_fun h]

/-- The `0`-th row of `sigmaS * X` is the `3`-rd row of `X`: the first row of `sigmaS` is the
standard basis vector `e₃`. -/
private lemma idealIRow_sigmaS_mul_row (X : Matrix (Fin 6) (Fin 6) ℂ) :
    (sigmaS * X) 0 = X 3 := by
  ext j
  simp [Matrix.mul_apply, sigmaS, Fin.sum_univ_six]

/-- Rows `0` and `3` of `(σ(T) - 1) ^ 2` vanish (rows `0` and `1` of `σ(T) - 1` are equal, and
so are rows `3` and `4`). -/
private lemma idealIRow_sigmaT_sub_one_sq_rows :
    (((sigmaT - (1 : Matrix (Fin 6) (Fin 6) ℂ)) ^ 2) 0 = 0) ∧
      (((sigmaT - (1 : Matrix (Fin 6) (Fin 6) ℂ)) ^ 2) 3 = 0) := by
  constructor
  · ext j
    fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.sub_apply, sigmaT, Fin.sum_univ_six, pow_two] <;> norm_num
  · ext j
    fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.sub_apply, sigmaT, Fin.sum_univ_six, pow_two] <;> norm_num

/-- The first row of the six-dimensional representation `σ` vanishes on the right ideal `I`;
this is the paper's observation that the first rows of
`σ ((T - 1) ^ 2 * r)` and `σ (S * (T - 1) ^ 2 * r)` both vanish. -/
theorem sigmaAlg_idealI_row {r : GroupRing} (hr : r ∈ idealI) : (sigmaAlg r) 0 = 0 := by
  refine Submodule.span_induction (p := fun x _ => (sigmaAlg x) 0 = 0) ?_ ?_ ?_ ?_ hr
  · rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · rw [map_mul, map_pow, map_sub, map_one, sigmaAlg_tR]
      exact idealIRow_mul_row_eq_zero idealIRow_sigmaT_sub_one_sq_rows.1
    · rw [map_mul, map_mul, map_pow, map_sub, map_one, sigmaAlg_tR, sigmaAlg_sR, mul_assoc]
      rw [idealIRow_sigmaS_mul_row]
      exact idealIRow_mul_row_eq_zero idealIRow_sigmaT_sub_one_sq_rows.2
  · rw [map_zero]
    funext j
    rw [Matrix.zero_apply, Pi.zero_apply]
  · intro x y _ _ hx hy
    rw [map_add]
    funext j
    rw [Matrix.add_apply, congr_fun hx j, congr_fun hy j, Pi.zero_apply, zero_add]
  · intro a x _ hx
    rw [map_smul]
    funext j
    rw [Matrix.smul_apply, congr_fun hx j, Pi.zero_apply, smul_zero]

end Work.Modular
