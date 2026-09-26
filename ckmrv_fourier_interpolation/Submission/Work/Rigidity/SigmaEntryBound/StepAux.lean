/-
# Elementary structural facts about one step of the Euclidean recursion

`M = Tpow (quo M) * Smat * nxt M` whenever `M 1 0 ≠ 0`, together with the terminal case
`M = ± Tpow (quo M)` when `M 1 0 = 0` and `detZ M = 1`.
-/
import Mathlib
import Submission.Work.Rigidity.SigmaEntryBound.Defs

namespace Work.Rigidity.SigmaEntryBound

open Matrix

theorem nxt_frozen {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M 1 0 = 0) : nxt M = M := by
  rw [nxt, if_pos h]

theorem nxt_apply {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M 1 0 ≠ 0) :
    nxt M = !![M 1 0, M 1 1; -(remz M), -(M 0 1 - quo M * M 1 1)] := by
  rw [nxt, if_neg h]

theorem nxt_entries {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M 1 0 ≠ 0) :
    (nxt M) 0 0 = M 1 0 ∧ (nxt M) 0 1 = M 1 1 ∧
    (nxt M) 1 0 = -(remz M) ∧ (nxt M) 1 1 = -(M 0 1 - quo M * M 1 1) := by
  rw [nxt_apply h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem remz_spec {M : Matrix (Fin 2) (Fin 2) ℤ} : M 0 0 = quo M * M 1 0 + remz M := by
  rw [remz]; ring

theorem step_id {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M 1 0 ≠ 0) :
    M = Tpow (quo M) * Smat * nxt M := by
  rw [nxt_apply h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tpow, Smat, remz, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem detZ_nxt {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M 1 0 ≠ 0) : detZ (nxt M) = detZ M := by
  rw [nxt_apply h]
  simp only [detZ, remz, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.head_fin_const, Matrix.head_cons, Matrix.of_apply]
  ring

theorem terminal_step {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M 1 0 = 0) (hdet : detZ M = 1) :
    M = Tpow (quo M) ∨ M = -(Tpow (quo M)) := by
  have hd : M 0 0 * M 1 1 = 1 := by
    have h1 : detZ M = M 0 0 * M 1 1 := by simp [detZ, h]
    rw [← h1, hdet]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Tpow, quo, h, ha, hb]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Tpow, quo, h, ha, hb]

end Work.Rigidity.SigmaEntryBound
