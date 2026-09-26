import Mathlib
import Submission.Work.SGsep.hand.HandDefs2

namespace Work.SGsep.hand

open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-! ## Vector/matrix bridges used below -/

/-- The map `v ↦ v.toFun` (the three integer coordinates as a function `Fin 3 → ℤ`) is injective. -/
theorem V3.toFun_injective : Function.Injective (V3.toFun) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [V3.toFun] at h0 h1 h2
  cases a; cases b; simp_all

/-- The zero vector has the zero function as its coordinate vector. -/
theorem V3.toFun_zero : (V3.zero).toFun = 0 := by
  funext i; fin_cases i <;> rfl

/-- Conjugating the rank-one matrix `c wᵀ` by `U` gives the rank-one matrix of `U c` and
`(U⁻¹)ᵀ w`.  This is the entrywise identity `(U (c wᵀ) U⁻¹)_{ij} = (U c)_i ((U⁻¹)ᵀ w)_j`. -/
theorem conj_rankOne {U : IMat} {c w : IVec} :
    U * rankOne c w * invMat U = rankOne (U.mulVec c) ((invMat U).transpose.mulVec w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOne, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.transpose_apply] <;> ring

/-- The rank-one matrix `c wᵀ` determines `w` from `c`: if a conjugation sends `c` to `c'` and
`c wᵀ` to `c' w'ᵀ` (as matrices), then `w'` is the contragredient transform of `w`. -/
theorem rankOne_eq_conj_V3 {U : IMat} {c c' w w' : V3} (hU : IsUnit U.det)
    (hcne : c ≠ V3.zero) (hc : c'.toFun = U.mulVec c.toFun)
    (h : rankOne c'.toFun w'.toFun = U * rankOne c.toFun w.toFun * invMat U) :
    w'.toFun = (invMat U).transpose.mulVec w.toFun := by
  -- `U * (c wᵀ) * U⁻¹ = (U c) ((U⁻¹)ᵀ w)ᵀ`, so `h` describes both sides through `c'`.
  have hkey : U * rankOne c.toFun w.toFun * invMat U
      = rankOne (U.mulVec c.toFun) ((invMat U).transpose.mulVec w.toFun) :=
    conj_rankOne
  rw [hkey, ← hc] at h
  -- `c ≠ 0`, and `U` is invertible, so `c' = U c ≠ 0`: some entry of `c'` is nonzero.
  have hc0 : c.toFun ≠ 0 := by
    intro hz
    exact hcne (V3.toFun_injective (by rw [hz, V3.toFun_zero]))
  have hc'ne : c'.toFun ≠ 0 := by
    intro hz
    apply hc0
    have h1 : (invMat U).mulVec c'.toFun = 0 := by rw [hz]; simp
    rw [hc, Matrix.mulVec_mulVec, invMat_mul hU, Matrix.one_mulVec] at h1
    exact h1
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc'ne
  -- Comparing the `i`-th entries and cancelling the nonzero factor `c'ᵢ` gives `w' = (U⁻¹)ᵀ w`.
  funext j
  have hij := congrFun (congrFun h i) j
  simp only [rankOne] at hij
  exact mul_left_cancel₀ hi hij

end Work.SGsep.hand
