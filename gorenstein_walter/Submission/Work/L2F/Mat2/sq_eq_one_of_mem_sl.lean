import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Mat2

/-- Pure field algebra underlying `sq_eq_one_of_mem_sl`.

If four scalars of a field with `2 ≠ 0` satisfy `a * a + b * c = 1`, `b * c + d * d = 1`,
`b * (a + d) = 0`, `c * (a + d) = 0` and `a * d - b * c = 1`, then `(a, b, c, d)` is either
`(1, 0, 0, 1)` or `(-1, 0, 0, -1)`.

Adding the first two equations and using `a * d - b * c = 1` gives `(a + d) ^ 2 = 4`, hence
`(a + d - 2) * (a + d + 2) = 0`, so `a + d = 2` or `a + d = -2`.  Since `2 ≠ 0` (and hence
`-2 ≠ 0`), the equations `b * (a + d) = 0` and `c * (a + d) = 0` force `b = c = 0`; then
`a * a = 1` and `a * d = 1` give `a = d` (as `a ≠ 0`), and cancelling the factor `2` in
`2 * d = a + d ± a = ±2` gives `d = ±1`. -/
lemma entries_of_sq_eq_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) {a b c d : F}
    (h00 : a * a + b * c = 1) (h11 : b * c + d * d = 1)
    (h01 : b * (a + d) = 0) (h10 : c * (a + d) = 0) (hdet : a * d - b * c = 1) :
    (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = -1 ∧ b = 0 ∧ c = 0 ∧ d = -1) := by
  have hsq : (a + d) ^ 2 = 4 := by linear_combination (h00 + h11) + 2 * hdet
  have hfac : (a + d - 2) * (a + d + 2) = 0 := by linear_combination hsq
  have h2neg : (-(2 : F)) ≠ 0 := neg_ne_zero.mpr h2
  have ha0_of : ∀ hh : a * a = 1, a ≠ 0 := by
    intro hh h0
    rw [h0] at hh
    simp at hh
  rcases mul_eq_zero.mp hfac with hcase | hcase
  · rw [sub_eq_zero] at hcase
    have hb : b = 0 := by
      have h := h01
      rw [hcase] at h
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h h2
    have hc : c = 0 := by
      have h := h10
      rw [hcase] at h
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h h2
    have ha2 : a * a = 1 := by have h := h00; rw [hb, hc] at h; simpa using h
    have had : a * d = 1 := by have h := hdet; rw [hb, hc] at h; simpa using h
    have ha_eq : a = d := mul_left_cancel₀ (ha0_of ha2) (ha2.trans had.symm)
    have h2d : (2 : F) * d = 2 * 1 := by linear_combination hcase - ha_eq
    have hd1 : d = 1 := mul_left_cancel₀ h2 h2d
    exact Or.inl ⟨ha_eq.trans hd1, hb, hc, hd1⟩
  · rw [add_eq_zero_iff_eq_neg] at hcase
    have hb : b = 0 := by
      have h := h01
      rw [hcase] at h
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h h2neg
    have hc : c = 0 := by
      have h := h10
      rw [hcase] at h
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h h2neg
    have ha2 : a * a = 1 := by have h := h00; rw [hb, hc] at h; simpa using h
    have had : a * d = 1 := by have h := hdet; rw [hb, hc] at h; simpa using h
    have ha_eq : a = d := mul_left_cancel₀ (ha0_of ha2) (ha2.trans had.symm)
    have h2d : (2 : F) * d = 2 * (-1) := by linear_combination hcase - ha_eq
    have hd1 : d = -1 := mul_left_cancel₀ h2 h2d
    exact Or.inr ⟨ha_eq.trans hd1, hb, hc, hd1⟩

/-- A `2 × 2` matrix over a field with `2 ≠ 0` that satisfies `M * M = 1` and `det M = 1`
is `±1`.  Proof: read off the four entries of `M * M = 1` (an involution has trace `±2` and
is forced to be scalar), then apply `entries_of_sq_eq_one` and reconstruct `M` from its four
entries. -/
lemma matrix_sq_eq_one_of_det_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) F) (h : M * M = 1) (hd : M.det = 1) :
    M = 1 ∨ M = -1 := by
  -- read the four entries of `M * M = 1`
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 1 := by
    have h' := h
    rw [Matrix.eta_fin_two M, Matrix.one_fin_two, Matrix.mul_fin_two] at h'
    simpa using congrFun (congrFun h' 0) 0
  have h11 : M 0 1 * M 1 0 + M 1 1 * M 1 1 = 1 := by
    have h' := h
    rw [Matrix.eta_fin_two M, Matrix.one_fin_two, Matrix.mul_fin_two] at h'
    have hraw : M 1 0 * M 0 1 + M 1 1 * M 1 1 = 1 := by
      simpa using congrFun (congrFun h' 1) 1
    rw [mul_comm (M 1 0) (M 0 1)] at hraw
    exact hraw
  have h01 : M 0 1 * (M 0 0 + M 1 1) = 0 := by
    have h' := h
    rw [Matrix.eta_fin_two M, Matrix.one_fin_two, Matrix.mul_fin_two] at h'
    have hraw : M 0 0 * M 0 1 + M 0 1 * M 1 1 = 0 := by
      simpa using congrFun (congrFun h' 0) 1
    linear_combination hraw
  have h10 : M 1 0 * (M 0 0 + M 1 1) = 0 := by
    have h' := h
    rw [Matrix.eta_fin_two M, Matrix.one_fin_two, Matrix.mul_fin_two] at h'
    have hraw : M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
      simpa using congrFun (congrFun h' 1) 0
    linear_combination hraw
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hd
    exact hd
  rcases entries_of_sq_eq_one F h2 h00 h11 h01 h10 hdet with ⟨ha, hb, hc, hd'⟩ | ⟨ha, hb, hc, hd'⟩
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd']
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.neg_apply, ha, hb, hc, hd']

/-- If `x ∈ SL(2,F)` satisfies `x * x = 1` and `(2:F) ≠ 0`, then `x = ±1`.
Proof (entrywise): write `x = !![a,b;c,d]`; `x*x = 1` gives `a² + bc = 1`, `d² + bc = 1`, `b(a+d) = 0`,
`c(a+d) = 0`, and `det x = ad - bc = 1`.  Adding the first two gives `a² + d² + 2bc = 2`; with
`ad = 1 + bc` this yields `(a+d)² = 4`, so `a + d = ±2`.  If `a+d = 2` then `b = c = 0` and `ad = 1`
with `a+d = 2` gives `a = d = 1`; if `a+d = -2` similarly `a = d = -1`. -/
theorem sq_eq_one_of_mem_sl (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = 1) :
    x = 1 ∨ x = Work.L2F.negOne F := by
  have hdet : (x : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe x
  rcases matrix_sq_eq_one_of_det_one F h2 (x : Matrix (Fin 2) (Fin 2) F) hx hdet with h | h
  · left
    ext i j
    rw [h]
    simp [Matrix.one_apply]
  · right
    ext i j
    rw [h]
    simp [Work.L2F.negOne, Matrix.neg_apply]

end Work.L2F.Mat2
