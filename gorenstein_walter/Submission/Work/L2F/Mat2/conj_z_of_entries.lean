import Mathlib

namespace Work.L2F.Mat2

/-- Field-level core of `Work.L2F.Mat2.exists_conj_z`: if `a + d = 0` and `a * a + b * c = -1`
over a field with `(2:F) ≠ 0`, then `!![a,b;c,d]` is conjugate to `!![0,1;-1,0]` by an invertible
matrix.  Case `b ≠ 0`: `P = !![1,0;a,b]` has `det P = b ≠ 0`.  Case `b = 0`, `c ≠ 0`:
`P = !![0,1;c,-a]` has `det P = -c ≠ 0`.  Case `b = c = 0`: then `a*a = -1` so `a ≠ 0`, and
`P = !![1,1;a,-a]` has `det P = -2*a ≠ 0`. -/
lemma conj_z_of_entries (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) {a b c d : F}
    (htr : a + d = 0) (h : a * a + b * c = -1) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 ∧
      P * !![a, b; c, d] = !![0, 1; -1, 0] * P := by
  have hd : d = -a := by linear_combination htr
  subst hd
  by_cases hb : b = 0
  · subst hb
    have ha2 : a * a = -1 := by simpa using h
    have ha : a ≠ 0 := by
      intro ha0
      rw [ha0, mul_zero] at ha2
      exact (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)) ha2.symm
    by_cases hc : c = 0
    · subst hc
      refine ⟨!![1, 1; a, -a], ?_, ?_⟩
      · have hdet : (!![1, 1; a, -a] : Matrix (Fin 2) (Fin 2) F).det = -(2 * a) := by
          rw [Matrix.det_fin_two]; simp; ring
        rw [hdet]
        exact neg_ne_zero.mpr (mul_ne_zero h2 ha)
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        all_goals (try ring)
        all_goals (try linear_combination ha2)
    · refine ⟨!![0, 1; c, -a], ?_, ?_⟩
      · have hdet : (!![0, 1; c, -a] : Matrix (Fin 2) (Fin 2) F).det = -c := by
          rw [Matrix.det_fin_two]; simp
        rw [hdet]
        exact neg_ne_zero.mpr hc
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        all_goals (try ring)
        all_goals (try linear_combination ha2)
  · refine ⟨!![1, 0; a, b], ?_, ?_⟩
    · have hdet : (!![1, 0; a, b] : Matrix (Fin 2) (Fin 2) F).det = b := by
        rw [Matrix.det_fin_two]; simp
      rw [hdet]; exact hb
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      all_goals (try ring)
      all_goals (try linear_combination h)

end Work.L2F.Mat2
