import Mathlib
import Submission.Work.WilE9G.Assembly.poly_eval_mono

namespace Work.WilE9G.Assembly

noncomputable def combineR (b5 : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2 * (b5 + Polynomial.C 1) + Polynomial.X + Polynomial.C 1

noncomputable def masterPoly (p2 b4 b5 : Polynomial ℕ) : Polynomial ℕ :=
  (Polynomial.X + Polynomial.C 1) * (b5 + Polynomial.C 1) * (p2.comp (b4.comp (combineR b5)))
    + (b4.comp (combineR b5)) + (b5 + Polynomial.C 1) + Polynomial.X + Polynomial.C 4

theorem masterPoly_bound (p2 b4 b5 : Polynomial ℕ) (D : ℕ) :
    (b5 + Polynomial.C 1).eval D ≤ (masterPoly p2 b4 b5).eval D ∧
    (b4.comp (combineR b5)).eval D ≤ (masterPoly p2 b4 b5).eval D ∧
    (p2.comp (b4.comp (combineR b5))).eval D ≤ (masterPoly p2 b4 b5).eval D ∧
    (D + 1) * (b5.eval D + 1) * (p2.comp (b4.comp (combineR b5))).eval D
      ≤ (masterPoly p2 b4 b5).eval D ∧
    (b5 + Polynomial.C 1).eval D = b5.eval D + 1 ∧
    2 * b5.eval D + D + 1 ≤ (combineR b5).eval D := by
  have hA : (b5 + Polynomial.C 1).eval D = b5.eval D + 1 := by simp
  have hC : (combineR b5).eval D = 2 * (b5.eval D + 1) + D + 1 := by
    simp only [combineR, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
  have hM : (masterPoly p2 b4 b5).eval D =
      (D + 1) * (b5.eval D + 1) * (p2.comp (b4.comp (combineR b5))).eval D
        + (b4.comp (combineR b5)).eval D + (b5.eval D + 1) + D + 4 := by
    simp only [masterPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
  refine ⟨?_, ?_, ?_, ?_, hA, ?_⟩
  · rw [hA, hM]
    set X := (p2.comp (b4.comp (combineR b5))).eval D with hXdef
    set B := (b4.comp (combineR b5)).eval D with hBdef
    set A := b5.eval D + 1 with hAdef
    set P := (D + 1) * A * X with hPdef
    omega
  · rw [hM]
    set X := (p2.comp (b4.comp (combineR b5))).eval D with hXdef
    set B := (b4.comp (combineR b5)).eval D with hBdef
    set A := b5.eval D + 1 with hAdef
    set P := (D + 1) * A * X with hPdef
    omega
  · rw [hM]
    set X := (p2.comp (b4.comp (combineR b5))).eval D with hXdef
    set B := (b4.comp (combineR b5)).eval D with hBdef
    set A := b5.eval D + 1 with hAdef
    set P := (D + 1) * A * X with hPdef
    have hApos : 0 < A := by omega
    have hXleP : X ≤ P := by
      rw [hPdef]
      exact Nat.le_mul_of_pos_left X (Nat.mul_pos (Nat.succ_pos D) hApos)
    omega
  · rw [hM]
    set X := (p2.comp (b4.comp (combineR b5))).eval D with hXdef
    set B := (b4.comp (combineR b5)).eval D with hBdef
    set A := b5.eval D + 1 with hAdef
    set P := (D + 1) * A * X with hPdef
    omega
  · rw [hC]; omega

end Work.WilE9G.Assembly
