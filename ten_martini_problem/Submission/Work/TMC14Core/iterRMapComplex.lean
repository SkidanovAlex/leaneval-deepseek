import Mathlib
import Submission.Work.TMComp.RotBasics.Defs

namespace Work.TMC14Core

/-- The complex transfer matrix `tmC` is the image of the real transfer matrix `tmR`
under the coercion `ℝ → ℂ` applied entrywise. -/
lemma tmR_map_ofReal (lam E x : ℝ) :
    (Work.TMContract.tmR lam E x).map Complex.ofRealHom = Work.TMContract.tmC lam (E : ℂ) x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Work.TMContract.tmR, Work.TMContract.tmC, Complex.ofRealHom]

theorem iterRMapComplex (α lam E : ℝ) (n : ℕ) (x : ℝ) : (Work.TMComp.RotBasics.iterR α lam E n x).map Complex.ofRealHom = Work.TMContract.iterC α lam (E : ℂ) n x := by
  induction n with
  | zero =>
    simp only [Work.TMComp.RotBasics.iterR, Work.TMContract.iterC]
    exact Matrix.map_one Complex.ofRealHom (map_zero _) (map_one _)
  | succ n ih =>
    simp only [Work.TMComp.RotBasics.iterR, Work.TMContract.iterC]
    rw [Matrix.map_mul, tmR_map_ofReal, ih]

end Work.TMC14Core
