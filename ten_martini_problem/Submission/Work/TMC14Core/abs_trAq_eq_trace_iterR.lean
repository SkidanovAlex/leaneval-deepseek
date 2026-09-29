import Mathlib
import Submission.Work.TMC14Core.RatRot

namespace Work.TMC14Core

/-!
# `‖tr A_q‖` equals the absolute trace of the real `q`-step cocycle

For real energy `E`, the complex transfer matrix `tmC` is the entrywise image of the real
transfer matrix `tmR` under the coercion `ℝ → ℂ`.  Consequently the whole cocycle `iterC`
is the image of the real cocycle `Work.TMComp.RotBasics.iterR`, and its trace is the
coercion of the real trace.  The complex norm of a real number is its absolute value,
which yields the stated identity.
-/

/-- `tmC` is the entrywise `ℝ → ℂ` image of `tmR`. -/
theorem tmR_map_tmC (lam E x : ℝ) :
    (Work.TMContract.tmR lam E x).map Complex.ofRealHom = Work.TMC14Core.tmC lam (E : ℂ) x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Work.TMC14Core.tmC, Work.TMContract.tmR, Complex.ofRealHom]

/-- At real energy, the complex cocycle `iterC` is the entrywise image of the real cocycle
`Work.TMComp.RotBasics.iterR`. -/
theorem iterR_map_iterC (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    (Work.TMComp.RotBasics.iterR α lam E n x).map Complex.ofRealHom
      = Work.TMC14Core.iterC α lam (E : ℂ) n x := by
  induction n with
  | zero =>
    simp only [Work.TMC14Core.iterC, Work.TMComp.RotBasics.iterR]
    exact Matrix.map_one Complex.ofRealHom (map_zero _) (map_one _)
  | succ n ih =>
    simp only [Work.TMC14Core.iterC, Work.TMComp.RotBasics.iterR]
    rw [Matrix.map_mul, tmR_map_tmC, ih]

theorem abs_trAq_eq_trace_iterR (p : ℤ) (q : ℕ) (lam E θ : ℝ) :
    ‖Work.TMC14Core.trAq p q lam (E : ℂ) θ‖
      = |(Work.TMComp.RotBasics.iterR ((p : ℝ) / (q : ℝ)) lam E q θ).trace| := by
  have h := iterR_map_iterC ((p : ℝ) / (q : ℝ)) lam E q θ
  have htr : Work.TMC14Core.trAq p q lam (E : ℂ) θ
      = ((Work.TMComp.RotBasics.iterR ((p : ℝ) / (q : ℝ)) lam E q θ).trace : ℂ) := by
    rw [Work.TMC14Core.trAq, ← Matrix.trace_fin_two, ← h]
    exact (AddMonoidHom.map_trace Complex.ofRealHom _).symm
  rw [htr]
  exact RCLike.norm_ofReal _

end Work.TMC14Core
