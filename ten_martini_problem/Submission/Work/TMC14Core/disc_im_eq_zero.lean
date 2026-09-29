import Mathlib
import Submission.Work.TMC14Core.RatRot

/-!
# TMC14Core: the discriminant of a rational approximant is real on the real axis

`disc p q lam` is the characteristic polynomial of the Bloch matrix
`blochMat p q lam (1/(4q)) 0`.  All entries of that matrix are real numbers (the
diagonal and the off-diagonal `1`'s are explicit reals, and at `k = 0` the two Bloch
corner entries are `e^{±0} = 1`), so `disc` has real coefficients, and in particular
its value at a real energy `E` is a real (rather than merely complex) number.

This is the analytic fact needed to talk about real roots of `disc`, e.g. in
`disc_deriv_ne_zero_even`/`disc_deriv_ne_zero_odd`.

The proof does not diagonalise the matrix: it uses Chambers' formula in its trace form
`disc_eval`, reducing `disc.eval E` to the trace of the real `q`-step transfer matrix
`iterR`, which is a real number.
-/

namespace Work.TMC14Core

noncomputable section

/-- At real energy, the complex transfer matrix `tmC` is the entrywise image of the real
transfer matrix `Work.TMContract.tmR` under `ℝ → ℂ`. -/
theorem tmR_map_tmC_ofRealHom (lam E x : ℝ) :
    (Work.TMContract.tmR lam E x).map Complex.ofRealHom = Work.TMC14Core.tmC lam (E : ℂ) x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Work.TMC14Core.tmC, Work.TMContract.tmR, Complex.ofRealHom]

/-- At real energy, the complex cocycle `iterC` is the entrywise image of the real cocycle
`Work.TMComp.RotBasics.iterR`. -/
theorem iterR_map_iterC_ofRealHom (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    (Work.TMComp.RotBasics.iterR α lam E n x).map Complex.ofRealHom
      = Work.TMC14Core.iterC α lam (E : ℂ) n x := by
  induction n with
  | zero =>
    simp only [Work.TMC14Core.iterC, Work.TMComp.RotBasics.iterR]
    exact Matrix.map_one Complex.ofRealHom (map_zero _) (map_one _)
  | succ n ih =>
    simp only [Work.TMC14Core.iterC, Work.TMComp.RotBasics.iterR]
    rw [Matrix.map_mul, tmR_map_tmC_ofRealHom, ih]

/-- At real energy, `trAq` is the coercion of the trace of the real `q`-step transfer
matrix; in particular it is a real number. -/
theorem trAq_eq_ofReal_trace (p : ℤ) (q : ℕ) (lam E θ : ℝ) :
    Work.TMC14Core.trAq p q lam (E : ℂ) θ
      = ((Work.TMComp.RotBasics.iterR ((p : ℝ) / (q : ℝ)) lam E q θ).trace : ℂ) := by
  rw [Work.TMC14Core.trAq, ← Matrix.trace_fin_two, ← iterR_map_iterC_ofRealHom]
  exact (AddMonoidHom.map_trace Complex.ofRealHom _).symm

/-- For `q ≥ 1`, `disc p q lam` is the characteristic polynomial of the Bloch matrix, so
`disc_eval` (Chambers' formula at `θ = 1/(4q)`) identifies its value at `E` with `trAq`. -/

theorem disc_im_eq_zero (p : ℤ) (q : ℕ) (lam E : ℝ) :
    ((Work.TMC14Core.disc p q lam).eval (E : ℂ)).im = 0 := by
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · -- `q = 0`: the matrix is `0 × 0`, its characteristic polynomial is `1`, and `1 + 2 = 3`.
    rw [hq0]
    rw [Work.TMC14Core.disc, Polynomial.eval_add, Polynomial.eval_C, Matrix.eval_charpoly]
    simp only [Matrix.det_fin_zero]
    norm_num
  · -- `q ≥ 1`: Chambers' formula expresses `disc.eval E` as `trAq`, a real trace.
    have hq : 1 ≤ q := hqpos
    rw [Work.TMC14Core.disc_eval p q lam (E : ℂ) hq, trAq_eq_ofReal_trace]
    exact Complex.ofReal_im _

end

end Work.TMC14Core
