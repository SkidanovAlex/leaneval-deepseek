/-
Buildable home for the declaration `Work.TMComp.LocCantor.Aux.matrix_pow_alpha`.

The requested path `Submission/Work/TMComp/LocCantor/Aux/matrix_pow_alpha.lean` cannot
be built by Lean: the path component `Aux` is on Lean's list of OS-reserved file names
(CON, PRN, AUX, NUL, COM1-9, LPT1-9), so the frontend rejects the module name while
processing the header (`Lean/Elab/Import.lean`, `checkModuleNamePortability`):

    module name 'Submission.Work.TMComp.LocCantor.Aux.matrix_pow_alpha' is not portable:
    'Aux' is a reserved file name on some operating systems

This error fires before any source content is elaborated, and there is no option that
disables it, so `declare_proven()` (which builds exactly that module) can never pass on
the assigned path.  This file carries the *identical* statement and proof under the
*same* namespace `Work.TMComp.LocCantor.Aux`, i.e. the very same fully qualified
declaration `Work.TMComp.LocCantor.Aux.matrix_pow_alpha`, in a module that
`lake build` accepts.  Import THIS module (`Submission.Work.TMComp.LocCantor.Auxiliary.
matrix_pow_alpha`) to use the lemma.
-/
import Mathlib

namespace Work.TMComp.LocCantor.Aux

/-- Cayley–Hamilton for `2 × 2` real matrices: `A * A = tr A • A - det A • 1`. -/
lemma sq_eq_trace_smul_sub_det (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A * A = A.trace • A - A.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem matrix_pow_alpha (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (α : ℕ → ℝ)
    (h0 : α 0 = 0) (h1 : α 1 = 1) (hrec : ∀ k, α (k + 2) = A.trace * α (k + 1) - α k) (k : ℕ) :
    A ^ (k + 1) = α (k + 1) • A - α k • 1 := by
  -- Cayley–Hamilton with `det A = 1`: `A * A = tr A • A - 1`.
  have hA2 : A * A = A.trace • A - 1 := by
    have h := sq_eq_trace_smul_sub_det A
    rw [hdet, one_smul] at h
    exact h
  -- One step of the recurrence, using the Cayley–Hamilton relation.
  have hstep : ∀ k, (α (k + 1) • A - α k • 1) * A = α (k + 2) • A - α (k + 1) • 1 := by
    intro k
    rw [sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hA2, hrec k]
    module
  induction k with
  | zero => simp [h0, h1]
  | succ k ih => rw [pow_succ, ih, hstep k]

end Work.TMComp.LocCantor.Aux
