import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Trig
import Submission.Work.TMC7Core.Trig.tmZ_smul
import Submission.Work.TMC7Core.Trig.exp_mul_omega_pow
import Submission.Work.TMC7Core.Trig.matProd_smul
import Submission.Work.TMC7Core.Trig.prod_range_exp_omega

/-!
# `z^n A_n(x)` via the algebraic transfer matrix

`iterZ α lam E n z` is the ordered product of the rescaled factors `tmZ lam E (z ω^j)`
(`j = 0, …, n-1`), and at `z = e^{2πix}` each factor is `z ω^j • tmC lam E (x + jα)`
(`tmZ_smul`, together with `exp_mul_omega_pow` for the phase).  Pulling all the scalar
factors out of the product (`matProd_smul`) and multiplying them
(`prod_range_exp_omega`) gives

`iterZ α lam E n (e^{2πix}) = (e^{2πi n x} ω^{n(n-1)/2}) • A_n(x)`,

i.e. `z^n A_n(x)` up to the unimodular factor `ω^{n(n-1)/2}`.  This is the algebraic
identity behind the Herman bound and the Fourier decay of `ln ‖A_n‖`.
-/

namespace Work.TMC7Core.Trig

open Work.TMC7Core

/-- `iterZ` is the ordered product of the rescaled factors `tmZ lam E (z ω^j)`. -/
theorem iterZ_eq_matProd (α lam : ℝ) (E : ℂ) (n : ℕ) (z : ℂ) :
    iterZ α lam E n z = matProd (fun j => tmZ lam E (z * omega α ^ j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterZ, ih, matProd_succ]

theorem iterZ_smul (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) : iterZ α lam E n (Complex.exp (2 * Real.pi * Complex.I * x)) = ((Complex.exp (2 * Real.pi * Complex.I * x)) ^ n * (omega α) ^ (n * (n - 1) / 2)) • iterC α lam E n x := by
  -- at `z = e^{2πix}`, the `j`-th rescaled factor is `z ω^j • tmC lam E (x + jα)`
  have hfac : ∀ j : ℕ,
      tmZ lam E (Complex.exp (2 * Real.pi * Complex.I * x) * omega α ^ j)
        = (Complex.exp (2 * Real.pi * Complex.I * x) * omega α ^ j)
          • tmC lam E (x + (j : ℝ) * α) := by
    intro j
    rw [exp_mul_omega_pow]
    convert tmZ_smul lam E (x + (j : ℝ) * α) using 2 <;> (congr 1; push_cast; ring)
  rw [iterZ_eq_matProd]
  simp only [hfac]
  -- pull the scalars `z ω^j` out of the ordered product and multiply them
  rw [matProd_smul (fun j => Complex.exp (2 * Real.pi * Complex.I * x) * omega α ^ j)
        (fun j => tmC lam E (x + (j : ℝ) * α)) n,
      prod_range_exp_omega α x n, ← iterC_eq_matProd]

end Work.TMC7Core.Trig
