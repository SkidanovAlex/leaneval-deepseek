import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Trig
import Submission.Work.TMC7Core.Trig.tmZ_smul

/-!
# `frobSq` and the algebraic cocycle `iterZ`

At `z = e^{2πix}` the algebraic transfer matrix satisfies `tmZ lam E z = z • tmC lam E x`
(lemma `tmZ_smul`).  Consequently the ordered product `iterZ α lam E n z` differs from
`z^n A_n(x)` only by a unit-modulus scalar, so every entry of `iterZ α lam E n (e^{2πix})`
has the same modulus as the corresponding entry of `A_n(x) = iterC α lam E n x`, and the
two matrices have the same squared Frobenius norm:

`frobSq α lam E n x = ∑ i j, ‖iterZ α lam E n (e^{2πix}) i j‖ ^ 2`.

Only the *moduli* of the entries are used, so instead of the closed form
`z^n ω^{n(n-1)/2}` we accumulate the scalar `iterZScale α z n = ∏_{k<n} z ω^k`, whose
modulus is one because `‖z‖ = 1` and `‖ω‖ = 1`.
-/

namespace Work.TMC7Core.Trig

open Work.TMC7Core

noncomputable section

/-- The scalar `∏_{k<n} (z ω^k)`, in the order in which the factors of `iterZ` are
multiplied. -/
private def iterZScale (α : ℝ) (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (z * omega α ^ n) * iterZScale α z n

/-- `‖e^{2πix}‖ = 1`. -/
private lemma norm_exp_two_pi_I_mul (x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * x)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- `‖ω‖ = 1`. -/
private lemma norm_omega (α : ℝ) : ‖omega α‖ = 1 := by
  rw [omega, Complex.norm_exp]
  simp [Complex.mul_re]

/-- `e^{2πix} ω^n = e^{2πi(x+nα)}`. -/
private lemma exp_mul_omega_pow (α x : ℝ) (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * x) * omega α ^ n
      = Complex.exp (2 * Real.pi * Complex.I * ((x + (n : ℝ) * α : ℝ) : ℂ)) := by
  rw [omega, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- On the unit circle `iterZ` equals `iterC` up to the unit-modulus scalar `iterZScale`. -/
private lemma iterZ_eq_smul (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    iterZ α lam E n (Complex.exp (2 * Real.pi * Complex.I * x))
      = iterZScale α (Complex.exp (2 * Real.pi * Complex.I * x)) n • iterC α lam E n x := by
  induction n with
  | zero => simp [iterZ, iterC, iterZScale]
  | succ n ih =>
    rw [iterZ, ih, iterZScale, exp_mul_omega_pow α x n]
    rw [tmZ_smul]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← iterC_succ]

/-- The scalar `iterZScale α z n` has modulus one when `‖z‖ = 1`. -/
private lemma norm_iterZScale (α : ℝ) (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖iterZScale α z n‖ = 1 := by
  induction n with
  | zero => simp [iterZScale]
  | succ n ih =>
    rw [iterZScale, norm_mul, norm_mul, norm_pow, ih, hz, norm_omega]
    simp

/-- Each entry of `iterZ α lam E n (e^{2πix})` has the same modulus as the corresponding
entry of `iterC α lam E n x`. -/
private lemma norm_iterZ_entry (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) (i j : Fin 2) :
    ‖iterZ α lam E n (Complex.exp (2 * Real.pi * Complex.I * x)) i j‖
      = ‖iterC α lam E n x i j‖ := by
  rw [iterZ_eq_smul, Matrix.smul_apply, norm_smul,
    norm_iterZScale _ _ (norm_exp_two_pi_I_mul x) n, one_mul]

theorem frobSq_eq_iterZ (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) : frobSq α lam E n x = ∑ i : Fin 2, ∑ j : Fin 2, ‖iterZ α lam E n (Complex.exp (2 * Real.pi * Complex.I * x)) i j‖ ^ 2 := by
  rw [frobSq, frob_sq, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [norm_iterZ_entry]
  ring

end

end Work.TMC7Core.Trig
