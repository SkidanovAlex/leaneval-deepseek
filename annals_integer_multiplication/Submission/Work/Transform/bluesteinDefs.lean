import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.DFT.expId
import Submission.Work.DFT.phaseLin

set_option autoImplicit false

namespace Work.Transform

/-!
# The exponential `e^{πi z}` and the Bluestein chirp

`expPi z = e^{πi z}` for a real `z`.  The Bluestein chirp of `Submission.Work.Transform.Defs` is
`chirp ts j = expPi (Σᵢ jᵢ²/tᵢ)` (`phase ts (digits ts j) (digits ts j)`), and working with `expPi`
(rather than with `Complex.exp` applied to a complexified real) makes multiplicativity and
conjugation below plain rewrites.
-/

/-- `e^{πi z}`, for a real `z`. -/
noncomputable def expPi (z : ℝ) : ℂ := Complex.exp (Real.pi * Complex.I * (z : ℂ))

@[simp] lemma expPi_zero : expPi 0 = 1 := by simp [expPi]

lemma expPi_add (z w : ℝ) : expPi (z + w) = expPi z * expPi w := by
  simp only [expPi, Complex.ofReal_add, ← Complex.exp_add]
  congr 1
  ring

/-- `star (e^{πi z}) = e^{πi(-z)}`. -/
lemma star_expPi (z : ℝ) : star (expPi z) = expPi (-z) := by
  rw [expPi,
    show star (Complex.exp (Real.pi * Complex.I * (z : ℂ)))
      = Complex.exp (star (Real.pi * Complex.I * (z : ℂ))) from (Complex.exp_conj _).symm,
    expPi]
  congr 1
  rw [← starRingEnd_apply]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `e^{πi(-z)}` is the conjugate of `e^{πi z}`. -/
lemma expPi_neg (z : ℝ) : expPi (-z) = star (expPi z) := (star_expPi z).symm

lemma expPi_sub (z w : ℝ) : expPi (z - w) = expPi z * star (expPi w) := by
  rw [sub_eq_add_neg, expPi_add, star_expPi]

/-- `e^{πi·2m} = 1` for an integer `m`. -/
lemma expPi_two_mul_int (m : ℤ) : expPi (2 * (m : ℝ)) = 1 := by
  have h : Real.pi * Complex.I * ((2 * (m : ℝ) : ℝ) : ℂ)
      = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [expPi, h, Complex.exp_int_mul_two_pi_mul_I]

/-- `e^{πi z}` only depends on `z` up to multiples of `2`. -/
lemma expPi_eq_of_sub_eq_two_mul (z w : ℝ) (m : ℤ) (h : z - w = 2 * (m : ℝ)) :
    expPi z = expPi w := by
  have hz : z = w + 2 * (m : ℝ) := by linarith
  rw [hz, expPi_add, expPi_two_mul_int, mul_one]

/-- The chirp is `e^{πi·Σᵢ jᵢ²/tᵢ}` in terms of `expPi`. -/
lemma chirp_eq_expPi (ts : List ℕ) (j : ℕ) :
    chirp ts j = expPi (HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts j)) := rfl

/-- The conjugate of the chirp. -/
lemma star_chirp (ts : List ℕ) (j : ℕ) :
    star (chirp ts j) = expPi (-(HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts j))) := by
  rw [chirp_eq_expPi, star_expPi]

/-- `dftExp` as an `expPi`. -/
lemma dftExp_eq_expPi (ts : List ℕ) (sgn : ℤ) (j k : ℕ) :
    Work.DFT.dftExp ts sgn j k
      = expPi ((sgn : ℝ) * (2 * HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts k))) := by
  simp only [Work.DFT.dftExp, expPi]
  congr 1
  push_cast
  ring

end Work.Transform
