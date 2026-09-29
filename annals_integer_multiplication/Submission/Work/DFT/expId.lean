import Mathlib
import Submission.Work.DFT.phaseLin

set_option autoImplicit false

open scoped BigOperators

namespace Work.DFT

/-! The exponential identities rewriting products of `dftExp` factors as single `charExp`
factors (the hypothesis needed to apply the orthogonality facts). -/

theorem dftExp_mul_charSub (ts : List ℕ) (j a k : Fin ts.prod) :
    dftExp ts 1 j k * dftExp ts (-1) k a
      = charExp ts (subN (HvdH.digits ts j) (HvdH.digits ts a)) k := by
  have h := phase_sub ts (HvdH.digits ts j) (HvdH.digits ts k) (HvdH.digits ts a)
    (digits_length ts j) (digits_length ts a) (digits_length ts k)
  unfold dftExp charExp
  rw [← Complex.exp_add]
  congr 1
  rw [← h, Complex.ofReal_sub]
  ring

theorem dftExp_mul_charConv (ts : List ℕ) (j a b k : Fin ts.prod) :
    dftExp ts 1 j k * dftExp ts (-1) k a * dftExp ts (-1) k b
      = charExp ts (subNZ (subN (HvdH.digits ts j) (HvdH.digits ts a))
          (HvdH.digits ts b)) k := by
  have h := phase_sub3 ts (HvdH.digits ts j) (HvdH.digits ts k) (HvdH.digits ts a)
    (HvdH.digits ts b) (digits_length ts j) (digits_length ts a)
    (digits_length ts k) (digits_length ts b)
  unfold dftExp charExp
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [← h, Complex.ofReal_sub, Complex.ofReal_sub]
  ring

/-- Unfolding `dftMulti` into a sum of `dftExp` factors. -/
theorem dftMulti_apply (ts : List ℕ) (sgn : ℤ) (u : Fin ts.prod → ℂ) (j : Fin ts.prod) :
    HvdH.dftMulti ts sgn u j
      = (1 / (ts.prod : ℂ)) * ∑ k : Fin ts.prod, dftExp ts sgn j k * u k := by
  simp only [HvdH.dftMulti, dftExp]

end Work.DFT
