import Mathlib
import Submission.Work.DFT.dftDefs

namespace Work.DFT

/-- The mixed-radix digits of `r + ts.prod * q` (with `r < ts.prod`, `q < t`) are `q` followed
by the digits of `r`. -/
theorem digits_cons_prod (t : ℕ) (ts : List ℕ) (hT : 0 < ts.prod) (q r : ℕ)
    (hq : q < t) (hr : r < ts.prod) :
    HvdH.digits (t :: ts) (r + ts.prod * q) = q :: HvdH.digits ts r := by
  rw [HvdH.digits]
  have hdiv : (r + ts.prod * q) / ts.prod = q := by
    rw [Nat.mul_comm ts.prod q, Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt hr, Nat.zero_add]
  have hmod : (r + ts.prod * q) % ts.prod = r := by
    rw [Nat.mul_comm ts.prod q, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  rw [hdiv, hmod, Nat.mod_eq_of_lt hq]

theorem charExpSplit (t : ℕ) (ts : List ℕ) (hT : 0 < ts.prod) (c₀ : ℤ) (cs : List ℤ)
    (q r : ℕ) (hq : q < t) (hr : r < ts.prod) :
    charExp (t :: ts) (c₀ :: cs) (r + ts.prod * q) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((c₀ : ℝ) * (q : ℝ)) / (t : ℝ) : ℝ)) *
        charExp ts cs r := by
  have hdig := digits_cons_prod t ts hT q r hq hr
  simp only [charExp, hdig, myPhase]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end Work.DFT
