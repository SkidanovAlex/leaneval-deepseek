import Mathlib
import Submission.Work.FIArea4.WdyadDefs2
import Submission.Work.FIArea4.WdyadSetup
import Submission.Work.FIArea4.WdyadPoisson

namespace Work.FIArea4.Vflip

open scoped FourierTransform BigOperators
open Finset

noncomputable section

/-! ## Elementary facts about `oddPart`, the Jacobi weight and the Gaussian majorant -/

/-- The odd part of `d` divides `d`. -/
lemma oddPart_dvd' (d : ℕ) : Work.FIPlan.oddPart d ∣ d := by
  unfold Work.FIPlan.oddPart
  exact Nat.div_dvd_of_dvd (Nat.ordProj_dvd d 2)

/-- If `oddPart d₁ * oddPart d₂` is a square, the Jacobi symbol `J(r | oddPart d₁ * oddPart d₂)`
is `1` for every `r` coprime to `d₁ d₂`. -/
lemma jacobiSym_oddPart_prod_eq_one (d1 d2 r m : ℕ) (hcop : Nat.Coprime r (d1*d2))
    (hm : Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2 = m^2) :
    jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) = 1 := by
  have hdiv1 : Work.FIPlan.oddPart d1 ∣ d1 := oddPart_dvd' d1
  have hdiv2 : Work.FIPlan.oddPart d2 ∣ d2 := oddPart_dvd' d2
  have hdvd : m^2 ∣ d1 * d2 := by
    rw [← hm]; exact Nat.mul_dvd_mul hdiv1 hdiv2
  have hcop2 : Nat.Coprime r (m^2) := hcop.coprime_dvd_right hdvd
  have hcopm : Nat.Coprime r m := hcop2.coprime_dvd_right (by exact ⟨m, by ring⟩)
  rw [hm, jacobiSym.pow_right]
  exact jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hcopm)

/-- Under the flatness hypothesis the Jacobi weight is just the indicator of coprimality. -/
lemma wChar_eq_ite (d1 d2 : ℕ) (hflat : ∃ m : ℕ, Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2 = m^2)
    (r : ℕ) :
    Work.FIArea4.wChar d1 d2 r = if Nat.Coprime r (d1*d2) then 1 else 0 := by
  unfold Work.FIArea4.wChar
  split_ifs with h
  · rw [jacobiSym_oddPart_prod_eq_one d1 d2 r _ h hflat.choose_spec]; norm_num
  · rfl

/-- The exponential factor `e(2π i r k a / q)` has unit modulus. -/
lemma norm_exp_unit (r a q : ℕ) (k : ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) / (q:ℝ))‖ = 1 := by
  have harg : 2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) / (q:ℝ)
      = ((2 * Real.pi * (r:ℝ) * (k:ℝ) * (a:ℝ) / (q:ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

end

end Work.FIArea4.Vflip
