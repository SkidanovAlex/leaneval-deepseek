import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.DLp_of_content

namespace Work.LinnikBurgess.lfSmall

open Work.LinnikBurgess

/-- A unit point `y` at the prime `3` together with content divisibility `3^h ∣ coeff n` for every
coefficient of the Wronskian `N = critN a b` gives the double-critical level `s` for every `s ≤ h`:
the same `y` is a witness, since `eval` is a finite `ℤ`-linear combination of the coefficients
(and likewise for the derivative, whose coefficients are multiples of those of `N`). -/
theorem DLp_of_content_three {e h s : ℕ} (a b : Fin 3 → ℕ) {y : ℕ} (hy : UnitAt 3 y a b)
    (hcontent : ∀ n : ℕ, ((3 ^ h : ℕ) : ℤ) ∣ (critN a b).coeff n) (hs : s ≤ h) :
    DLp 3 s a b := by
  have hcoeff : ∀ n : ℕ, ((3 ^ s : ℕ) : ℤ) ∣ (critN a b).coeff n := fun n =>
    dvd_trans (Int.natCast_dvd_natCast.mpr (pow_dvd_pow 3 hs)) (hcontent n)
  exact ⟨y, hy, dvd_eval_of_dvd_coeff hcoeff (y : ℤ),
    dvd_eval_of_dvd_coeff (dvd_coeff_derivative hcoeff) (y : ℤ)⟩

end Work.LinnikBurgess.lfSmall
