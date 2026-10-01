import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.critN_content_iff

namespace Work.LinnikBurgess

open Polynomial

/-- If an integer `c` divides every coefficient of an integral polynomial `P`, then it divides every
value of `P` at an integer. -/
lemma dvd_eval_of_dvd_coeff {c : ℤ} {P : Polynomial ℤ} (h : ∀ n, c ∣ P.coeff n) (x : ℤ) :
    c ∣ P.eval x := by
  obtain ⟨Q, hQ⟩ := (Polynomial.C_dvd_iff_dvd_coeff c P).mpr h
  rw [hQ, Polynomial.eval_mul, Polynomial.eval_C]
  exact dvd_mul_right c _

/-- If an integer `c` divides every coefficient of an integral polynomial `P`, then it divides every
coefficient of the derivative of `P`. -/
lemma dvd_coeff_derivative {c : ℤ} {P : Polynomial ℤ} (h : ∀ n, c ∣ P.coeff n) :
    ∀ n, c ∣ (Polynomial.derivative P).coeff n := by
  intro n
  rw [Polynomial.coeff_derivative]
  exact dvd_mul_of_dvd_left (h (n + 1)) _

/-- If `J` is the `p`-adic valuation of the content `contAB a b` and `y` is a unit at `p`, then every
level `j ≤ min J e` is doubly critical: `DLp p j a b`.

Hints: `j ≤ J` gives `p^j ∣ contAB a b`; `critN_content_iff` turns this into the coefficient-wise
divisibility `p^j ∣ (critN a b).coeff n` for all `n`, which passes to the evaluations
`p^j ∣ N(y)` and `p^j ∣ N'(y)` (each is a finite sum of multiples of `p^j`).  Witness: `y`. -/
theorem DLp_of_content {p e J : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (a b : Fin 3 → ℕ) {y : ℕ} (hy : UnitAt p y a b) (hc : contAB a b ≠ 0)
    (hJ : padicValNat p (contAB a b) = J) :
    ∀ j : ℕ, j ≤ J → j ≤ e → DLp p j a b := by
  intro j hjJ _
  have hle : j ≤ padicValNat p (contAB a b) := by rw [hJ]; exact hjJ
  have hpdvd : p ^ j ∣ contAB a b := (padicValNat_dvd_iff_le hc).mpr hle
  have hcoeff : ∀ n, (((p ^ j : ℕ)) : ℤ) ∣ (critN a b).coeff n :=
    (critN_content_iff hp5 a b).mpr hpdvd
  exact ⟨y, hy, dvd_eval_of_dvd_coeff hcoeff (y : ℤ),
    dvd_eval_of_dvd_coeff (dvd_coeff_derivative hcoeff) (y : ℤ)⟩

end Work.LinnikBurgess
