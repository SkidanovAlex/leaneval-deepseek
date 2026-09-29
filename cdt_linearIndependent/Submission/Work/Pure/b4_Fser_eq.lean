/-
# The relation `4·Fser = -(4 - y)·W` for the pure function `B₄`

Calegari--Dimitrov--Tang, arXiv:2408.15403, Section "Pure functions".
With the auxiliary series

* `Fser = Σₙ C(2n,n)·yⁿ/((2n-1)·16ⁿ) = -√(1 - y/4)`   (`Submission.Work.Pure.b4_aux`),
* `W    = Σₙ C(2n,n)·yⁿ/16ⁿ       = (1 - y/4)^{-1/2}`  (`Submission.Work.Pure.b4_W_sq`),

the two are related by the polynomial identity

`4·Fser = -(4 - y)·W`,

which is exactly the statement of `Work.Pure.b4_Fser_eq`.  (Indeed with `y = 4z`,
`Fser = -√(1-z)`, `W = (1-z)^{-1/2}` and `4 - y = 4(1-z)`, so
`(4-y)·W = 4(1-z)(1-z)^{-1/2} = 4(1-z)^{1/2} = -4·Fser`.)

The proof is a direct coefficient comparison; the only arithmetic input is the
central-binomial recurrence `(n+1)·C(2n+2,n+1) = 2(2n+1)·C(2n,n)`
(`Nat.succ_mul_centralBinom_succ`).

The series `W` is imported from `Submission.Work.Pure.b4_W_sq` (it is a shared
notion, re-declared nowhere here) so that the two sibling modules agree on the
*same* constant `Work.Pure.W`.
-/
import Mathlib
import Submission.Work.Pure.b4_aux
import Submission.Work.Pure.b4_W_sq

namespace Work.Pure

open PowerSeries

noncomputable section

/-- The unit `4` of `ℚ[y]` is the image of the unit `4` of `ℚ`. -/
private lemma four_eq_C : (4 : PowerSeries ℚ) = PowerSeries.C (4 : ℚ) := by
  rw [PowerSeries.C_eq_algebraMap]
  exact (map_ofNat (algebraMap ℚ (PowerSeries ℚ)) 4).symm

/-- Coefficient of `X * f`. -/
private lemma coeff_X_mul' (n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff n ((X : PowerSeries ℚ) * f)
      = if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 n

/-- Coefficients of `W`. -/
private lemma coeff_W_eq (n : ℕ) :
    PowerSeries.coeff n W = (Nat.centralBinom n : ℚ) / 16 ^ n := by
  simp [W]

/-- Central-binomial recurrence in the form needed for the coefficient match:
`C(2m+2,m+1)·(2m+2) = 4·C(2m,m)·(2m+1)`. -/
private lemma centralBinom_key (m : ℕ) :
    (Nat.centralBinom (m + 1) : ℚ) * (2 * (m : ℚ) + 2)
      = 4 * (Nat.centralBinom m : ℚ) * (2 * (m : ℚ) + 1) := by
  have h := Nat.succ_mul_centralBinom_succ m
  have hq : ((m : ℚ) + 1) * (Nat.centralBinom (m + 1) : ℚ)
      = 2 * (2 * (m : ℚ) + 1) * (Nat.centralBinom m : ℚ) := by
    have hc := congrArg (fun x : ℕ => (x : ℚ)) h
    push_cast at hc
    exact hc
  nlinarith [hq]

theorem b4_Fser_eq : 4 * Work.Pure.Fser = -(4 - PowerSeries.X) * Work.Pure.W := by
  apply PowerSeries.ext
  intro n
  have hF : PowerSeries.coeff n (4 * Fser)
      = 4 * ((Nat.centralBinom n : ℚ) / ((2 * (n : ℚ) - 1) * 16 ^ n)) := by
    rw [four_eq_C, PowerSeries.coeff_C_mul, coeff_Fser]
  have hW : PowerSeries.coeff n (-(4 - (X : PowerSeries ℚ)) * W)
      = (if 1 ≤ n then (Nat.centralBinom (n - 1) : ℚ) / 16 ^ (n - 1) else 0)
        - 4 * ((Nat.centralBinom n : ℚ) / 16 ^ n) := by
    rw [show (-(4 - (X : PowerSeries ℚ)) * W)
          = (X : PowerSeries ℚ) * W - (4 : PowerSeries ℚ) * W by ring]
    rw [map_sub, coeff_X_mul', four_eq_C, PowerSeries.coeff_C_mul, coeff_W_eq, coeff_W_eq]
  rw [hF, hW]
  rcases n with _ | k
  · rw [if_neg (by norm_num : ¬ (1 : ℕ) ≤ 0)]
    norm_num [Nat.centralBinom]
  · rw [if_pos (by omega : (1 : ℕ) ≤ k + 1)]
    rw [show k + 1 - 1 = k by omega]
    have hk := centralBinom_key k
    have h16 : (16 : ℚ) ^ (k + 1) = 16 * 16 ^ k := by ring
    have hnum : (2 * ((k + 1 : ℕ) : ℚ) - 1) = 2 * (k : ℚ) + 1 := by push_cast; ring
    rw [hnum, h16]
    have h16k : (16 : ℚ) ^ k ≠ 0 := by positivity
    have hden : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    nlinarith [hk]

end

end Work.Pure
