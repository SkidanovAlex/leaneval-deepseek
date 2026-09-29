/-
# The differential equation of `Fser`

`Fser = Σ_n C(2n,n)·yⁿ/((2n-1)·16ⁿ) = -√(1 - y/4)`, so it satisfies

`2·(4 - y)·Fser' + Fser = 0`.

We prove this coefficientwise. Writing `aₙ = C(2n,n)/((2n-1)·16ⁿ)` the two
coefficient identities

* `(2n-1)·aₙ = C(2n,n)/16ⁿ`,
* `8(n+1)·aₙ₊₁ = C(2n,n)/16ⁿ`

(the second one being the central-binomial recurrence `(n+1)·C(2n+2,n+1) = 2(2n+1)·C(2n,n)`)
give the recurrence `8(n+1)·aₙ₊₁ = (2n-1)·aₙ`, which is exactly the ODE.
-/
import Mathlib
import Submission.Work.Pure.b4_aux

namespace Work.Pure

open PowerSeries

noncomputable section

/-- The explicit coefficient sequence of `Fser`: `aₙ = C(2n,n)/((2n-1)·16ⁿ)`. -/
def FserCoeff (n : ℕ) : ℚ := (Nat.centralBinom n : ℚ) / ((2 * (n : ℚ) - 1) * 16 ^ n)

lemma coeff_Fser_eq_FserCoeff (n : ℕ) : PowerSeries.coeff n Fser = FserCoeff n := by
  simp [Fser, FserCoeff]

lemma two_mul_natCast_sub_one_ne_zero (n : ℕ) : (2 * (n : ℚ) - 1) ≠ 0 := by
  intro h
  have h2 : (2 * (n : ℚ)) = 1 := by linarith
  have h3 : (((2 * n : ℕ)) : ℚ) = 1 := by push_cast; linarith
  have : (2 * n : ℕ) = 1 := by exact_mod_cast h3
  omega

/-- `(2n-1)·aₙ = C(2n,n)/16ⁿ`. -/
lemma FserCoeff_mul_denom (n : ℕ) :
    (2 * (n : ℚ) - 1) * FserCoeff n = (Nat.centralBinom n : ℚ) / 16 ^ n := by
  unfold FserCoeff
  rw [← mul_div_assoc, mul_div_mul_left _ _ (two_mul_natCast_sub_one_ne_zero n)]

/-- `8(n+1)·aₙ₊₁ = C(2n,n)/16ⁿ`, from the central-binomial recurrence. -/
lemma FserCoeff_succ_mul (n : ℕ) :
    8 * ((n : ℚ) + 1) * FserCoeff (n + 1) = (Nat.centralBinom n : ℚ) / 16 ^ n := by
  have h2n : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
  have hnat : ((n : ℚ) + 1) * (Nat.centralBinom (n + 1) : ℚ)
      = 2 * (2 * (n : ℚ) + 1) * (Nat.centralBinom n : ℚ) := by
    have := Nat.succ_mul_centralBinom_succ n
    have h := congrArg (fun m : ℕ => (m : ℚ)) this
    push_cast at h
    linarith [h]
  unfold FserCoeff
  rw [show (2 * ((n + 1 : ℕ) : ℚ) - 1) = 2 * (n : ℚ) + 1 from by push_cast; ring]
  rw [show (16 : ℚ) ^ (n + 1) = 16 ^ n * 16 from by rw [pow_succ]]
  rw [← mul_div_assoc]
  rw [show 8 * ((n : ℚ) + 1) * (Nat.centralBinom (n + 1) : ℚ)
        = 8 * (((n : ℚ) + 1) * (Nat.centralBinom (n + 1) : ℚ)) by ring, hnat]
  rw [show 8 * (2 * (2 * (n : ℚ) + 1) * (Nat.centralBinom n : ℚ))
        = (2 * (n : ℚ) + 1) * (16 * (Nat.centralBinom n : ℚ)) by ring]
  rw [mul_div_mul_left _ _ h2n]
  rw [show (16 : ℚ) * (Nat.centralBinom n : ℚ) / (16 ^ n * 16)
        = (16 * (Nat.centralBinom n : ℚ)) / (16 * 16 ^ n) by ring]
  rw [mul_div_mul_left _ _ (by norm_num : (16 : ℚ) ≠ 0)]

/-- The coefficient recurrence of `Fser`: `8(n+1)·aₙ₊₁ = (2n-1)·aₙ`. -/
lemma FserCoeff_recur (n : ℕ) :
    8 * ((n : ℚ) + 1) * FserCoeff (n + 1) = (2 * (n : ℚ) - 1) * FserCoeff n := by
  rw [FserCoeff_succ_mul, FserCoeff_mul_denom]

/-- Coefficient of `y·Fser'`. -/
lemma coeff_X_derivative_Fser (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ) Fser))
      = (n : ℚ) * PowerSeries.coeff n Fser := by
  rcases n with _ | m
  · rw [show (PowerSeries.X : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Fser
          = PowerSeries.X ^ 1 * PowerSeries.derivative (R := ℚ) Fser by rw [pow_one]]
    rw [PowerSeries.coeff_X_pow_mul']
    norm_num
  · rw [show (PowerSeries.X : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Fser
          = PowerSeries.X ^ 1 * PowerSeries.derivative (R := ℚ) Fser by rw [pow_one]]
    rw [PowerSeries.coeff_X_pow_mul']
    simp only [le_add_self, ↓reduceIte, Nat.add_sub_cancel]
    rw [PowerSeries.coeff_derivative]
    push_cast
    ring

/-- Coefficient of `(4 - y)·Fser'`. -/
lemma coeff_sub_X_derivative_Fser (n : ℕ) :
    PowerSeries.coeff n ((4 - (PowerSeries.X : PowerSeries ℚ)) * (PowerSeries.derivative (R := ℚ) Fser))
      = 4 * (PowerSeries.coeff (n + 1) Fser * ((n : ℚ) + 1))
          - (n : ℚ) * PowerSeries.coeff n Fser := by
  rw [show (4 : PowerSeries ℚ) - PowerSeries.X = PowerSeries.C 4 - PowerSeries.X from rfl]
  rw [sub_mul, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_derivative,
    coeff_X_derivative_Fser]

theorem b4_Fser_ode : 2 * (4 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) Work.Pure.Fser + Work.Pure.Fser = 0 := by
  ext n
  have h2 : PowerSeries.coeff n
        (2 * (4 - (PowerSeries.X : PowerSeries ℚ)) * (PowerSeries.derivative (R := ℚ) Fser))
      = 2 * (4 * (PowerSeries.coeff (n + 1) Fser * ((n : ℚ) + 1))
          - (n : ℚ) * PowerSeries.coeff n Fser) := by
    rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, mul_assoc,
      PowerSeries.coeff_C_mul, coeff_sub_X_derivative_Fser]
  rw [map_add, map_zero, h2, coeff_Fser_eq_FserCoeff, coeff_Fser_eq_FserCoeff]
  have hrec := FserCoeff_recur n
  linear_combination hrec

end

end Work.Pure
