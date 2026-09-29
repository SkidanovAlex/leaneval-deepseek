/-
Definitions for the two-sided bound `αⁿ/(n+1) ≤ u_n(b) ≤ αⁿ`
(`α = b + √(b²-1)`) on the Beukers coefficients
`u_n(b) = Submission.CDT.beukersUR b n` (the Legendre-type coefficients with
generating series `(1 - 2bX + X²)^{-1/2}`).

The proof route fixes the two formal power series

* `Sα α = Σ_k c_k αᵏ Xᵏ`  with `c_k = C(2k,k)/4ᵏ`, the series of
  `(1 - αX)^{-1/2}`  (`cR`, `Sα`);
* `U a  = Σ_n u_n(a) Xⁿ`  (`U`),

and proves `U a = Sα α * Sα β` where `α = a + √(a²-1)`, `β = a - √(a²-1)`.
Extracting the coefficient of `Xⁿ` gives
`u_n = Σ_k c_k c_{n-k} αᵏ β^{n-k}`, from which

* `u_n ≤ αⁿ` (every term is `≤ c_k c_{n-k} αⁿ`, and `Σ_k c_k c_{n-k} = 1`),
* `u_n ≥ c_n αⁿ ≥ αⁿ/(n+1)` (the `k = n` term, using `C(2n,n)(n+1) ≥ 4ⁿ`).
-/
import Mathlib
import Submission.CDT.Beukers

open PowerSeries

namespace Work.C17

noncomputable section

/-- `c_k = C(2k,k)/4^k`, the coefficients of `(1-X)^{-1/2}`. -/
def cR (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) / (4 : ℝ) ^ k

/-- the formal series `Σ_k c_k α^k X^k`, i.e. the series of `(1-αX)^{-1/2}`. -/
def Sα (α : ℝ) : PowerSeries ℝ := PowerSeries.mk (fun k => cR k * α ^ k)

/-- the formal series `Σ_n u_n(a) X^n` whose coefficients are the Beukers
coefficients `Submission.CDT.beukersUR a n`. -/
def U (a : ℝ) : PowerSeries ℝ := PowerSeries.mk (Submission.CDT.beukersUR a)

@[simp] lemma coeff_Sα (α : ℝ) (k : ℕ) : PowerSeries.coeff k (Sα α) = cR k * α ^ k := by
  rw [Sα, PowerSeries.coeff_mk]

@[simp] lemma coeff_U (a : ℝ) (n : ℕ) :
    PowerSeries.coeff n (U a) = Submission.CDT.beukersUR a n := by
  rw [U, PowerSeries.coeff_mk]

lemma cR_zero : cR 0 = 1 := by simp [cR]

lemma coefficient_zero_Sα (α : ℝ) : PowerSeries.constantCoeff (Sα α) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Sα]
  simp [cR]

lemma coefficient_zero_U (a : ℝ) : PowerSeries.constantCoeff (U a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_U]
  simp [Submission.CDT.beukersUR_zero]

end

end Work.C17
