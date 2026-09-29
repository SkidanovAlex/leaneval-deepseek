/-
# Auxiliary series `Fser`, `fG` for the product formula of `B₄`

Calegari--Dimitrov--Tang, arXiv:2408.15403, Section "Pure functions".  The
double-binomial coefficient of the pure function `B₄`

`B₄ = 4 Σ_{n≥0} y^{n+1}/16ⁿ Σ_k C(2k,k)·C(2n-2k,n-k)/((2k-1)(2n-2k+1)²)`

is the `k`-convolution (Cauchy product) of the two series

* `Fser = Σ_n C(2n,n) yⁿ/((2n-1)·16ⁿ) = -√(1-y/4)`,
* `fG   = Σ_n C(2n,n) yⁿ/((2n+1)²·16ⁿ)`,

so that `B₄ = 4·y·Fser·fG` (this is the statement `Work.Pure.b4_eq_prod`).

Both series are entire in `y` (radius `4`), with rational coefficients.
-/
import Mathlib

namespace Work.Pure

open PowerSeries

noncomputable section

/-- `Fser = Σ_n C(2n,n)·yⁿ/((2n-1)·16ⁿ) = -√(1 - y/4)`. -/
def Fser : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.centralBinom n : ℚ) / ((2 * (n : ℚ) - 1) * 16 ^ n)

/-- `fG = Σ_n C(2n,n)·yⁿ/((2n+1)²·16ⁿ)`. -/
def fG : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.centralBinom n : ℚ) / ((2 * (n : ℚ) + 1) ^ 2 * 16 ^ n)

@[simp] lemma coeff_Fser (n : ℕ) :
    PowerSeries.coeff n Fser = (Nat.centralBinom n : ℚ) / ((2 * (n : ℚ) - 1) * 16 ^ n) := by
  simp [Fser]

@[simp] lemma coeff_fG (n : ℕ) :
    PowerSeries.coeff n fG = (Nat.centralBinom n : ℚ) / ((2 * (n : ℚ) + 1) ^ 2 * 16 ^ n) := by
  simp [fG]

end

end Work.Pure
