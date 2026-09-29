import Mathlib
import Submission.Work.C17adj.divisor_defs

/-!
# The three coefficient polynomials `PhiU, PhiV, PhiZ` of `PhiNum`

`PhiNum a b W` is the cleared numerator of `D³·(P₂β'' + A·β' + C·β)` for `β = W/D`, `D = DadjL`
(see `Work.C17adj.divisor_defs`).  It is `ℂ`-linear in `W`: collecting the coefficients of
`W`, `W'` and `W''` gives

`PhiNum a b W = W * PhiU a b + W.derivative * PhiV a b + W.derivative.derivative * PhiZ a b`

with the universal (i.e. `W`-independent) polynomials

* `PhiU = P₂·(2·D'² − D·D'') − A·D'·D + C·D²`   (`natDegree ≤ 25`, `coeff 25 = 25`),
* `PhiV = −2·P₂·D·D' + A·D²`                     (`natDegree ≤ 26`, `coeff 26 = −9`),
* `PhiZ = P₂·D²`                                 (`natDegree ≤ 27`, `coeff 27 = 1`).

These are the data that turn the degree statement for `PhiNum` into a computation with
coefficient extraction (`coeff_mul_natDegree_le` below).
-/

open Polynomial

namespace Work.C17adj

noncomputable section

/-- The `W`-coefficient of the cleared adjoint numerator: `P₂(2D'² − D D'') − A D' D + C D²`. -/
def PhiU (a b : ℚ) : Polynomial ℂ :=
  P2Cm a b * (2 * DadjL.derivative ^ 2 - DadjL * DadjL.derivative.derivative)
    - AadjL a b * DadjL.derivative * DadjL
    + CadjL a b * DadjL ^ 2

/-- The `W'`-coefficient of the cleared adjoint numerator: `−2 P₂ D D' + A D²`. -/
def PhiV (a b : ℚ) : Polynomial ℂ :=
  -2 * P2Cm a b * DadjL * DadjL.derivative + AadjL a b * DadjL ^ 2

/-- The `W''`-coefficient of the cleared adjoint numerator: `P₂ D²`. -/
def PhiZ (a b : ℚ) : Polynomial ℂ := P2Cm a b * DadjL ^ 2

/-- `PhiNum` collects into the three coefficient polynomials `PhiU, PhiV, PhiZ`. -/
theorem PhiNum_eq (a b : ℚ) (W : Polynomial ℂ) :
    PhiNum a b W = W * PhiU a b + W.derivative * PhiV a b
      + W.derivative.derivative * PhiZ a b := by
  simp only [PhiNum, PhiU, PhiV, PhiZ]
  ring

/-- The top coefficient of a product of two polynomials whose degrees are bounded by `m` and `t`
is the product of their `m`-th and `t`-th coefficients. -/
theorem coeff_mul_natDegree_le (p q : Polynomial ℂ) (m t : ℕ)
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ t) :
    (p * q).coeff (m + t) = p.coeff m * q.coeff t := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single (m, t) ?_ ?_
  · rintro ⟨i, j⟩ hmem hne
    have hsum : i + j = m + t := by simpa using hmem
    change p.coeff i * q.coeff j = 0
    rcases lt_trichotomy i m with hlt | heq | hgt
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show q.natDegree < j by omega), mul_zero]
    · subst heq
      have hjt : j = t := by omega
      exact absurd (by simp [hjt]) hne
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < i by omega), zero_mul]
  · intro hmem
    exact absurd (by simp) hmem

end

end Work.C17adj
