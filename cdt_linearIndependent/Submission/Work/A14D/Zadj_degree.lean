import Mathlib
import Submission.Work.A14D.Zadj_defs
import Submission.Commons.Algebra.Polynomial.coeff_mul_natDegree_le
import Submission.Work.A14D.deriv_mul_le_prod
import Submission.Work.A14D.deriv2_mul_le_prod

/-!
# Degree and leading coefficient of the cleared adjoint numerator `PhiNumZ`

`PhiNumZ W = DZ³·(LZf (W/DZ))` is the cleared numerator of the self-adjoint operator
`P₂β'' + P₁β' + P₀β` for `β = W/DZ`, where

* `P₂ = x − 10x² + 9x³ = x(1−x)(1−9x)`, `P₁ = 1 − 20x + 27x²`, `P₀ = −3 + 9x`,
* `DZ = x²(x−1)`.

It is `ℂ`-linear in `W`: collecting the coefficients of `W`, `W'` and `W''` gives

`PhiNumZ W = W·PhiUZ + W'·PhiVZ + W''·PhiWZ`

with the universal (`W`-independent) polynomials

* `PhiUZ = P₂·(2·DZ'² − DZ·DZ'') − P₁·DZ'·DZ + P₀·DZ²`  (`natDegree ≤ 7`, `coeff 7 = 36`),
* `PhiVZ = −2·P₂·DZ·DZ' + P₁·DZ²`                        (`natDegree ≤ 8`, `coeff 8 = −27`),
* `PhiWZ = P₂·DZ²`                                       (`natDegree ≤ 9`, `coeff 9 = 9`).

Since `W` has degree `n`, the three summands have degree at most `n + 7` and contribute to the
top coefficient `lc W·(36 + n·(−27) + n(n−1)·9) = lc W·9(n−2)²`.  This is the statement of
`Zadj_degree`, needed by `Zadj_wbound` (`W.natDegree ≤ 2`) and hence by
`adjointZ_no_solution`.
-/

open Polynomial

noncomputable section

namespace Work.A14D

/-- `DZ' = (x²(x−1))' = 3x² − 2x`. -/
def DZ1 : Polynomial ℂ := 3 * X ^ 2 - 2 * X

/-- `DZ'' = 6x − 2`. -/
def DZ2 : Polynomial ℂ := 6 * X - 2

/-- The `W`-coefficient of the cleared numerator:
`P₂·(2·DZ'² − DZ·DZ'') − P₁·DZ'·DZ + P₀·DZ²`. -/
def PhiUZ : Polynomial ℂ :=
  P2Z * (2 * DZ1 ^ 2 - DZ * DZ2) - P1Z * DZ1 * DZ + P0Z * DZ ^ 2

/-- The `W'`-coefficient of the cleared numerator: `−2·P₂·DZ·DZ' + P₁·DZ²`. -/
def PhiVZ : Polynomial ℂ := -2 * P2Z * DZ * DZ1 + P1Z * DZ ^ 2

/-- The `W''`-coefficient of the cleared numerator: `P₂·DZ²`. -/
def PhiWZ : Polynomial ℂ := P2Z * DZ ^ 2

lemma DZ_deriv : DZ.derivative = DZ1 := by
  unfold DZ DZ1
  simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.C_eq_natCast]
  ring_nf

lemma DZ1_deriv : DZ1.derivative = DZ2 := by
  unfold DZ1 DZ2
  simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_sub, Polynomial.derivative_ofNat, Polynomial.C_eq_natCast]
  ring_nf

lemma DZ_deriv2 : DZ.derivative.derivative = DZ2 := by
  rw [DZ_deriv, DZ1_deriv]

/-- `PhiNumZ` collects into the three coefficient polynomials `PhiUZ, PhiVZ, PhiWZ`. -/
lemma PhiNumZ_eq (W : Polynomial ℂ) :
    PhiNumZ W = W * PhiUZ + W.derivative * PhiVZ + W.derivative.derivative * PhiWZ := by
  unfold PhiNumZ PhiUZ PhiVZ PhiWZ
  rw [DZ_deriv2, DZ_deriv]
  ring

/-- Top-degree data of `PhiUZ = 36x⁷ − 90x⁶ + 84x⁵ − 34x⁴ + 4x³`. -/
lemma PhiUZ_facts : PhiUZ.natDegree ≤ 7 ∧ PhiUZ.coeff 7 = 36 := by
  constructor <;> (unfold PhiUZ P2Z P1Z P0Z DZ DZ1 DZ2; compute_degree!)

/-- Top-degree data of `PhiVZ = −27x⁸ + 76x⁷ − 74x⁶ + 28x⁵ − 3x⁴`. -/
lemma PhiVZ_facts : PhiVZ.natDegree ≤ 8 ∧ PhiVZ.coeff 8 = -27 := by
  constructor <;> (unfold PhiVZ P2Z P1Z DZ DZ1; compute_degree!)

/-- Top-degree data of `PhiWZ = 9x⁹ − 28x⁸ + 30x⁷ − 12x⁶ + x⁵`. -/
lemma PhiWZ_facts : PhiWZ.natDegree ≤ 9 ∧ PhiWZ.coeff 9 = 9 := by
  constructor <;> (unfold PhiWZ P2Z DZ; compute_degree!)

theorem Zadj_degree (W : Polynomial ℂ) (hW : W ≠ 0) :
    (PhiNumZ W).natDegree ≤ W.natDegree + 7 ∧
      (PhiNumZ W).coeff (W.natDegree + 7)
        = 9 * W.leadingCoeff * ((W.natDegree : ℂ) - 2) ^ 2 := by
  obtain ⟨hUnd, hUc⟩ := PhiUZ_facts
  obtain ⟨hVnd, hVc⟩ := PhiVZ_facts
  obtain ⟨hWnd, hWc⟩ := PhiWZ_facts
  obtain ⟨h1nd, h1c⟩ := deriv_mul_le_prod W PhiVZ 7 hVnd
  obtain ⟨h2nd, h2c⟩ := deriv2_mul_le_prod W PhiWZ 7 hWnd
  rw [PhiNumZ_eq W]
  -- degree bound
  have hd1 : (W * PhiUZ).natDegree ≤ W.natDegree + 7 := by
    calc (W * PhiUZ).natDegree ≤ W.natDegree + PhiUZ.natDegree := natDegree_mul_le
      _ ≤ W.natDegree + 7 := by omega
  have hd2 : (W.derivative * PhiVZ).natDegree ≤ W.natDegree + 7 := h1nd
  have hd3 : (W.derivative.derivative * PhiWZ).natDegree ≤ W.natDegree + 7 := h2nd
  constructor
  · calc (W * PhiUZ + W.derivative * PhiVZ + W.derivative.derivative * PhiWZ).natDegree
        ≤ max (W * PhiUZ + W.derivative * PhiVZ).natDegree
            (W.derivative.derivative * PhiWZ).natDegree := natDegree_add_le _ _
      _ ≤ W.natDegree + 7 :=
          max_le (le_trans (natDegree_add_le _ _) (max_le hd1 hd2)) hd3
  · rw [coeff_add, coeff_add,
      Commons.Algebra.Polynomial.coeff_mul_natDegree_le W PhiUZ W.natDegree 7 le_rfl hUnd,
      hUc, h1c, hVc, h2c, hWc, coeff_natDegree]
    ring

end Work.A14D
