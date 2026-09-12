import Mathlib
import Submission.Core.FaAnalytic

/-!
# F1: `f_a` pointwise norm on the circle

(F1 of Plan.md DESIGN NOTE 6.)  For circle points `z_j`, weights
`p_j ≥ 0` with `∑p_j = n ≥ 1`, and `a ≥ 0`, define (as in the KL proof,
Fedja's auxiliary function; complex powers via the principal branch)

    f_a(w) := a · ∏_j (1 + w·conj z_j)^{p_j},     ‖w‖ = 1, w ≠ -z_j.

This module proves the POINTWISE NORM IDENTITY on the circle:

    ‖f_a(w)‖ = a · ∏_j ‖w + z_j‖^{p_j}          (w on the circle, w ≠ -z_j)

i.e. `f_a`'s modulus is `a` times the Konyagin-Lev distance product with
the points `-z_j`-shifted to `w + z_j` (equivalently the product at `-w`).
This is the identity that turns the margin hypothesis (`‖f_a‖ ≤ a·M < 2`)
into the `‖f‖ ≤ c`, `c < 2` hypothesis of `Submission.Core.D3.per_arc_bound`.

Mathlib hints: `Complex.norm_cpow_real` (‖x^y‖ = ‖x‖^y for real exponents),
`Complex.mul_conj`/`norm_conj` (conjugation), `norm_mul`, `norm_prod`
(product of moduli), `norm_one_add_mul_conj`-style identities
(`‖1 + w·conj z‖ = ‖w + z‖` for `‖z‖ = ‖w‖ = 1`, proved via
`conj z * z = 1`).
-/

noncomputable section

open scoped Real Complex
open Complex

namespace Submission.Core

/-- The modulus of a real power is the power of the modulus. -/
lemma norm_cPow (w : ℂ) (p : ℝ) : ‖cPow w p‖ = ‖w‖ ^ p := by
  dsimp [cPow]
  rw [Complex.norm_cpow_real]


/-- For `‖z‖ = ‖w‖ = 1`: `‖1 + w·conj z‖ = ‖w + z‖`. -/
lemma norm_one_add_mul_conj {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖(1 : ℂ) + w * starRingEnd ℂ z‖ = ‖w + z‖ := by
  -- conj z * (z + w) = 1 + conj z * w = 1 + w * conj z  (commutative), and
  -- ‖conj z‖ = 1.
  have hz' : ‖starRingEnd ℂ z‖ = 1 := by
    rw [Complex.norm_conj, hz]
  -- conj z * z = ‖z‖² = 1
  have hzz : starRingEnd ℂ z * z = 1 := by
    have h := Complex.mul_conj z
    -- z * conj z = ↑(normSq z); commute and use ‖z‖ = 1
    rw [mul_comm] at h
    have hns : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hz, one_pow]
    simpa [hns] using h
  calc
    ‖(1 : ℂ) + w * starRingEnd ℂ z‖ = ‖starRingEnd ℂ z * (z + w)‖ := by
        congr 1
        rw [mul_add, hzz]
        ring
    _ = ‖starRingEnd ℂ z‖ * ‖z + w‖ := by rw [norm_mul]
    _ = ‖w + z‖ := by
        rw [hz']
        simp
        rw [add_comm]

/-- **F1 (pointwise norm on the circle).**  For circle points `z_j`, real
`a ≥ 0`, and unit `w` avoiding the antipodes `-z_j`:
`‖f_a(w)‖ = a · ∏_j ‖w + z_j‖^{p_j}`. -/
theorem fa_norm_on_circle (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (z : Fin n → ℂ)
    (p : Fin n → ℝ) (hz : ∀ j : Fin n, ‖z j‖ = 1) {w : ℂ} (hw : ‖w‖ = 1)
    (hne : ∀ j : Fin n, w ≠ -z j) :
    ‖fa n a z p w‖ = a * ∏ j : Fin n, ‖w + z j‖ ^ p j := by
  calc
    ‖fa n a z p w‖ = ‖(a : ℂ) * ∏ j : Fin n, cPow (1 + w * starRingEnd ℂ (z j)) (p j)‖ := rfl
    _ = ‖(a : ℂ)‖ * ‖∏ j : Fin n, cPow (1 + w * starRingEnd ℂ (z j)) (p j)‖ := by
        rw [norm_mul]
    _ = a * ‖∏ j : Fin n, cPow (1 + w * starRingEnd ℂ (z j)) (p j)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    _ = a * ∏ j : Fin n, ‖cPow (1 + w * starRingEnd ℂ (z j)) (p j)‖ := by
        rw [norm_prod]
    _ = a * ∏ j : Fin n, ‖1 + w * starRingEnd ℂ (z j)‖ ^ p j := by
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        rw [norm_cPow]
    _ = a * ∏ j : Fin n, ‖w + z j‖ ^ p j := by
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        rw [norm_one_add_mul_conj (hz j) hw]

end Submission.Core

end
