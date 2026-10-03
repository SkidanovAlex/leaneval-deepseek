/-
# `Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaHol_one_div_dual`

The Poisson/Poisson-dual transformation of the **weight-`m` holomorphic** theta series at the single
point `u = 1/x`:

  `thetaHol χ m (1/x) = x^{m+1}·thetaDualMG d χ m x`,   `x > 0`,

in the dual form in which it is consumed by the Mellin-transform (weak functional equation)
argument for the Hecke `L`-function of `ℚ(i)`.  Generalises `R/thetaHol_zero_one_div` (the case
`m = 0`) to every weight `m : ℕ`; the inputs are the twisted Poisson summation for the *odd*
theta series `thetaOdd χ m` (`Work.FIArea5.S16Hecke.thetaOdd_eq_poisson_form`) together with the
elementary relation `thetaOdd χ m = unitSum χ m · thetaHol χ m`.  No primitivity is needed.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.LamRightHalf.Defs
import Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson
import Submission.Work.FIArea5.S16Hecke.thetaOdd_eq_unitSum_mul_thetaHol

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

open Work.FIArea5.S16Hecke

/-- The exponent bookkeeping of the Poisson form at `u = 1/x`: the complex exponent
`-π(ξ₁²+ξ₂²)/((1/x)(4d)²)` is the real number `-π·(ξ₁²+ξ₂²)·x/(16d²)`. -/
private lemma exp_arg_eq (d : ℕ) {x : ℝ} (ξ : ℤ × ℤ) :
    -(Real.pi : ℂ) * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
        (((1 / x : ℝ) : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2))
      = ((-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * (x / (16 * (d : ℝ) ^ 2)))) : ℝ) : ℂ) := by
  rw [show ((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2)
      = ((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) : ℝ) : ℂ) by push_cast; ring]
  rw [show ((((4 * d : ℕ) : ℂ)) ^ 2) = (((16 * (d : ℝ) ^ 2) : ℝ) : ℂ) by push_cast; ring]
  rw [show (((1 / x : ℝ) : ℂ)) = ((x : ℂ))⁻¹ by rw [one_div, Complex.ofReal_inv]]
  rw [← Complex.ofReal_inv]
  push_cast
  field_simp

/-- The Poisson dual form of `thetaOdd_eq_poisson_form` at `u = 1/x`, written with the monomial
`(ξ₁+iξ₂)^m` instead of `((ξ₁+iξ₂)/4d)^m` and with the exponent `x/(16d²)`. -/
private lemma thetaOdd_one_div_x (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaOdd chi m (1 / x)
      = (1 / (((4 * d : ℕ) : ℂ)) ^ 2) * (-Complex.I) ^ m * ((((4 * d : ℕ) : ℂ)) ^ (-(m : ℤ))) *
          ((x : ℂ) ^ (m + 1)) * thetaDualM d chi m (x / (16 * (d : ℝ) ^ 2)) := by
  have hpois := thetaOdd_eq_poisson_form d hd chi hchi m (u := 1 / x) (one_div_pos.mpr hx)
  rw [hpois]
  have hpinv : (((↑(1 / x) : ℂ)) ^ (m + 1))⁻¹ = (x : ℂ) ^ (m + 1) := by
    rw [one_div, Complex.ofReal_inv, inv_pow, inv_inv]
  rw [hpinv]
  have hsum : (∑' ξ : ℤ × ℤ, Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
        (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m *
        Complex.exp (-(Real.pi : ℂ) * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
          (((1 / x : ℝ) : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2))))
      = ((((4 * d : ℕ) : ℂ)) ^ (-(m : ℤ))) * thetaDualM d chi m (x / (16 * (d : ℝ) ^ 2)) := by
    rw [thetaDualM, ← tsum_mul_left]
    refine tsum_congr (fun ξ => ?_)
    have hexp : Complex.exp (-(Real.pi : ℂ) * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
          (((1 / x : ℝ) : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))
        = Complex.exp (((-(Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) *
            (x / (16 * (d : ℝ) ^ 2)))) : ℝ) : ℂ)) := by
      rw [exp_arg_eq d ξ]
    rw [hexp, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_pow, inv_pow]
    ring_nf
  rw [hsum]
  ring

/-- **The dual Poisson transformation of the weight-`m` holomorphic theta series.** -/
theorem thetaHol_one_div_dual_pow (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℕ)
    (hU : unitSum chi m ≠ 0) {x : ℝ} (hx : 0 < x) :
    thetaHol chi m (1 / x) = (x : ℂ) ^ (m + 1) * thetaDualMG d chi m x := by
  have hpois := thetaOdd_one_div_x d hd hchi m hx
  have hunit := thetaOdd_eq_unitSum_mul_thetaHol chi m hchi.1.2.1 (1 / x)
  have hmul : unitSum chi m * thetaHol chi m (1 / x)
      = (1 / (((4 * d : ℕ) : ℂ)) ^ 2) * (-Complex.I) ^ m * ((((4 * d : ℕ) : ℂ)) ^ (-(m : ℤ))) *
          ((x : ℂ) ^ (m + 1)) * thetaDualM d chi m (x / (16 * (d : ℝ) ^ 2)) := by
    rw [← hunit]
    exact hpois
  have h2 : ((unitSum chi m)⁻¹ * (unitSum chi m)) * thetaHol chi m (1 / x)
      = (unitSum chi m)⁻¹ * ((1 / (((4 * d : ℕ) : ℂ)) ^ 2) * (-Complex.I) ^ m *
          ((((4 * d : ℕ) : ℂ)) ^ (-(m : ℤ))) * ((x : ℂ) ^ (m + 1)) *
          thetaDualM d chi m (x / (16 * (d : ℝ) ^ 2))) := by
    rw [← hmul]; ring
  rw [inv_mul_cancel₀ hU, one_mul] at h2
  rw [h2, thetaDualMG, dualConst]
  rw [zpow_neg, zpow_natCast]
  ring

/-- **The dual Poisson transformation of the weight-`m` holomorphic theta series**, in the
normalisation consumed by the weak functional equation (`↑(x^k)` with `k = m+1`). -/
theorem thetaHol_one_div_dual (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℕ)
    (hU : unitSum chi m ≠ 0) {x : ℝ} (hx : 0 < x) :
    thetaHol chi m (1 / x)
      = (1 * (((x ^ ((m + 1 : ℕ) : ℝ)) : ℝ) : ℂ)) • thetaDualMG d chi m x := by
  rw [thetaHol_one_div_dual_pow d hd hchi m hU hx, one_mul, smul_eq_mul,
    Real.rpow_natCast, Complex.ofReal_pow]

end

end Work.FIArea6Hecke.R
