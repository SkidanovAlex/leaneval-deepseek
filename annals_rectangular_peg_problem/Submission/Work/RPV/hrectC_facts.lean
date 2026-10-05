import Mathlib
import Submission.Work.RPV.HrectPhase

/-!
# Algebraic facts about the normalising unit complex number `hrectC`

Writing `c = hrectC φ d = i·e^{iφ/2}·d/‖d‖` (for `d ≠ 0`), this file records the
four elementary facts used when a `φ`-rectangle `x' - y' = e^{iφ}(x - y)`,
`x + y = x' + y'` is rotated into the normal form `R z w θ`:

* `‖c‖ = 1`,
* `c · conj c = 1` (so `c` is a unit complex number),
* `conj d · c² = -e^{iφ} · d` (the diagonal direction of the rotated rectangle),
* `d · conj c = -i·e^{-iφ/2}·‖d‖`.

All four are consequences of `i² = -1`, `e^{iθ}·conj(e^{iθ}) = 1` and
`d · conj d = ‖d‖²`.
-/

noncomputable section

namespace Work.RPV

theorem hrectC_facts (φ : ℝ) (d : ℂ) (hd : d ≠ 0) :
    ‖hrectC φ d‖ = 1 ∧
    hrectC φ d * (starRingEnd ℂ) (hrectC φ d) = 1 ∧
    (starRingEnd ℂ) d * (hrectC φ d) ^ 2 = -Complex.exp ((φ : ℂ) * Complex.I) * d ∧
    d * (starRingEnd ℂ) (hrectC φ d) =
      -Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I) * (‖d‖ : ℂ) := by
  have hr : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hrne : (‖d‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  -- `d · conj d = ‖d‖²`
  have hdd : d * (starRingEnd ℂ) d = (‖d‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hdd' : (starRingEnd ℂ) d * d = (‖d‖ : ℂ) ^ 2 := by
    rw [mul_comm, hdd]
  -- the square of the exponential factor is the full phase
  have hE2 : Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) ^ 2
      = Complex.exp ((φ : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul (((φ / 2 : ℝ) : ℂ) * Complex.I) 2]
    congr 1
    push_cast
    ring
  -- the conjugate of the exponential factor
  have hconjE : (starRingEnd ℂ) (Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  -- the conjugate of `hrectC φ d`
  have hconjc : (starRingEnd ℂ) (hrectC φ d)
      = -Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I) *
        ((starRingEnd ℂ) d / (‖d‖ : ℂ)) := by
    rw [hrectC, map_mul, map_mul, map_div₀, hconjE, Complex.conj_I, Complex.conj_ofReal]
  have h1 : ‖hrectC φ d‖ = 1 := by
    rw [hrectC, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg d)]
    exact div_self (ne_of_gt hr)
  have h2 : hrectC φ d * (starRingEnd ℂ) (hrectC φ d) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    norm_num
  have h3 : (starRingEnd ℂ) d * (hrectC φ d) ^ 2
      = -Complex.exp ((φ : ℂ) * Complex.I) * d := by
    have hc2 : (hrectC φ d) ^ 2
        = -Complex.exp ((φ : ℂ) * Complex.I) * d ^ 2 / (‖d‖ : ℂ) ^ 2 := by
      rw [hrectC, mul_pow, mul_pow, hE2, Complex.I_sq, div_pow]
      ring
    rw [hc2]
    rw [show (starRingEnd ℂ) d *
          (-Complex.exp ((φ : ℂ) * Complex.I) * d ^ 2 / (‖d‖ : ℂ) ^ 2)
        = -Complex.exp ((φ : ℂ) * Complex.I) * ((starRingEnd ℂ) d * d) * d /
            (‖d‖ : ℂ) ^ 2 by ring]
    rw [hdd']
    field_simp
  have h4 : d * (starRingEnd ℂ) (hrectC φ d)
      = -Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I) * (‖d‖ : ℂ) := by
    rw [hconjc]
    rw [show d * (-Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I) *
          ((starRingEnd ℂ) d / (‖d‖ : ℂ)))
        = -Complex.I * Complex.exp (((-(φ / 2) : ℝ) : ℂ) * Complex.I) *
            (d * (starRingEnd ℂ) d) / (‖d‖ : ℂ) by ring]
    rw [hdd]
    field_simp
  exact ⟨h1, h2, h3, h4⟩

end Work.RPV
