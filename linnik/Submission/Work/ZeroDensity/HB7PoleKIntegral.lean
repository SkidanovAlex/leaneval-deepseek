import Mathlib
import Submission.Work.ZeroDensity.LogFree.poleLSDefs

namespace Work.ZeroDensity

open MeasureTheory Complex

/-! ## The Euler integral for `Γ` with a positive real rate

For `r > 0` and `0 < w.re` the integral `∫_{y>0} e^{-y/r} y^{w-1} dy` converges absolutely and
equals `Γ(w) r^w`.  This is `Complex.integral_cpow_mul_exp_neg_mul_Ioi` with the rate `r` replaced
by `1/r`, together with a direct integrability proof: the modulus of the integrand is
`y ^ (w.re - 1) · e^{-y/r}`, which is integrable on `(0,∞)` by
`integrableOn_rpow_mul_exp_neg_mul_rpow`. -/

lemma hb7PoleK_integrableOn_exp_neg_div_mul_cpow {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun y : ℝ => ((Real.exp (-(y / r)) : ℝ) : ℂ) * (y : ℂ) ^ (w - 1))
      (Set.Ioi 0) := by
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := w.re - 1) (b := 1 / r)
    (by linarith) one_pos (one_div_pos.mpr hr)
  refine hg.mono' ?_ ?_
  · measurability
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    rw [Complex.norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (Real.exp_pos _).le]
    simp only [Complex.sub_re, Complex.one_re, Real.rpow_one]
    rw [show -(1 / r) * y = -(y / r) by ring, mul_comm]

lemma hb7PoleK_integral_exp_neg_div_mul_cpow {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : 0 < w.re) :
    (∫ y in Set.Ioi (0 : ℝ), ((Real.exp (-(y / r)) : ℝ) : ℂ) * (y : ℂ) ^ (w - 1))
      = Complex.Gamma w * (r : ℂ) ^ w := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := w) (r := 1 / r) hw
    (one_div_pos.mpr hr)
  have h1 : (1 : ℂ) / ((1 / r : ℝ) : ℂ) = (r : ℂ) := by
    push_cast
    field_simp
  rw [h1, mul_comm] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
  rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div]
  have key : ((1 / r : ℝ) : ℂ) * (y : ℂ) = (y : ℂ) / (r : ℂ) := by
    push_cast
    ring
  rw [key, mul_comm]

/-! ## The pointwise shape of the pole kernel

For real `y > 0` the product `y^{1-ρ} · conj(y^{1-σ}) / y` is `y^{(2-ρ-\barσ)-1}`: conjugating
`y^{1-σ}` moves the conjugation onto the exponent (the base is a positive real), the exponents add,
and dividing by `y = y^1` subtracts one. -/

lemma hb7PoleK_cpow_mul_conj_cpow_div {y : ℝ} (hy : 0 < y) (ρ σ : ℂ) :
    (y : ℂ) ^ (1 - ρ) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - σ)) / (y : ℂ)
      = (y : ℂ) ^ ((2 - ρ - (starRingEnd ℂ) σ) - 1) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have harg : ((y : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]
    exact Real.pi_ne_zero.symm
  have hconj : (starRingEnd ℂ) ((y : ℂ) ^ (1 - σ))
      = (y : ℂ) ^ ((starRingEnd ℂ) (1 - σ)) := by
    have h := Complex.cpow_conj (y : ℂ) (1 - σ) harg
    simp only [Complex.conj_ofReal] at h
    exact h.symm
  have hexp : (1 - ρ) + (starRingEnd ℂ) (1 - σ) = 2 - ρ - (starRingEnd ℂ) σ := by
    simp only [map_sub, map_one]
    ring
  have hdiv : (y : ℂ) ^ (2 - ρ - (starRingEnd ℂ) σ) / (y : ℂ)
      = (y : ℂ) ^ ((2 - ρ - (starRingEnd ℂ) σ) - 1) := by
    rw [div_eq_mul_inv, ← Complex.cpow_neg_one (y : ℂ), ← Complex.cpow_add _ _ hy0]
    exact congrArg (fun e : ℂ => (y : ℂ) ^ e) (by ring)
  rw [hconj, ← Complex.cpow_add (1 - ρ) ((starRingEnd ℂ) (1 - σ)) hy0, hexp, hdiv]

/-! Entry identity for the pole Gram kernel: for `Re ρ < 1`, `Re σ < 1` and `0 < U' ≤ X`,
`poleK X U' ρ σ = Γ(2-ρ-\barσ)(X^{2-ρ-\barσ} - U'^{2-ρ-\barσ})` equals the integral
`∫_{y>0} (e^{-y/X} - e^{-y/U'}) · y^{1-ρ} · conj(y^{1-σ}) / y dy`:  the integral representation
`∫_{y>0} e^{-y/X} y^{w-1} dy = Γ(w) X^w` of `Complex.integral_cpow_mul_exp_neg_mul_Ioi`
(with `w = (1-ρ) + (1-\barσ) = 2-ρ-\barσ`, and `y^{w-1} = y^{1-ρ} * conj(y^{1-σ}) / y` for real `y > 0`). -/
theorem HB7PoleKIntegral {X U' : ℝ} (hX : 0 < X) (hU' : 0 < U') (hUX : U' ≤ X)
    (ρ σ : ℂ) (hρ : ρ.re < 1) (hσ : σ.re < 1) :
    Work.ZeroDensity.LogFree.poleK X U' ρ σ
      = ∫ y in Set.Ioi (0 : ℝ),
          (((Real.exp (-(y / X)) - Real.exp (-(y / U')) : ℝ) : ℂ)
            * (y : ℂ) ^ (1 - ρ) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - σ)) / (y : ℂ)) := by
  let w : ℂ := 2 - ρ - (starRingEnd ℂ) σ
  have hwre : w.re = 2 - ρ.re - σ.re := by
    rw [show w = 2 - ρ - (starRingEnd ℂ) σ from rfl]
    rw [Complex.sub_re, Complex.sub_re, Complex.conj_re]
    norm_num
  have hwpos : 0 < w.re := by
    rw [hwre]
    linarith
  have hIX := hb7PoleK_integrableOn_exp_neg_div_mul_cpow (r := X) hX hwpos
  have hIU := hb7PoleK_integrableOn_exp_neg_div_mul_cpow (r := U') hU' hwpos
  have hVX := hb7PoleK_integral_exp_neg_div_mul_cpow (r := X) hX hwpos
  have hVU := hb7PoleK_integral_exp_neg_div_mul_cpow (r := U') hU' hwpos
  have hcongr : (∫ y in Set.Ioi (0 : ℝ),
          (((Real.exp (-(y / X)) - Real.exp (-(y / U')) : ℝ) : ℂ)
            * (y : ℂ) ^ (1 - ρ) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - σ)) / (y : ℂ)))
      = ∫ y in Set.Ioi (0 : ℝ),
          (((Real.exp (-(y / X)) : ℝ) : ℂ) * (y : ℂ) ^ (w - 1)
            - ((Real.exp (-(y / U')) : ℝ) : ℂ) * (y : ℂ) ^ (w - 1)) := by
    refine integral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    have hypos : 0 < y := hy
    have h1 : (y : ℂ) ^ (1 - ρ) * (starRingEnd ℂ) ((y : ℂ) ^ (1 - σ)) / (y : ℂ)
        = (y : ℂ) ^ (w - 1) := hb7PoleK_cpow_mul_conj_cpow_div hypos ρ σ
    rw [Complex.ofReal_sub]
    calc ((↑(Real.exp (-(y / X))) - ↑(Real.exp (-(y / U')))) * ↑y ^ (1 - ρ)
            * (starRingEnd ℂ) (↑y ^ (1 - σ)) / ↑y)
        = (↑(Real.exp (-(y / X))) - ↑(Real.exp (-(y / U'))))
            * (↑y ^ (1 - ρ) * (starRingEnd ℂ) (↑y ^ (1 - σ)) / ↑y) := by ring
      _ = (↑(Real.exp (-(y / X))) - ↑(Real.exp (-(y / U')))) * ↑y ^ (w - 1) := by rw [h1]
      _ = ↑(Real.exp (-(y / X))) * ↑y ^ (w - 1)
            - ↑(Real.exp (-(y / U'))) * ↑y ^ (w - 1) := by ring
  rw [hcongr, integral_sub hIX hIU, hVX, hVU]
  simp only [Work.ZeroDensity.LogFree.poleK]
  rw [show w = 2 - ρ - (starRingEnd ℂ) σ from rfl]
  ring

end Work.ZeroDensity
