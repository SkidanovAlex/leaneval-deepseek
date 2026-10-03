import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Gates

/-!
# PERT · `Work.PertCrux.gate_tauC_lower`

The upper gate `Qp Ξ' α = Qreg (some Ξ') (some (-Ξ' + 1/α))` contains a point at which the
perturbed coordinate `τ_f` is *bounded below* by `1/(4(Ξ'+1))`.

Recall `τ_f w = σ / (1 - exp (-2πi α w))`, so `‖τ_f w‖ = ‖σ‖ / ‖1 - exp (-2πi α w)‖`: the bound
is a **min-modulus** statement for the denominator `1 - exp(-2πi α w)` on the gate.  The gate
conditions, written out (`Work.Pert.Qp_mem_iff`), are

`Ξ' - |w.im| < w.re`  and  `w.re < Re(1/α) - Ξ' + |w.im - Im(1/α)|`,

i.e. `Qp Ξ' α` is the complement of the two opposing 45° cones with apices `Ξ'` and
`-Ξ' + 1/α`.

The pole line of `τ_f` is the line `u = α w ∈ ℝ` through the poles `k/α`; the two gate
inequalities cut out of it exactly the interval

`u ∈ (a, 1 - a)`,   `a := Ξ' / (Re(1/α) + |Im(1/α)|)`,

between the pole `0` and the pole `1/α` (both excluded, each apex of the gate lying `Ξ'` to the
wrong side of its pole).  On that line

`‖1 - exp (-2πi α w)‖ = ‖1 - exp (-2πi u)‖ = 2 |sin (π u)|`,

so picking `u = ξ` just to the right of `a` makes the denominator as small as the gate allows.

The two hypotheses on the sizes are what make the bookkeeping close:

* `QAdm` gives `Re(1/α) > 2Ξ' + 4`, hence `‖α‖ < 1/(2Ξ'+4)` (as `Re(1/α) ≤ 1/‖α‖`);
* `‖α‖ ≤ α.re + |α.im| = ‖α‖² (Re(1/α) + |Im(1/α)|)`, hence `a ≤ Ξ'‖α‖`;
* `‖σ‖ ≥ π‖α‖/2` (`hσ`) converts the additive bound `2 sin (πξ) ≤ 2πξ ≤ 2π(Ξ'+1)‖α‖` into
  `‖τ_f w‖ ≥ (π‖α‖/2) / (2π(Ξ'+1)‖α‖) = 1/(4(Ξ'+1))`.

(`InF1 α` is used only through `α.re > 0`; in fact `QAdm` alone already forces `Re(1/α) > 0`.)
-/

namespace Work.PertCrux

open Complex

theorem gate_tauC_lower {Ξ' : ℝ} (hΞ' : 4 ≤ Ξ') {σ α : ℂ} (hα : α ≠ 0)
    (hinf : MandelDim.InF1 α)
    (hadm : MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α)))
    (hσ : Real.pi * ‖α‖ / 2 ≤ ‖σ‖) :
    ∃ w ∈ Work.Pert.Qp Ξ' α, 1 / (4 * (Ξ' + 1)) ≤ ‖Work.Pert.tauC σ α w‖ := by
  have hna : 0 < ‖α‖ := norm_pos_iff.mpr hα
  -- `QAdm` at the two vertices of the gate: `Re(1/α) > 2Ξ' + 4`
  have hP2 : 2 * Ξ' + 4 < (1 / α).re := by
    have h := hadm (Ξ' : ℂ) (by simp) (-(Ξ' : ℂ) + 1 / α) (by simp)
    simp only [Complex.ofReal_re, Complex.add_re, Complex.neg_re] at h
    linarith
  -- `Re(1/α) ≤ 1/‖α‖`, hence `‖α‖ < 1/(2Ξ'+4)`
  have hle1 : (1 / α).re ≤ 1 / ‖α‖ := by
    calc (1 / α).re ≤ ‖(1 / α : ℂ)‖ := Complex.re_le_norm _
      _ = 1 / ‖α‖ := by rw [norm_div]; simp
  have hlt : ‖α‖ < 1 / (2 * Ξ' + 4) := by
    have h : 2 * Ξ' + 4 < 1 / ‖α‖ := lt_of_lt_of_le hP2 hle1
    rw [lt_div_iff₀ hna] at h
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < 2 * Ξ' + 4)]
    nlinarith [h]
  -- the two gate parameters in coordinates
  have hPsum : (1 / α).re + |(1 / α).im| = (α.re + |α.im|) / Complex.normSq α := by
    have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr hα
    rw [one_div, Complex.inv_re, Complex.inv_im]
    rw [abs_div, abs_neg, abs_of_pos hns]
    field_simp
  have hxy : ‖α‖ ≤ α.re + |α.im| := by
    have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hinf
    have h1 : ‖α‖ ^ 2 ≤ (α.re + |α.im|) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [abs_nonneg α.im, hre, mul_self_nonneg α.im, sq_abs α.im]
    nlinarith [norm_nonneg α, abs_nonneg α.im, h1, hre]
  have hPQpos : 0 < (1 / α).re + |(1 / α).im| := by
    linarith [hP2, abs_nonneg (1 / α).im]
  -- the right endpoint of the admissible interval of the pole line
  set a : ℝ := Ξ' / ((1 / α).re + |(1 / α).im|) with hadef
  have ha0 : 0 < a := by rw [hadef]; exact div_pos (by linarith) hPQpos
  have hann : ‖α‖ * ((1 / α).re + |(1 / α).im|) = (α.re + |α.im|) / ‖α‖ := by
    rw [hPsum, Complex.normSq_eq_norm_sq]
    field_simp
  have ha_le : a ≤ Ξ' * ‖α‖ := by
    rw [hadef, div_le_iff₀ hPQpos]
    have h1 : 1 ≤ ‖α‖ * ((1 / α).re + |(1 / α).im|) := by
      rw [hann, le_div_iff₀ hna]; linarith
    have h2 : Ξ' ≤ Ξ' * (‖α‖ * ((1 / α).re + |(1 / α).im|)) := by
      have := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ Ξ')
      simpa using this
    nlinarith [h2]
  have ha_half : a < 1 / 2 := by
    have h2 : Ξ' * ‖α‖ < Ξ' * (1 / (2 * Ξ' + 4)) :=
      mul_lt_mul_of_pos_left hlt (by linarith : (0:ℝ) < Ξ')
    have h3 : Ξ' * (1 / (2 * Ξ' + 4)) < 1 / 2 := by
      rw [mul_one_div, div_lt_iff₀ (by linarith : (0:ℝ) < 2 * Ξ' + 4)]
      linarith
    linarith [ha_le, h2, h3]
  have ha_B : a < (Ξ' + 1) * ‖α‖ := by
    have h : Ξ' * ‖α‖ < (Ξ' + 1) * ‖α‖ := by nlinarith
    linarith [ha_le, h]
  have haP : a * ((1 / α).re + |(1 / α).im|) = Ξ' := by
    rw [hadef]; field_simp
  -- the witness `ξ` on the pole line, chosen just inside the admissible interval
  set b : ℝ := min (1 - a) ((Ξ' + 1) * ‖α‖) with hbdef
  have hab : a < b := by rw [hbdef]; exact lt_min (by linarith) ha_B
  have hb1 : b ≤ 1 - a := by rw [hbdef]; exact min_le_left _ _
  have hb2 : b ≤ (Ξ' + 1) * ‖α‖ := by rw [hbdef]; exact min_le_right _ _
  set ξ : ℝ := (a + b) / 2 with hξdef
  have haξ : a < ξ := by rw [hξdef]; linarith
  have hξb : ξ < b := by rw [hξdef]; linarith
  have hξ0 : 0 < ξ := lt_trans ha0 haξ
  have hξ1 : ξ < 1 := by linarith [hξb, hb1, ha0]
  have hξB : ξ ≤ (Ξ' + 1) * ‖α‖ := le_of_lt (lt_of_lt_of_le hξb hb2)
  have hξP : Ξ' < ξ * ((1 / α).re + |(1 / α).im|) := by nlinarith [haξ, hPQpos]
  have hξQ : ξ * ((1 / α).re + |(1 / α).im|) < (1 / α).re + |(1 / α).im| - Ξ' := by
    have h : ξ < 1 - a := lt_of_lt_of_le hξb hb1
    nlinarith [h, hPQpos, haP]
  -- ## the witness lies in the gate
  have hmem : ((ξ : ℂ) / α) ∈ Work.Pert.Qp Ξ' α := by
    rw [Work.Pert.Qp_mem_iff]
    have hwr : ((ξ : ℂ) / α).re = ξ * (1 / α).re := by
      rw [div_eq_mul_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, one_div]
    have hwi : ((ξ : ℂ) / α).im = ξ * (1 / α).im := by
      rw [div_eq_mul_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, one_div]
    rw [hwr, hwi]
    constructor
    · have h3 : ξ * |(1 / α).im| = |ξ * (1 / α).im| := by
        rw [abs_mul, abs_of_pos hξ0]
      have h4 : ξ * ((1 / α).re + |(1 / α).im|)
          = ξ * (1 / α).re + ξ * |(1 / α).im| := by ring
      linarith
    · have h4 : |ξ * (1 / α).im - (1 / α).im| = (1 - ξ) * |(1 / α).im| := by
        have h5 : ξ * (1 / α).im - (1 / α).im = (ξ - 1) * (1 / α).im := by ring
        rw [h5, abs_mul, abs_of_neg (by linarith : ξ - 1 < 0)]
        ring
      have h5 : ξ * ((1 / α).re + |(1 / α).im|)
          = ξ * (1 / α).re + ξ * |(1 / α).im| := by ring
      nlinarith [hξQ, h4]
  refine ⟨(ξ : ℂ) / α, hmem, ?_⟩
  -- ## the moduli estimate
  set w : ℂ := (ξ : ℂ) / α with hw
  have hξpi : Real.pi * ξ < Real.pi := by nlinarith [Real.pi_pos]
  have hsinpos : 0 < Real.sin (Real.pi * ξ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) hξpi
  -- the exponent of `τ_f` at the witness is `-2πi ξ`
  have hexp : -(2 * Real.pi * Complex.I * α * w) = Complex.I * (-(2 * Real.pi * ξ)) := by
    have h1 : 2 * Real.pi * Complex.I * α * w = 2 * Real.pi * Complex.I * (ξ : ℂ) := by
      rw [hw, mul_assoc (2 * Real.pi * Complex.I) α, mul_div_cancel₀ (ξ : ℂ) hα]
    rw [h1]
    ring
  have hexp' : Complex.I * (-(2 * Real.pi * ξ))
      = Complex.I * ((-(2 * Real.pi * ξ) : ℝ) : ℂ) := by
    push_cast
    ring
  have hnormeq : ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w))‖
      = 2 * Real.sin (Real.pi * ξ) := by
    rw [hexp, hexp', norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show -(2 * Real.pi * ξ) / 2 = -(Real.pi * ξ) by ring, Real.sin_neg,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_neg,
      abs_of_pos hsinpos]
  have hsin2pos : 0 < 2 * Real.sin (Real.pi * ξ) := by linarith
  have hdenle : 2 * Real.sin (Real.pi * ξ) ≤ 2 * Real.pi * (Ξ' + 1) * ‖α‖ := by
    have h := Real.abs_sin_le_abs (x := Real.pi * ξ)
    rw [abs_of_pos hsinpos, abs_of_pos (mul_pos Real.pi_pos hξ0)] at h
    have h2 : 2 * (Real.pi * ξ) ≤ 2 * (Real.pi * ((Ξ' + 1) * ‖α‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hξB (le_of_lt Real.pi_pos))
        (by norm_num)
    nlinarith [h, h2]
  have hσpos : 0 < ‖σ‖ := lt_of_lt_of_le (by positivity) hσ
  have hcpos : 0 < 2 * Real.pi * (Ξ' + 1) * ‖α‖ := by
    have : (0:ℝ) < (Ξ' + 1) := by linarith
    positivity
  rw [Work.Pert.tauC, norm_div, hnormeq]
  have hconst : (Real.pi * ‖α‖ / 2) / (2 * Real.pi * (Ξ' + 1) * ‖α‖) = 1 / (4 * (Ξ' + 1)) := by
    field_simp
    ring
  rw [← hconst]
  exact le_trans (div_le_div_of_nonneg_right hσ (le_of_lt hcpos))
    (div_le_div_of_nonneg_left (le_of_lt hσpos) hsin2pos hdenle)

end Work.PertCrux
