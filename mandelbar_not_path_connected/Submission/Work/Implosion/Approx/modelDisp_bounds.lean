import Mathlib
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp
import Submission.Work.Implosion.Approx.modelDisp_eq_neg_h_mul_integral

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

set_option maxHeartbeats 1000000

/-!
# Uniform bounds on the model displacement `Φ = modelDisp a h u`

For the local normal form of `Disp.lean`, with `a = i·λ` (`λ > 0`) and a point `u`
whose Écalle point `ζ = ecalPt a u` is small (`‖ζ‖ + λ ≤ 1/4`), the displacement

  `Φ(u) = (log(1+A₁) − log(1+A₂))/(2a)`,  `A₁ = (ζ−a)h(ζ)`, `A₂ = (ζ+a)h(ζ)`

satisfies the three uniform bounds requested downstream:

* `Re Φ ≤ −1/40`  (the displacement really points downwards),
* `‖Φ‖ ≤ 6`,
* `Φ + h(ζ)/(1+ζ·h(ζ)) = O(λ²)`  with constant `100`.

The third bound is the important one: it says that `Φ` agrees, to second order in
`λ`, with the *rational* expression `−h(ζ)/(1+ζ h(ζ))` — not merely with `−h(ζ)`
(which is only the first order term).  The mechanism is the exact identity

  `2a·(Φ + q) = Λ(−w) − Λ(w)`,   `q = h(ζ)/(1+ζh(ζ))`, `w = a·q`,

where `Λ(z) = log(1+z) − z + z²/2` is the cubic remainder of the logarithm; the
quadratic terms cancel because `Λ(−w) − Λ(w)` is odd and starts at `w³`.
-/

/-- `logRem z = log (1+z) - z + z²/2`: the cubic remainder of the logarithm
(= `log (1+z) - logTaylor 3 z`). -/
noncomputable def logRem (z : ℂ) : ℂ := Complex.log (1 + z) - z + z ^ 2 / 2

lemma logTaylor_three (z : ℂ) : Complex.logTaylor 3 z = z - z ^ 2 / 2 := by
  simp only [Complex.logTaylor_succ, Complex.logTaylor_zero, Pi.add_apply]
  ring

lemma logRem_eq (z : ℂ) : logRem z = Complex.log (1 + z) - Complex.logTaylor 3 z := by
  rw [logTaylor_three]
  simp only [logRem]
  ring

/-- The cubic remainder of the logarithm is `O(‖z‖³)`. -/
lemma norm_logRem_le (z : ℂ) (hz : ‖z‖ < 1) :
    ‖logRem z‖ ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := by
  have h := Complex.norm_log_sub_logTaylor_le 2 hz
  rw [show ((2 : ℕ) : ℝ) + 1 = 3 by norm_num] at h
  rw [logRem_eq]
  exact h

/-- On the disc `‖z‖ ≤ 3/5` the cubic remainder is bounded by `5‖z‖³/6`. -/
lemma norm_logRem_le_three_fifths (z : ℂ) (hz : ‖z‖ ≤ 3/5) :
    ‖logRem z‖ ≤ 5 * ‖z‖ ^ 3 / 6 := by
  refine (norm_logRem_le z (by linarith)).trans ?_
  have hinv : (1 - ‖z‖)⁻¹ ≤ 5/2 := by
    have h := (inv_le_inv₀ (by linarith : (0:ℝ) < 1 - ‖z‖) (by norm_num : (0:ℝ) < 2/5)).mpr
      (by linarith : (2:ℝ)/5 ≤ 1 - ‖z‖)
    rw [show ((2:ℝ)/5)⁻¹ = 5/2 by norm_num] at h
    exact h
  have hx := mul_le_mul_of_nonneg_left hinv (by positivity : (0:ℝ) ≤ ‖z‖^3/3)
  calc ‖z‖^3 * (1 - ‖z‖)⁻¹ / 3 = ‖z‖^3/3 * (1 - ‖z‖)⁻¹ := by ring
    _ ≤ ‖z‖^3/3 * (5/2) := hx
    _ = 5 * ‖z‖^3 / 6 := by ring

/-- The argument of a product of two elements of the open right half-plane is the sum
of the arguments. -/
lemma arg_add_mem_Ioc_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hx' : |x.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have hy' : |y.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy)
  rw [abs_lt] at hx' hy'
  exact ⟨by linarith [hx'.1, hy'.1], by linarith [hx'.2, hy'.2]⟩

/-- **The exact second-order identity.**  With `ζ = ecalPt a u`, `H = h ζ`,
`c = 1 + ζH`, `w = aH/c`,

  `2a·(modelDisp a h u + H·c⁻¹) = logRem (−w) − logRem w`.

The two quadratic terms of the two logarithms cancel. -/
lemma two_a_mul_modelDisp_add_inv (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ζ H c w : ℂ) (ha : a ≠ 0)
    (hζa : ζ = ecalPt a u) (hHa : H = h ζ)
    (hc : c = 1 + ζ * H) (hw : w = a * H / c)
    (hc0 : c ≠ 0) (hw1 : 1 - w ≠ 0) (hw2 : 1 + w ≠ 0)
    (ha1 : c.arg + (1 - w).arg ∈ Set.Ioc (-Real.pi) Real.pi)
    (ha2 : c.arg + (1 + w).arg ∈ Set.Ioc (-Real.pi) Real.pi) :
    2 * a * (modelDisp a h u + H * c⁻¹) = logRem (-w) - logRem w := by
  have hden : 1 + ζ * H ≠ 0 := by rw [← hc]; exact hc0
  have hA1 : 1 + dispNum1 a h u = c * (1 - w) := by
    have e1 : 1 + dispNum1 a h u = 1 + (ζ - a) * H := by
      simp only [dispNum1]
      rw [← hζa, ← hHa]
    have e2 : c * (1 - w) = 1 + (ζ - a) * H := by
      rw [hw, hc]
      field_simp
      ring
    rw [e1, e2]
  have hA2 : 1 + dispNum2 a h u = c * (1 + w) := by
    have e1 : 1 + dispNum2 a h u = 1 + (ζ + a) * H := by
      simp only [dispNum2]
      rw [← hζa, ← hHa]
    have e2 : c * (1 + w) = 1 + (ζ + a) * H := by
      rw [hw, hc]
      field_simp
      ring
    rw [e1, e2]
  have hlog1 : Complex.log (1 + dispNum1 a h u) = Complex.log c + Complex.log (1 - w) := by
    rw [hA1, Complex.log_mul hc0 hw1 ha1]
  have hlog2 : Complex.log (1 + dispNum2 a h u) = Complex.log c + Complex.log (1 + w) := by
    rw [hA2, Complex.log_mul hc0 hw2 ha2]
  have hmd : 2 * a * modelDisp a h u
      = Complex.log (1 - w) - Complex.log (1 + w) := by
    have h : 2 * a * modelDisp a h u
        = Complex.log (1 + dispNum1 a h u) - Complex.log (1 + dispNum2 a h u) := by
      rw [modelDisp]
      field_simp
    rw [h, hlog1, hlog2]
    ring
  have hw2' : 2 * w = 2 * a * (H * c⁻¹) := by
    rw [hw, div_eq_mul_inv]; ring
  rw [mul_add, hmd, ← hw2']
  simp only [logRem, sub_eq_add_neg]
  ring_nf

/-- **The main bounds.** -/
theorem modelDisp_bounds (lam : ℝ) (h : ℂ → ℂ) (u : ℂ) (hl : 0 < lam)
    (hζ : ‖ecalPt ((lam:ℂ)*I) u‖ + lam ≤ 1/4)
    (hh : ‖h (ecalPt ((lam:ℂ)*I) u) - 1‖ ≤ 1/2) :
    (modelDisp ((lam:ℂ)*I) h u).re ≤ -1/40
    ∧ ‖modelDisp ((lam:ℂ)*I) h u‖ ≤ 6
    ∧ ‖modelDisp ((lam:ℂ)*I) h u + h (ecalPt ((lam:ℂ)*I) u) *
        (1 + ecalPt ((lam:ℂ)*I) u * h (ecalPt ((lam:ℂ)*I) u))⁻¹‖ ≤ 100 * lam^2 := by
  set a : ℂ := (lam:ℂ)*I with ha
  set ζ : ℂ := ecalPt a u with hζa
  set H : ℂ := h ζ with hHa
  set c : ℂ := 1 + ζ * H with hc
  set w : ℂ := a * H / c with hw
  set Q : ℝ := ‖H * c⁻¹‖ with hQ
  -- basic numerical facts
  have hlne : lam ≠ 0 := ne_of_gt hl
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hlne) Complex.I_ne_zero
  have hanorm : ‖a‖ = lam := by
    rw [ha, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos hl
  have hlam4 : lam ≤ 1/4 := by linarith [hζ, norm_nonneg ζ]
  have hζle : ‖ζ‖ ≤ 1/4 := by linarith [hζ, hl]
  -- bounds on H
  have hHle : ‖H‖ ≤ 3/2 := by
    calc ‖H‖ = ‖(H - 1) + 1‖ := by ring_nf
      _ ≤ ‖H - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖H - 1‖ + 1 := by rw [norm_one]
      _ ≤ 3/2 := by linarith [hh]
  have hHge : (1/2 : ℝ) ≤ ‖H‖ := by
    have h1 : (1 : ℝ) - ‖H‖ ≤ ‖(1 : ℂ) - H‖ := by
      have := norm_sub_norm_le (1 : ℂ) H
      rwa [norm_one] at this
    rw [norm_sub_rev] at h1
    linarith [hh]
  have habsre : |H.re - 1| ≤ 1/2 := by
    have h1 : |(H - 1).re| ≤ ‖H - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [hh]
  have hreH : (1/2 : ℝ) ≤ H.re := by linarith [(abs_le.mp habsre).1]
  have hreHle : H.re ≤ 3/2 := by linarith [(abs_le.mp habsre).2]
  have hHsq : ‖H‖^2 ≤ 2 * H.re - 3/4 := by
    have h1 : (H.re - 1)^2 + H.im^2 ≤ 1/4 := by
      have h2 : ‖H - 1‖^2 ≤ (1/2)^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
      rw [Complex.sq_norm, Complex.normSq_apply] at h2
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at h2
      linarith [h2]
    have h3 : ‖H‖^2 = H.re^2 + H.im^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h3]; nlinarith [h1]
  have hHH : (2/3 : ℝ) * ‖H‖^2 ≤ H.re := by nlinarith [hHsq, hreHle]
  have hζre : -(1/4 : ℝ) ≤ ζ.re := by
    have h1 := (abs_le.mp (Complex.abs_re_le_norm ζ)).1
    linarith [hζle]
  -- `c = 1 + ζH` is close to 1
  have hcd : ‖c - 1‖ ≤ 3/8 := by
    have hce : c - 1 = ζ * H := by rw [hc]; ring
    rw [hce, norm_mul]
    calc ‖ζ‖ * ‖H‖ ≤ (1/4) * (3/2) := mul_le_mul hζle hHle (norm_nonneg H) (by norm_num)
      _ = 3/8 := by norm_num
  have hc_upper : ‖c‖ ≤ 11/8 := by
    calc ‖c‖ = ‖(c - 1) + 1‖ := by ring_nf
      _ ≤ ‖c - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖c - 1‖ + 1 := by rw [norm_one]
      _ ≤ 11/8 := by linarith [hcd]
  have hc_lower : 5/8 ≤ ‖c‖ := by
    have h1 : (1 : ℝ) - ‖c‖ ≤ ‖(1 : ℂ) - c‖ := by
      have := norm_sub_norm_le (1 : ℂ) c
      rwa [norm_one] at this
    rw [norm_sub_rev] at h1
    linarith [hcd]
  have hre_c : 0 < c.re := by
    have h2 : c.re = 1 + (ζ * H).re := by rw [hc]; simp
    have h3 : -(3/8 : ℝ) ≤ (ζ * H).re := by
      have h4 : ‖ζ * H‖ ≤ 3/8 := by
        rw [norm_mul]
        calc ‖ζ‖ * ‖H‖ ≤ (1/4) * (3/2) := mul_le_mul hζle hHle (norm_nonneg H) (by norm_num)
          _ = 3/8 := by norm_num
      have h5 := (abs_le.mp (Complex.abs_re_le_norm (ζ * H))).1
      linarith [h5, h4]
    rw [h2]; linarith
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0] at hre_c
    simp at hre_c
  -- the key real-part inequality: `re (H/c) ≥ (5/12) ‖H/c‖²`
  have hA : (5/12 : ℝ) * ‖H‖^2 ≤ H.re * c.re + H.im * c.im := by
    have hcr : c.re = 1 + (ζ * H).re := by rw [hc]; simp
    have hci : c.im = (ζ * H).im := by rw [hc]; simp
    have hid : H.re * c.re + H.im * c.im = H.re + ‖H‖^2 * ζ.re := by
      rw [hcr, hci, Complex.mul_re, Complex.mul_im]
      have h2 : ‖H‖^2 = H.re * H.re + H.im * H.im := by
        rw [Complex.sq_norm, Complex.normSq_apply]
      rw [h2]; ring
    rw [hid]
    nlinarith [hHH, hζre, sq_nonneg ‖H‖]
  have hreq : (5/12 : ℝ) * Q^2 ≤ (H * c⁻¹).re := by
    rw [hQ]
    have hdiv : H * c⁻¹ = H / c := by rw [div_eq_mul_inv]
    have e1 : (H / c).re = (H.re * c.re + H.im * c.im) / ‖c‖^2 := by
      rw [Complex.div_re, Complex.sq_norm, Complex.normSq_apply]; ring_nf
    have e2 : ‖H / c‖^2 = ‖H‖^2 / ‖c‖^2 := by rw [norm_div, div_pow]
    rw [hdiv, e1, e2]
    have hposD : (0 : ℝ) < ‖c‖^2 := by positivity
    rw [show (5/12) * (‖H‖^2 / ‖c‖^2) = ((5/12) * ‖H‖^2) / ‖c‖^2 by ring]
    exact (div_le_div_iff_of_pos_right hposD).mpr hA
  -- bounds on `Q` and `w`
  have hQle : Q ≤ 12/5 := by
    rw [hQ, norm_mul, norm_inv]
    have h1 : ‖c‖⁻¹ ≤ (5/8 : ℝ)⁻¹ := by
      rw [inv_le_inv₀ (by linarith : (0:ℝ) < ‖c‖) (by norm_num : (0:ℝ) < 5/8)]
      exact hc_lower
    calc ‖H‖ * ‖c‖⁻¹ ≤ (3/2) * (5/8)⁻¹ := mul_le_mul hHle h1 (by positivity) (by norm_num)
      _ = 12/5 := by norm_num
  have hQge : (4/11 : ℝ) ≤ Q := by
    rw [hQ, norm_mul, norm_inv]
    have h1 : (8/11 : ℝ) ≤ ‖c‖⁻¹ := by
      have h := (inv_le_inv₀ (by norm_num : (0:ℝ) < 11/8) (by linarith : (0:ℝ) < ‖c‖)).mpr
        hc_upper
      rw [show ((11:ℝ)/8)⁻¹ = 8/11 by norm_num] at h
      exact h
    calc (4 : ℝ)/11 = (1/2) * (8/11) := by norm_num
      _ ≤ ‖H‖ * ‖c‖⁻¹ := mul_le_mul hHge h1 (by norm_num) (norm_nonneg H)
  have hw_eq : w = a * (H * c⁻¹) := by rw [hw]; ring
  have hwQ : ‖w‖ = lam * Q := by rw [hw_eq, norm_mul, hanorm, ← hQ]
  have hw_le : ‖w‖ ≤ 12 * lam / 5 := by
    rw [hwQ]
    calc lam * Q ≤ lam * (12/5) := mul_le_mul_of_nonneg_left hQle (le_of_lt hl)
      _ = 12 * lam / 5 := by ring
  have hw_small : ‖w‖ ≤ 3/5 := by
    have h1 : 12 * lam / 5 ≤ 12 * (1/4) / 5 := by nlinarith [hl]
    linarith [hw_le, h1]
  -- non-vanishing and argument conditions
  have hw_re_pos : 0 < (1 - w).re := by
    have h1 : w.re ≤ ‖w‖ := (abs_le.mp (Complex.abs_re_le_norm w)).2
    rw [Complex.sub_re, Complex.one_re]
    linarith [hw_small, h1]
  have hw_re_pos2 : 0 < (1 + w).re := by
    have h1 : -(‖w‖) ≤ w.re := (abs_le.mp (Complex.abs_re_le_norm w)).1
    rw [Complex.add_re, Complex.one_re]
    linarith [hw_small, h1]
  have hw1 : 1 - w ≠ 0 := fun h0 => by rw [h0] at hw_re_pos; simp at hw_re_pos
  have hw2 : 1 + w ≠ 0 := fun h0 => by rw [h0] at hw_re_pos2; simp at hw_re_pos2
  have ha1 : c.arg + (1 - w).arg ∈ Set.Ioc (-Real.pi) Real.pi :=
    arg_add_mem_Ioc_of_re_pos hre_c hw_re_pos
  have ha2 : c.arg + (1 + w).arg ∈ Set.Ioc (-Real.pi) Real.pi :=
    arg_add_mem_Ioc_of_re_pos hre_c hw_re_pos2
  -- the exact identity
  have hid : 2 * a * (modelDisp a h u + H * c⁻¹) = logRem (-w) - logRem w :=
    two_a_mul_modelDisp_add_inv a h u ζ H c w ha0 hζa hHa hc hw hc0 hw1 hw2 ha1 ha2
  have h2a : (2 : ℂ) * a ≠ 0 := mul_ne_zero (by norm_num) ha0
  -- the error term
  have hlogRem_neg : ‖logRem (-w)‖ ≤ 5 * ‖w‖^3 / 6 := by
    have h := norm_logRem_le_three_fifths (-w) (by rw [norm_neg]; exact hw_small)
    rwa [norm_neg] at h
  have hlogRem_pos : ‖logRem w‖ ≤ 5 * ‖w‖^3 / 6 :=
    norm_logRem_le_three_fifths w hw_small
  have hcorr : ‖modelDisp a h u + H * c⁻¹‖ ≤ 5 * ‖w‖^3 / (6 * lam) := by
    have hsplit : modelDisp a h u + H * c⁻¹ = (logRem (-w) - logRem w) / (2 * a) := by
      rw [eq_div_iff h2a]
      rw [mul_comm]
      exact hid
    rw [hsplit, norm_div]
    have h2an : ‖(2 : ℂ) * a‖ = 2 * lam := by
      rw [norm_mul, Complex.norm_ofNat, hanorm]
    rw [h2an]
    have hsum : ‖logRem (-w) - logRem w‖ ≤ 5 * ‖w‖^3 / 3 := by
      calc ‖logRem (-w) - logRem w‖ ≤ ‖logRem (-w)‖ + ‖logRem w‖ := norm_sub_le _ _
        _ ≤ 5 * ‖w‖^3 / 6 + 5 * ‖w‖^3 / 6 := add_le_add hlogRem_neg hlogRem_pos
        _ = 5 * ‖w‖^3 / 3 := by ring
    calc ‖logRem (-w) - logRem w‖ / (2 * lam) ≤ (5 * ‖w‖^3 / 3) / (2 * lam) :=
          div_le_div_of_nonneg_right hsum (by linarith)
      _ = 5 * ‖w‖^3 / (6 * lam) := by ring
  -- conclusion 3
  have h3b : ‖modelDisp a h u + H * c⁻¹‖ ≤ 100 * lam^2 := by
    refine hcorr.trans ?_
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 6 * lam)]
    have hw3 : ‖w‖^3 ≤ (12 * lam / 5)^3 := pow_le_pow_left₀ (norm_nonneg w) hw_le 3
    nlinarith [hw3, sq_nonneg lam, hl]
  -- conclusion 2
  have h2b : ‖modelDisp a h u‖ ≤ 6 := by
    have h1 : ‖modelDisp a h u‖ ≤ ‖modelDisp a h u + H * c⁻¹‖ + ‖H * c⁻¹‖ := by
      calc ‖modelDisp a h u‖ = ‖(modelDisp a h u + H * c⁻¹) - H * c⁻¹‖ := by ring_nf
        _ ≤ ‖modelDisp a h u + H * c⁻¹‖ + ‖H * c⁻¹‖ := norm_sub_le _ _
    have hQle' : ‖H * c⁻¹‖ ≤ 12/5 := hQle
    have hcorr2 : 5 * ‖w‖^3 / (6 * lam) ≤ (288/25) * lam^2 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 6 * lam)]
      have hw3 : ‖w‖^3 ≤ (12 * lam / 5)^3 := pow_le_pow_left₀ (norm_nonneg w) hw_le 3
      nlinarith [hw3, sq_nonneg lam]
    have hcorr3 : (288/25) * lam^2 ≤ 18/25 := by nlinarith [hl, hlam4]
    linarith [h1, hcorr, hcorr2, hcorr3, hQle']
  -- conclusion 1
  have h1b : (modelDisp a h u).re ≤ -1/40 := by
    have hdecomp : (modelDisp a h u).re
        = (modelDisp a h u + H * c⁻¹).re - (H * c⁻¹).re := by
      rw [Complex.add_re]; ring
    have hcorr_re : (modelDisp a h u + H * c⁻¹).re ≤ 5 * lam^2 * Q^3 / 6 := by
      have h := Complex.re_le_norm (modelDisp a h u + H * c⁻¹)
      have heq : 5 * ‖w‖^3 / (6 * lam) = 5 * lam^2 * Q^3 / 6 := by
        rw [div_eq_div_iff (by linarith : (6:ℝ) * lam ≠ 0) (by norm_num : (6:ℝ) ≠ 0),
          hwQ, mul_pow]
        ring
      linarith [h, hcorr, heq]
    have hmain : (5/12 : ℝ) * Q^2 - 5 * lam^2 * Q^3 / 6 ≥ 1/40 := by
      have hL2 : lam^2 ≤ 1/16 := by nlinarith [hl, hlam4]
      have hQ2 : (0:ℝ) ≤ Q := norm_nonneg _
      have hlamQ : lam^2 * Q ≤ 3/20 := by
        calc lam^2 * Q ≤ (1/16) * (12/5) := mul_le_mul hL2 hQle hQ2 (by norm_num)
          _ = 3/20 := by norm_num
      have h1 : 5 * lam^2 * Q^3 / 6 ≤ Q^2 / 8 := by
        calc 5 * lam^2 * Q^3 / 6 = Q^2 * (5/6 * (lam^2 * Q)) := by ring
          _ ≤ Q^2 * (5/6 * (3/20)) :=
              mul_le_mul_of_nonneg_left (by linarith [hlamQ]) (sq_nonneg Q)
          _ = Q^2 / 8 := by ring
      have h2 : 7/24 * (16/121) ≤ 7/24 * Q^2 := by nlinarith [hQge]
      nlinarith [h1, h2]
    rw [hdecomp]
    linarith [hcorr_re, hreq, hmain]
  exact ⟨h1b, h2b, h3b⟩

end Work.Implosion.Approx
