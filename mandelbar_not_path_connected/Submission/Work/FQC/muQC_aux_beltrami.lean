/-
# The pointwise dilatation of the MNS twist `ℓ_t`

`ell t w = w + i (t · saw w.re)` is the shear `(x,y) ↦ (x, y + t·saw x)` of the Écalle
cylinder.  This file proves that its complex dilatation `Work.MRMT.beltramiOf (ell t) w` is
bounded by `|t| / √(1+t²)` at **every** point `w`.

Off the corner lines `Re w ∈ 1/4 + (1/2)ℤ` the map is locally real-affine with derivative
`L(1) = 1 + i t s`, `L(i) = i` where `s = ±2` is the slope of the triangle wave; hence
`∂̄ℓ = i t s / 2`, `∂ℓ = 1 + i t s / 2` and the dilatation is `i t s / (2 + i t s)`, of modulus
`|t|/√(1+t²)`.  We obtain this without ever analysing the corner points:

* if `ℓ_t` is not real-differentiable at `w` then `fderiv ℝ (ell t) w = 0`, so both Wirtinger
  derivatives vanish and the dilatation is the junk value `0`
  (`fderiv_zero_of_not_differentiableAt`);
* if it is differentiable with derivative `L`, the two *directional* difference quotients
  (the limit of `hasFDerivAt_iff_tendsto` restricted to the real and the imaginary axis) give
  `L(i) = i` (the imaginary direction is unaltered), `Re (L 1) = 1` (the real part of
  `ℓ_t (w+u)` is `Re w + u`) and `‖L 1 - 1‖ ≤ 2|t|` (the difference quotient is `t` times the
  difference quotient of `saw`, which is bounded by `2` because `saw` is `2`-Lipschitz,
  `Work.FQC.saw_lipschitz`).  The modulus bound `‖(L 1 - 1)/(L 1 + 1)‖ ≤ |t|/√(1+t²)` then
  follows from `Re (L 1) = 1` and `‖L 1 - 1‖ ≤ 2|t|`.
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.saw_lipschitz_infDist

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Filter Set Function Topology
open scoped ComplexConjugate Topology NNReal

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## 1. Elementary identities for the shear `ℓ_t` -/

theorem ell_zero (w : ℂ) : ell 0 w = w := by
  simp [ell_apply]

theorem ell_eq_id_zero : ell 0 = id := funext ell_zero

/-- The real direction: `ℓ_t (w+u) - ℓ_t w - u = i t (saw (Re w + u) - saw (Re w))`. -/
theorem ell_sub_ell_add (t : ℝ) (w : ℂ) (u : ℝ) :
    ell t (w + (u : ℂ)) - ell t w - (u : ℂ) =
      ((t * (saw (w.re + u) - saw w.re) : ℝ) : ℂ) * Complex.I := by
  simp only [ell_apply, Complex.add_re, Complex.ofReal_re, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

/-- The imaginary direction is fixed: `ℓ_t (w + ui) = ℓ_t w + ui`. -/
theorem ell_add_mul_I (t : ℝ) (w : ℂ) (u : ℝ) :
    ell t (w + (u : ℂ) * Complex.I) = ell t w + (u : ℂ) * Complex.I := by
  simp only [ell_apply, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring_nf

/-- The real part of `ℓ_t` is `Re` itself: `(ℓ_t (w + u)).re = (ℓ_t w).re + u`. -/
theorem ell_re_eq (t : ℝ) (w : ℂ) (u : ℝ) : (ell t (w + (u : ℂ))).re = (ell t w).re + u := by
  simp only [ell_apply, Complex.add_re, Complex.ofReal_re]
  simp

/-! ## 2. The two difference quotients -/

/-- Along the real axis the difference quotient of `ℓ_t` at `w` is
`1 + i t · (saw (Re w + h) - saw (Re w))/h`. -/
theorem ell_slope_real_eq (t : ℝ) (w : ℂ) (L : ℂ →L[ℝ] ℂ) {h : ℝ} (hh : h ≠ 0) :
    ‖(w + (h : ℂ)) - w‖⁻¹ * ‖ell t (w + (h : ℂ)) - ell t w - L ((w + (h : ℂ)) - w)‖
      = ‖1 + ((t * ((saw (w.re + h) - saw w.re) / h) : ℝ) : ℂ) * Complex.I - L 1‖ := by
  have h1 : (w + (h : ℂ)) - w = (h : ℂ) := by ring
  have h2 : ell t (w + (h : ℂ)) - ell t w =
      (h : ℂ) + ((t * (saw (w.re + h) - saw w.re) : ℝ) : ℂ) * Complex.I := by
    have hsub := ell_sub_ell_add t w h
    calc ell t (w + (h : ℂ)) - ell t w
        = (ell t (w + (h : ℂ)) - ell t w - (h : ℂ)) + (h : ℂ) := by abel
      _ = ((t * (saw (w.re + h) - saw w.re) : ℝ) : ℂ) * Complex.I + (h : ℂ) := by rw [hsub]
      _ = (h : ℂ) + ((t * (saw (w.re + h) - saw w.re) : ℝ) : ℂ) * Complex.I := by ring
  have hLh : L ((h : ℂ)) = (h : ℂ) * L 1 := by
    have hsm : (h : ℂ) = h • (1 : ℂ) := by rw [Complex.real_smul, mul_one]
    rw [hsm, map_smul]
    simp [Complex.real_smul]
  have hcoef : ((t * (saw (w.re + h) - saw w.re) : ℝ) : ℂ)
      = (h : ℂ) * ((t * ((saw (w.re + h) - saw w.re) / h) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  have hfac : (h : ℂ) + ((t * (saw (w.re + h) - saw w.re) : ℝ) : ℂ) * Complex.I - (h : ℂ) * L 1
      = (h : ℂ) * (1 + ((t * ((saw (w.re + h) - saw w.re) / h) : ℝ) : ℂ) * Complex.I - L 1) := by
    rw [hcoef]
    ring
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  rw [h1, h2, hLh, hfac, norm_mul]
  exact inv_mul_cancel_left₀ (ne_of_gt (norm_pos_iff.mpr hh')) _

/-- Along the imaginary axis the difference quotient of `ℓ_t` at `w` is `i - L i`. -/
theorem ell_slope_imag_eq (t : ℝ) (w : ℂ) (L : ℂ →L[ℝ] ℂ) {h : ℝ} (hh : h ≠ 0) :
    ‖(w + (h : ℂ) * Complex.I) - w‖⁻¹ *
        ‖ell t (w + (h : ℂ) * Complex.I) - ell t w - L ((w + (h : ℂ) * Complex.I) - w)‖
      = ‖Complex.I - L Complex.I‖ := by
  have h1 : (w + (h : ℂ) * Complex.I) - w = (h : ℂ) * Complex.I := by ring
  have h2 : ell t (w + (h : ℂ) * Complex.I) - ell t w = (h : ℂ) * Complex.I := by
    rw [ell_add_mul_I]; ring
  have hLh : L ((h : ℂ) * Complex.I) = (h : ℂ) * L Complex.I := by
    have hsm : (h : ℂ) * Complex.I = h • (Complex.I : ℂ) := by rw [Complex.real_smul]
    rw [hsm, map_smul, Complex.real_smul]
  have hfac : (h : ℂ) * Complex.I - (h : ℂ) * L Complex.I = (h : ℂ) * (Complex.I - L Complex.I) := by
    ring
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hz : ‖(h : ℂ) * Complex.I‖ = ‖(h : ℂ)‖ := by rw [norm_mul, Complex.norm_I, mul_one]
  rw [h1, h2, hLh, hfac, hz, norm_mul]
  exact inv_mul_cancel_left₀ (ne_of_gt (norm_pos_iff.mpr hh')) _

/-! ## 3. A complex-analytic estimate -/

/-- If `Re a = 0` and `‖a‖ ≤ 2|t|`, then `‖a/(a+2)‖ ≤ |t|/√(1+t²)`. -/
theorem norm_div_add_two_le {a : ℂ} {t : ℝ} (hre : a.re = 0) (ha : ‖a‖ ≤ 2 * |t|) :
    ‖a / (a + 2)‖ ≤ |t| / Real.sqrt (1 + t ^ 2) := by
  have hA : ‖a‖ ^ 2 ≤ 4 * t ^ 2 := by
    nlinarith [ha, abs_nonneg t, norm_nonneg a, sq_abs t]
  have hre2 : (a + 2).re = 2 := by simp [Complex.add_re, hre]
  have him2 : (a + 2).im = a.im := by simp [Complex.add_im]
  have hna : Complex.normSq a = a.im * a.im := by rw [Complex.normSq_apply, hre]; ring
  have hnorm : ‖a + 2‖ ^ 2 = ‖a‖ ^ 2 + 4 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, hre2, him2, hna]
    ring
  have hsq : (‖a / (a + 2)‖) ^ 2 ≤ (|t| / Real.sqrt (1 + t ^ 2)) ^ 2 := by
    rw [norm_div, div_pow, div_pow, hnorm, Real.sq_sqrt (by positivity), sq_abs]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hA]
  calc ‖a / (a + 2)‖ = Real.sqrt ((‖a / (a + 2)‖) ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((|t| / Real.sqrt (1 + t ^ 2)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |t| / Real.sqrt (1 + t ^ 2) := Real.sqrt_sq (div_nonneg (abs_nonneg t) (Real.sqrt_nonneg _))

/-! ## 4. The dilatation of `ℓ_t` -/

/-- The complex dilatation of the MNS twist, at every point. -/
theorem beltramiOf_ell_le (t : ℝ) (w : ℂ) :
    ‖Work.MRMT.beltramiOf (ell t) w‖ ≤ |t| / Real.sqrt (1 + t ^ 2) := by
  by_cases hd : DifferentiableAt ℝ (ell t) w
  swap
  · have hzero : Work.MRMT.beltramiOf (ell t) w = 0 := by
      simp [Work.MRMT.beltramiOf, Work.MRMT.dzbar, Work.MRMT.dz,
        fderiv_zero_of_not_differentiableAt hd]
    rw [hzero, norm_zero]
    exact div_nonneg (abs_nonneg t) (Real.sqrt_nonneg _)
  rcases eq_or_ne t 0 with rfl | ht
  · rw [ell_eq_id_zero, Work.MRMT.beltramiOf_id, norm_zero]
    exact div_nonneg (abs_nonneg 0) (Real.sqrt_nonneg _)
  set L : ℂ →L[ℝ] ℂ := fderiv ℝ (ell t) w with hLdef
  have hslope : Tendsto (fun y : ℂ => ‖y - w‖⁻¹ * ‖ell t y - ell t w - L (y - w)‖) (𝓝 w) (𝓝 0) := by
    rw [hLdef]
    exact hasFDerivAt_iff_tendsto.mp hd.hasFDerivAt
  -- the real axis
  have hreal : Tendsto
      (fun h : ℝ => ‖1 + ((t * ((saw (w.re + h) - saw w.re) / h) : ℝ) : ℂ) * Complex.I - L 1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hcont : Tendsto (fun h : ℝ => w + (h : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 w) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have h1 : ContinuousAt (fun h : ℝ => w + (h : ℂ)) 0 :=
        (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).const_add w
      simpa using h1.tendsto
    exact (hslope.comp hcont).congr' (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Function.comp_def]
      exact ell_slope_real_eq t w L (by simpa using hh))
  -- the imaginary axis
  have himag : Tendsto (fun _ : ℝ => ‖Complex.I - L Complex.I‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hcont : Tendsto (fun h : ℝ => w + (h : ℂ) * Complex.I) (𝓝[≠] (0 : ℝ)) (𝓝 w) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have h1 : ContinuousAt (fun h : ℝ => w + (h : ℂ) * Complex.I) 0 :=
        ((Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).mul_const Complex.I).const_add w
      simpa using h1.tendsto
    exact (hslope.comp hcont).congr' (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Function.comp_def]
      exact ell_slope_imag_eq t w L (by simpa using hh))
  have hLI : L Complex.I = Complex.I := by
    have h1 : Tendsto (fun _ : ℝ => ‖Complex.I - L Complex.I‖) (𝓝[≠] (0 : ℝ))
        (𝓝 ‖Complex.I - L Complex.I‖) := tendsto_const_nhds
    have h0 : ‖Complex.I - L Complex.I‖ = 0 := (tendsto_nhds_unique himag h1).symm
    exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm
  -- the two facts about `L 1`
  have hlim : Tendsto
      (fun h : ℝ => 1 + ((t * ((saw (w.re + h) - saw w.re) / h) : ℝ) : ℂ) * Complex.I)
      (𝓝[≠] (0 : ℝ)) (𝓝 (L 1)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [sub_eq_add_neg, add_assoc] using hreal
  have hL1re : (L 1).re = 1 := by
    have hre : Tendsto
        (fun h : ℝ => (1 + ((t * ((saw (w.re + h) - saw w.re) / h) : ℝ) : ℂ) * Complex.I).re)
        (𝓝[≠] (0 : ℝ)) (𝓝 (L 1).re) := (Complex.continuous_re.tendsto (L 1)).comp hlim
    have hconst : (fun h : ℝ =>
        (1 + ((t * ((saw (w.re + h) - saw w.re) / h) : ℝ) : ℂ) * Complex.I).re)
        = fun _ : ℝ => (1 : ℝ) := by
      funext h
      simp [Complex.add_re, Complex.mul_re]
    rw [hconst] at hre
    exact tendsto_nhds_unique hre tendsto_const_nhds
  have hbound : ‖L 1 - 1‖ ≤ 2 * |t| := by
    have hnormlim : Tendsto
        (fun h : ℝ => ‖1 + ((t * ((saw (w.re + h) - saw w.re) / h) : ℝ) : ℂ) * Complex.I - 1‖)
        (𝓝[≠] (0 : ℝ)) (𝓝 ‖L 1 - 1‖) :=
      (continuous_norm.tendsto (L 1 - 1)).comp (hlim.sub tendsto_const_nhds)
    refine le_of_tendsto hnormlim ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hΔ : |saw (w.re + h) - saw w.re| ≤ 2 * |h| := by
      simpa using saw_lipschitz (w.re + h) w.re
    have hdiv : |(saw (w.re + h) - saw w.re) / h| ≤ 2 := by
      rw [abs_div, div_le_iff₀ (abs_pos.mpr (by simpa using hh))]
      exact hΔ
    calc ‖1 + ((t * ((saw (w.re + h) - saw w.re) / h) : ℝ) : ℂ) * Complex.I - 1‖
        = |t * ((saw (w.re + h) - saw w.re) / h)| := by
          have hnorm : ‖((t * ((saw (w.re + h) - saw w.re) / h) : ℝ) : ℂ)‖
              = |t * ((saw (w.re + h) - saw w.re) / h)| := RCLike.norm_ofReal _
          rw [add_sub_cancel_left, norm_mul, hnorm, Complex.norm_I, mul_one]
      _ = |t| * |(saw (w.re + h) - saw w.re) / h| := by rw [abs_mul]
      _ ≤ |t| * 2 := by nlinarith [abs_nonneg t]
      _ = 2 * |t| := by ring
  -- assemble
  have hII : (Complex.I : ℂ) * L Complex.I = -1 := by rw [hLI, Complex.I_mul_I]
  have hdzbar : Work.MRMT.dzbar (ell t) w = (L 1 - 1) / 2 := by
    rw [Work.MRMT.dzbar, ← hLdef, hII]
    ring
  have hdz : Work.MRMT.dz (ell t) w = (L 1 + 1) / 2 := by
    rw [Work.MRMT.dz, ← hLdef, hII]
    ring
  have hne : L 1 + 1 ≠ 0 := by
    intro h
    have hre : (L 1).re = -1 := by
      have h2 := congrArg Complex.re h
      simp at h2
      linarith
    linarith [hL1re]
  rw [Work.MRMT.beltramiOf, hdzbar, hdz]
  have hcancel : ((L 1 - 1) / 2) / ((L 1 + 1) / 2) = (L 1 - 1) / (L 1 + 1) := by
    field_simp
  rw [hcancel]
  have hgoal : ‖(L 1 - 1) / (L 1 - 1 + 2)‖ ≤ |t| / Real.sqrt (1 + t ^ 2) :=
    norm_div_add_two_le (a := L 1 - 1) (by simp [Complex.sub_re, hL1re]) hbound
  rwa [show L 1 - 1 + 2 = L 1 + 1 by ring] at hgoal

end Work.FQC

end
