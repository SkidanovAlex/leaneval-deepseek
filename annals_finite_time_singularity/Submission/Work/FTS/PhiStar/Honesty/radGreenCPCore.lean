import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllExist

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 4000000


/-! ### Auxiliary real-power facts -/

/-- `y^{-r} ≤ z^{-r}` for `0 < z ≤ y` and `0 ≤ r`. -/
lemma rgMeas_rpow_neg_le {r y z : ℝ} (hr : 0 ≤ r) (hz : 0 < z) (hzy : z ≤ y) :
    y ^ (-r) ≤ z ^ (-r) := by
  have hy : 0 < y := lt_of_lt_of_le hz hzy
  rw [Real.rpow_neg hy.le, Real.rpow_neg hz.le]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hy r) (Real.rpow_pos_of_pos hz r)).mpr
    (Real.rpow_le_rpow hz.le hzy hr)

/-- **Pointwise kernel bound.**  For `2 ≤ z`, `y ∈ [z/2, 3z/2]` and `t` between `z` and `y`,

  `|y^{-q} t^{q-1} - y^p t^{-p-1}| ≤ Cz · |t - y|`,  `Cz = (z/2)^{-q}(q-1)(3z/2)^{q-2}
     + (3z/2)^p (p+1)(z/2)^{-p-2}`.

The function of `t` on the left vanishes at `t = y` (both terms equal `y^{-1}` there), so it is
controlled by its derivative on the interval. -/
lemma rgMeas_kernel_bound {p q z y t : ℝ} (hq : 2 ≤ q) (hp : 0 ≤ p)
    (hz : 2 ≤ z) (hy1 : z / 2 ≤ y) (hy2 : y ≤ 3 * z / 2)
    (ht : t ∈ Set.uIcc z y) :
    |y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1)|
      ≤ ((z / 2) ^ (-q) * (q - 1) * (3 * z / 2) ^ (q - 2)
          + (3 * z / 2) ^ p * (p + 1) * (z / 2) ^ (-p - 2)) * |t - y| := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hz2 : (0 : ℝ) < z / 2 := by linarith
  have hz32 : (0 : ℝ) < 3 * z / 2 := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hz2 hy1
  have htmem : min z y ≤ t ∧ t ≤ max z y := by
    have h := ht; rw [Set.uIcc] at h; exact h
  have h2le : z / 2 ≤ min z y := le_min (by linarith) hy1
  have hle32 : max z y ≤ 3 * z / 2 := max_le (by linarith) hy2
  set C : ℝ := (z / 2) ^ (-q) * (q - 1) * (3 * z / 2) ^ (q - 2)
      + (3 * z / 2) ^ p * (p + 1) * (z / 2) ^ (-p - 2) with hC
  set κ : ℝ → ℝ := fun x => y ^ (-q) * x ^ (q - 1) - y ^ p * x ^ (-p - 1) with hκ
  have hκy : κ y = 0 := by
    simp only [hκ]
    have e1 : y ^ (-q) * y ^ (q - 1) = y ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hy0]; congr 1; ring
    have e2 : y ^ p * y ^ (-p - 1) = y ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hy0]; congr 1; ring
    rw [e1, e2, sub_self]
  have hderiv : ∀ x ∈ Set.Icc (min t y) (max t y),
      HasDerivWithinAt κ (y ^ (-q) * ((q - 1) * x ^ (q - 2))
          + y ^ p * ((p + 1) * x ^ (-p - 2))) (Set.Icc (min t y) (max t y)) x := by
    intro x hx
    have hxlo : z / 2 ≤ x := le_trans (le_trans h2le (le_min htmem.1 (min_le_right _ _))) hx.1
    have hxhi : x ≤ 3 * z / 2 :=
      le_trans hx.2 (le_trans (max_le htmem.2 (le_max_right _ _)) hle32)
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hz2 hxlo)
    have h1 : HasDerivAt (fun x : ℝ => y ^ (-q) * x ^ (q - 1))
        (y ^ (-q) * ((q - 1) * x ^ (q - 2))) x := by
      have h := (Real.hasDerivAt_rpow_const (x := x) (p := q - 1) (Or.inl hx0)).const_mul
        (y ^ (-q))
      refine h.congr_deriv ?_
      rw [show (q - 1) - 1 = q - 2 by ring]
    have h2 : HasDerivAt (fun x : ℝ => y ^ p * x ^ (-p - 1))
        (y ^ p * ((-(p + 1)) * x ^ (-p - 2))) x := by
      have h := (Real.hasDerivAt_rpow_const (x := x) (p := -p - 1) (Or.inl hx0)).const_mul (y ^ p)
      refine h.congr_deriv ?_
      rw [show (-p - 1) - 1 = -p - 2 by ring]
      ring
    have h3 := h1.sub h2
    rw [hκ]
    exact h3.hasDerivWithinAt.congr_deriv (by ring)
  have hbnd : ∀ x ∈ Set.Ico (min t y) (max t y),
      ‖y ^ (-q) * ((q - 1) * x ^ (q - 2)) + y ^ p * ((p + 1) * x ^ (-p - 2))‖ ≤ C := by
    intro x hx
    have hxlo : z / 2 ≤ x :=
      le_trans (le_trans h2le (le_min htmem.1 (min_le_right _ _))) hx.1
    have hxhi : x ≤ 3 * z / 2 :=
      le_trans hx.2.le (le_trans (max_le htmem.2 (le_max_right _ _)) hle32)
    have hx0 : 0 < x := lt_of_lt_of_le hz2 hxlo
    have hAnn : 0 ≤ y ^ (-q) * ((q - 1) * x ^ (q - 2)) :=
      mul_nonneg (Real.rpow_nonneg hy0.le _)
        (mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _))
    have hBnn : 0 ≤ y ^ p * ((p + 1) * x ^ (-p - 2)) :=
      mul_nonneg (Real.rpow_nonneg hy0.le _)
        (mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _))
    have hA : y ^ (-q) * ((q - 1) * x ^ (q - 2))
        ≤ (z / 2) ^ (-q) * (q - 1) * (3 * z / 2) ^ (q - 2) := by
      have hyq : y ^ (-q) ≤ (z / 2) ^ (-q) :=
        rgMeas_rpow_neg_le (by linarith : (0 : ℝ) ≤ q) hz2 hy1
      have hxq : x ^ (q - 2) ≤ (3 * z / 2) ^ (q - 2) :=
        Real.rpow_le_rpow hx0.le hxhi (by linarith)
      have h1 : (q - 1) * x ^ (q - 2) ≤ (q - 1) * (3 * z / 2) ^ (q - 2) :=
        mul_le_mul_of_nonneg_left hxq (by linarith)
      have h2 : y ^ (-q) * ((q - 1) * x ^ (q - 2))
          ≤ (z / 2) ^ (-q) * ((q - 1) * (3 * z / 2) ^ (q - 2)) :=
        mul_le_mul hyq h1 (mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _))
          (Real.rpow_nonneg hz2.le _)
      calc y ^ (-q) * ((q - 1) * x ^ (q - 2))
          ≤ (z / 2) ^ (-q) * ((q - 1) * (3 * z / 2) ^ (q - 2)) := h2
        _ = (z / 2) ^ (-q) * (q - 1) * (3 * z / 2) ^ (q - 2) := by ring
    have hB : y ^ p * ((p + 1) * x ^ (-p - 2))
        ≤ (3 * z / 2) ^ p * (p + 1) * (z / 2) ^ (-p - 2) := by
      have hyp : y ^ p ≤ (3 * z / 2) ^ p := Real.rpow_le_rpow hy0.le hy2 hp
      have hxp : x ^ (-p - 2) ≤ (z / 2) ^ (-p - 2) := by
        have h := rgMeas_rpow_neg_le (r := p + 2) (by linarith : (0 : ℝ) ≤ p + 2) hz2 hxlo
        rwa [show -(p + 2) = -p - 2 by ring] at h
      have h1 : (p + 1) * x ^ (-p - 2) ≤ (p + 1) * (z / 2) ^ (-p - 2) :=
        mul_le_mul_of_nonneg_left hxp (by linarith)
      have h2 : y ^ p * ((p + 1) * x ^ (-p - 2))
          ≤ (3 * z / 2) ^ p * ((p + 1) * (z / 2) ^ (-p - 2)) :=
        mul_le_mul hyp h1 (mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _))
          (Real.rpow_nonneg hz32.le _)
      calc y ^ p * ((p + 1) * x ^ (-p - 2))
          ≤ (3 * z / 2) ^ p * ((p + 1) * (z / 2) ^ (-p - 2)) := h2
        _ = (3 * z / 2) ^ p * (p + 1) * (z / 2) ^ (-p - 2) := by ring
    rw [hC, Real.norm_eq_abs, abs_of_nonneg (add_nonneg hAnn hBnn)]
    linarith
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := κ)
      (f' := fun x => y ^ (-q) * ((q - 1) * x ^ (q - 2)) + y ^ p * ((p + 1) * x ^ (-p - 2)))
      (a := min t y) (b := max t y) (C := C) hderiv hbnd
      (max t y) (right_mem_Icc.mpr min_le_max)
  rcases le_total t y with h | h
  · have hMVT' : ‖κ y - κ t‖ ≤ C * (y - t) := by
      have hh := hMVT
      rwa [min_eq_left h, max_eq_right h] at hh
    rw [hκy, zero_sub, norm_neg] at hMVT'
    calc |y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1)|
        = ‖κ t‖ := by simp only [hκ, Real.norm_eq_abs]
      _ ≤ C * (y - t) := hMVT'
      _ = C * |t - y| := by
          rw [abs_of_nonpos (by linarith : t - y ≤ 0)]
          ring
  · have hMVT' : ‖κ t - κ y‖ ≤ C * (t - y) := by
      have hh := hMVT
      rwa [min_eq_right h, max_eq_left h] at hh
    rw [hκy, sub_zero] at hMVT'
    calc |y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1)|
        = ‖κ t‖ := by simp only [hκ, Real.norm_eq_abs]
      _ ≤ C * (t - y) := hMVT'
      _ = C * |t - y| := by
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - y)]

/-! ### the shrinking-interval integral vanishes at the base point -/

/-- If `g` is integrable on the two halves of `(z/2, 3z/2)` around `z`, then the integral of `|g|`
over `(z, y)` tends to `0` as `y → z` (continuity of the primitive at the base point). -/
lemma rgMeas_shrink_tendsto {g : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hI1 : IntegrableOn g (Set.Ioc (z / 2) z))
    (hI2 : IntegrableOn g (Set.Ioc z (3 * z / 2))) :
    Filter.Tendsto (fun y : ℝ => ∫ t in z..y, ‖g t‖) (nhds z) (nhds 0) := by
  have h₁ : IntegrableOn (fun t => ‖g t‖) (Set.Ioc (z / 2) z) :=
    (show Integrable g (volume.restrict (Set.Ioc (z / 2) z)) from hI1).norm
  have h₂ : IntegrableOn (fun t => ‖g t‖) (Set.Ioc z (3 * z / 2)) :=
    (show Integrable g (volume.restrict (Set.Ioc z (3 * z / 2))) from hI2).norm
  set F : ℝ → ℝ := Set.indicator (Set.Ioc (z / 2) z) (fun t => ‖g t‖)
      + Set.indicator (Set.Ioc z (3 * z / 2)) (fun t => ‖g t‖) with hF
  have hFint : Integrable F volume :=
    (h₁.integrable_indicator measurableSet_Ioc).add
      (h₂.integrable_indicator measurableSet_Ioc)
  have hcont : Continuous fun u : ℝ => ∫ t in z..u, F t :=
    MeasureTheory.Integrable.continuous_primitive hFint z
  have hlim : Filter.Tendsto (fun u : ℝ => ∫ t in z..u, F t) (nhds z) (nhds 0) := by
    have h := (hcont.continuousAt (x := z)).tendsto
    have hzF : (∫ t in z..z, F t) = 0 := intervalIntegral.integral_same
    rwa [hzF] at h
  refine Filter.Tendsto.congr' ?_ hlim
  have hmem : Set.Ioo (z / 2) (3 * z / 2) ∈ nhds z :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  filter_upwards [hmem] with u hu
  refine intervalIntegral.integral_congr fun t ht => ?_
  have ht' : t ∈ Set.Ioo (z / 2) (3 * z / 2) := by
    rw [Set.uIcc] at ht
    exact ⟨lt_of_lt_of_le (lt_min_iff.mpr ⟨by linarith, hu.1⟩) ht.1,
      lt_of_le_of_lt ht.2 (max_lt_iff.mpr ⟨by linarith, hu.2⟩)⟩
  have hpt : F t = ‖g t‖ := by
    rw [hF]
    simp only [Pi.add_apply, Set.indicator]
    by_cases htz : t ≤ z
    · rw [if_pos (show t ∈ Set.Ioc (z / 2) z from ⟨ht'.1, htz⟩),
        if_neg (show t ∉ Set.Ioc z (3 * z / 2) from fun hc => absurd hc.1 (not_lt.mpr htz))]
      ring
    · rw [if_neg (show t ∉ Set.Ioc (z / 2) z from fun hc => absurd hc.2 (not_le.mpr (lt_of_not_ge htz))),
        if_pos (show t ∈ Set.Ioc z (3 * z / 2) from ⟨lt_of_not_ge htz, ht'.2.le⟩)]
      ring
  rw [hpt]

/-! ### interval-integral helpers -/

/-- `‖∫_z^y h‖` is bounded by the integral of `‖h‖` over the (unoriented) interval. -/
lemma rgMeas_norm_intervalIntegral_le {hh : ℝ → ℝ} {z y : ℝ} :
    ‖∫ t in z..y, hh t‖ ≤ ∫ t in (min z y)..(max z y), ‖hh t‖ := by
  rcases le_total z y with h | h
  · rw [min_eq_left h, max_eq_right h]
    calc ‖∫ t in z..y, hh t‖ = ‖∫ t in Set.Ioc z y, hh t‖ := by
          rw [intervalIntegral.integral_of_le h]
      _ ≤ ∫ t in Set.Ioc z y, ‖hh t‖ :=
          MeasureTheory.norm_integral_le_integral_norm (fun t : ℝ => hh t)
      _ = ∫ t in z..y, ‖hh t‖ := by rw [intervalIntegral.integral_of_le h]
  · rw [min_eq_right h, max_eq_left h]
    calc ‖∫ t in z..y, hh t‖ = ‖∫ t in Set.Ioc y z, hh t‖ := by
          rw [intervalIntegral.integral_of_ge h, norm_neg]
      _ ≤ ∫ t in Set.Ioc y z, ‖hh t‖ :=
          MeasureTheory.norm_integral_le_integral_norm (fun t : ℝ => hh t)
      _ = ∫ t in y..z, ‖hh t‖ := by rw [intervalIntegral.integral_of_le h]

/-- For a nonnegative `h`, the integral over the unoriented interval is the absolute value of the
oriented one. -/
lemma rgMeas_intervalIntegral_abs_eq {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) (z y : ℝ) :
    ∫ t in (min z y)..(max z y), f t = |∫ t in z..y, f t| := by
  rcases le_total z y with hzy | hzy
  · rw [min_eq_left hzy, max_eq_right hzy,
      abs_of_nonneg (intervalIntegral.integral_nonneg hzy (fun t _ => hf t))]
  · rw [min_eq_right hzy, max_eq_left hzy]
    have h1 : (∫ t in z..y, f t) = -∫ t in Set.Ioc y z, f t :=
      intervalIntegral.integral_of_ge hzy
    have h2 : (∫ t in y..z, f t) = ∫ t in Set.Ioc y z, f t :=
      intervalIntegral.integral_of_le hzy
    have hnn : 0 ≤ ∫ t in Set.Ioc y z, f t := by
      rw [← intervalIntegral.integral_of_le hzy]
      exact intervalIntegral.integral_nonneg hzy (fun t _ => hf t)
    rw [h2, h1, abs_neg, abs_of_nonneg hnn]

/-! ### the combined difference quotient is `O(√|y-z|)` -/

/-- **Pointwise bound for the combined difference quotient numerator.**
With `g₀ t = c t t^{-p-1}` and `κ_y(t) = y^{-q} t^{q-1} - y^p t^{-p-1}` (which vanishes at `t = y`),

  `‖∫_z^y c t κ_y(t)‖ ≤ Cz · (3z/2)^{p+1} · |y - z| · ∫_{(z,y)} ‖g₀‖`,

where `Cz = (z/2)^{-q}(q-1)(3z/2)^{q-2} + (3z/2)^p (p+1)(z/2)^{-p-2}` is the kernel constant of
`rgMeas_kernel_bound`. -/
lemma rgMeas_CP_pointwise {p q z y : ℝ} {c : ℝ → ℝ} (hz : 2 ≤ z) (hq : 2 ≤ q) (hp : 0 ≤ p)
    (hy1 : z / 2 ≤ y) (hy2 : y ≤ 3 * z / 2)
    (hIf : IntegrableOn (fun t => ‖c t * t ^ (-p - 1)‖) (Set.uIoc z y)) :
    ‖∫ t in z..y, c t * (y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1))‖
      ≤ ((z / 2) ^ (-q) * (q - 1) * (3 * z / 2) ^ (q - 2)
          + (3 * z / 2) ^ p * (p + 1) * (z / 2) ^ (-p - 2))
        * (3 * z / 2) ^ (p + 1) * |y - z|
        * ∫ t in (min z y)..(max z y), ‖c t * t ^ (-p - 1)‖ := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hz2 : (0 : ℝ) < z / 2 := by linarith
  have hz32 : (0 : ℝ) < 3 * z / 2 := by linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hz2 hy1
  set Cz : ℝ := (z / 2) ^ (-q) * (q - 1) * (3 * z / 2) ^ (q - 2)
      + (3 * z / 2) ^ p * (p + 1) * (z / 2) ^ (-p - 2) with hCz
  have hCznn : 0 ≤ Cz := by
    rw [hCz]
    have h1 : 0 ≤ (z / 2) ^ (-q) := Real.rpow_nonneg hz2.le _
    have h2 : 0 ≤ q - 1 := by linarith
    have h3 : 0 ≤ (3 * z / 2) ^ (q - 2) := Real.rpow_nonneg hz32.le _
    have h4 : 0 ≤ (3 * z / 2) ^ p := Real.rpow_nonneg hz32.le _
    have h5 : 0 ≤ (z / 2) ^ (-p - 2) := Real.rpow_nonneg hz2.le _
    have h6 : 0 ≤ p + 1 := by linarith
    nlinarith [mul_nonneg (mul_nonneg h1 h2) h3, mul_nonneg (mul_nonneg h4 h6) h5]
  have h1 : ‖∫ t in z..y, c t * (y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1))‖
      ≤ ∫ t in (min z y)..(max z y),
          ‖c t * (y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1))‖ :=
    rgMeas_norm_intervalIntegral_le
  have h2 : ∫ t in (min z y)..(max z y),
        ‖c t * (y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1))‖
      ≤ ∫ t in (min z y)..(max z y),
          Cz * (3 * z / 2) ^ (p + 1) * |y - z| * ‖c t * t ^ (-p - 1)‖ := by
    rw [intervalIntegral.integral_of_le (min_le_max),
      intervalIntegral.integral_of_le (min_le_max)]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
      (hIf.const_mul (Cz * (3 * z / 2) ^ (p + 1) * |y - z|)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htmem : t ∈ Set.uIcc z y := ⟨ht.1.le, ht.2⟩
    have htlo : z / 2 ≤ t :=
      le_trans (le_min (by linarith) hy1) ht.1.le
    have hthi : t ≤ 3 * z / 2 := le_trans ht.2 (max_le (by linarith) hy2)
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hz2 htlo
    have hty : |t - y| ≤ |y - z| := by
      rcases le_total z y with h | h
      · have htlo' : z < t := by simpa [min_eq_left h] using ht.1
        have hthi' : t ≤ y := by simpa [max_eq_right h] using ht.2
        rw [abs_of_nonpos (by linarith : t - y ≤ 0),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - z)]
        linarith
      · have htlo' : y < t := by simpa [min_eq_right h] using ht.1
        have hthi' : t ≤ z := by simpa [max_eq_left h] using ht.2
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - y),
          abs_of_nonpos (by linarith : y - z ≤ 0)]
        linarith
    have hkb : |y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1)| ≤ Cz * |y - z| := by
      have h := rgMeas_kernel_bound hq hp hz hy1 hy2 htmem
      rw [← hCz] at h
      have h2' : Cz * |t - y| ≤ Cz * |y - z| := mul_le_mul_of_nonneg_left hty hCznn
      linarith
    have hcg : |c t| = ‖c t * t ^ (-p - 1)‖ * t ^ (p + 1) := by
      have h : ‖c t * t ^ (-p - 1)‖ = |c t| * t ^ (-p - 1) := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      rw [h, mul_assoc, ← Real.rpow_add ht0]
      norm_num
    have htp : t ^ (p + 1) ≤ (3 * z / 2) ^ (p + 1) :=
      Real.rpow_le_rpow ht0.le hthi (by linarith)
    have hgnn : 0 ≤ ‖c t * t ^ (-p - 1)‖ := norm_nonneg _
    calc ‖c t * (y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1))‖
        = |c t| * |y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1)| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |c t| * (Cz * |y - z|) := mul_le_mul_of_nonneg_left hkb (abs_nonneg _)
      _ = (Cz * |y - z|) * (‖c t * t ^ (-p - 1)‖ * t ^ (p + 1)) := by rw [hcg]; ring
      _ ≤ (Cz * |y - z|) * (‖c t * t ^ (-p - 1)‖ * (3 * z / 2) ^ (p + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCznn (abs_nonneg _))
          exact mul_le_mul_of_nonneg_left htp hgnn
      _ = Cz * (3 * z / 2) ^ (p + 1) * |y - z| * ‖c t * t ^ (-p - 1)‖ := by ring
  have h3 : ∫ t in (min z y)..(max z y),
        Cz * (3 * z / 2) ^ (p + 1) * |y - z| * ‖c t * t ^ (-p - 1)‖
      = Cz * (3 * z / 2) ^ (p + 1) * |y - z|
        * ∫ t in (min z y)..(max z y), ‖c t * t ^ (-p - 1)‖ := by
    rw [show (∫ t in (min z y)..(max z y),
          Cz * (3 * z / 2) ^ (p + 1) * |y - z| * ‖c t * t ^ (-p - 1)‖)
        = ∫ t in (min z y)..(max z y),
          (Cz * (3 * z / 2) ^ (p + 1) * |y - z|) * ‖c t * t ^ (-p - 1)‖
        from intervalIntegral.integral_congr (fun t _ => by ring),
      intervalIntegral.integral_const_mul]
  rw [h3] at h2
  exact le_trans h1 h2

/-! ### the combined difference quotient tends to `0` -/

/-- **The crux estimate.**  With `q ≥ 2`, `p ≥ 0` and the two honestness hypotheses on `c`
(`c t^{q-1}` integrable up to `z`, `c t^{-p-1}` integrable beyond `z`), the combined difference
quotient
`(y^{-q}(A y - A z) + y^p (B y - B z))/(y - z)`, where `A` and `B` are the primitives of
`c t^{q-1}` and `c t^{-p-1}`, is `O(√|y-z|)`, hence tends to `0` as `y → z`.  The mechanism is
that the numerator is a single integral of `c t κ_y(t)` with `κ_y` vanishing at `t = y`, so the
two source terms cancel to first order. -/
lemma rgMeas_CP_tendsto {p q z : ℝ} {c : ℝ → ℝ}
    (hq : 2 ≤ q) (hp : 0 ≤ p) (hz : 2 ≤ z)
    (hnear : IntegrableOn (fun t => c t * t ^ (q - 1)) (Set.Ioc 1 z))
    (hfar : IntegrableOn (fun t => c t * t ^ (-p - 1)) (Set.Ioi z)) :
    Filter.Tendsto (fun y : ℝ =>
        (∫ t in z..y, (y ^ (-q) * (c t * t ^ (q - 1)) - y ^ p * (c t * t ^ (-p - 1))))
          / (y - z)) (nhdsWithin z {z}ᶜ) (nhds 0) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hz2 : (0 : ℝ) < z / 2 := by linarith
  have hz32 : (0 : ℝ) < 3 * z / 2 := by linarith
  set g : ℝ → ℝ := fun t => c t * t ^ (-p - 1) with hg
  have hI1 : IntegrableOn g (Set.Ioc (z / 2) z) := by
    have hbase : IntegrableOn (fun t => c t * t ^ (q - 1)) (Set.Ioc (z / 2) z) :=
      hnear.mono_set (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
    have hbased : Integrable (fun t => c t * t ^ (q - 1))
        (volume.restrict (Set.Ioc (z / 2) z)) := hbase
    have hdom : Integrable (fun t => (z / 2) ^ (-(p + q)) * ‖c t * t ^ (q - 1)‖)
        (volume.restrict (Set.Ioc (z / 2) z)) := hbased.norm.const_mul _
    refine Integrable.mono' hdom ?_ ?_
    · have hrpow : AEStronglyMeasurable (fun t : ℝ => t ^ (-(p + q)))
          (volume.restrict (Set.Ioc (z / 2) z)) :=
        ContinuousOn.aestronglyMeasurable
          (continuousOn_id.rpow_const
            (fun x hx => Or.inl (ne_of_gt (lt_trans hz2 hx.1)))) measurableSet_Ioc
      refine (hbased.1.mul hrpow).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : (0 : ℝ) < t := lt_trans hz2 ht.1
      have hthis : t ^ (q - 1) * t ^ (-(p + q)) = t ^ (-p - 1) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      simp only [Pi.mul_apply, hg]
      rw [mul_assoc, hthis]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : (0 : ℝ) < t := lt_trans hz2 ht.1
      have hmono : t ^ (-p - 1) ≤ (z / 2) ^ (-(p + q)) * t ^ (q - 1) := by
        have h1 : (z / 2) ^ (p + q) ≤ t ^ (p + q) :=
          Real.rpow_le_rpow hz2.le ht.1.le (by linarith)
        have h2 : t ^ (-(p + q)) ≤ (z / 2) ^ (-(p + q)) := by
          rw [Real.rpow_neg ht0.le, Real.rpow_neg hz2.le]
          exact (inv_le_inv₀ (Real.rpow_pos_of_pos ht0 _) (Real.rpow_pos_of_pos hz2 _)).mpr h1
        have h3 : t ^ (-p - 1) = t ^ (-(p + q)) * t ^ (q - 1) := by
          rw [← Real.rpow_add ht0]; congr 1; ring
        rw [h3]
        exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg ht0.le _)
      rw [hg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc |c t| * t ^ (-p - 1) ≤ |c t| * ((z / 2) ^ (-(p + q)) * t ^ (q - 1)) :=
            mul_le_mul_of_nonneg_left hmono (abs_nonneg _)
        _ = (z / 2) ^ (-(p + q)) * (|c t| * t ^ (q - 1)) := by ring
  have hI2 : IntegrableOn g (Set.Ioc z (3 * z / 2)) :=
    hfar.mono_set (fun t ht => ht.1)
  have hIg1 : IntegrableOn (fun t => ‖g t‖) (Set.Ioc (z / 2) z) :=
    (show Integrable g (volume.restrict (Set.Ioc (z / 2) z)) from hI1).norm
  have hIg2 : IntegrableOn (fun t => ‖g t‖) (Set.Ioc z (3 * z / 2)) :=
    (show Integrable g (volume.restrict (Set.Ioc z (3 * z / 2))) from hI2).norm
  have hshrink : Filter.Tendsto (fun y : ℝ => ∫ t in z..y, ‖g t‖) (nhds z) (nhds 0) :=
    rgMeas_shrink_tendsto hz0 hI1 hI2
  have hH : Filter.Tendsto (fun y : ℝ => ‖∫ t in z..y, ‖g t‖‖) (nhds z) (nhds 0) := by
    simpa using hshrink.norm
  have hlim : Filter.Tendsto
      (fun y : ℝ => ((z / 2) ^ (-q) * (q - 1) * (3 * z / 2) ^ (q - 2)
          + (3 * z / 2) ^ p * (p + 1) * (z / 2) ^ (-p - 2)) * (3 * z / 2) ^ (p + 1)
          * ‖∫ t in z..y, ‖g t‖‖) (nhdsWithin z {z}ᶜ) (nhds 0) := by
    have h : Filter.Tendsto
        (fun y : ℝ => (((z / 2) ^ (-q) * (q - 1) * (3 * z / 2) ^ (q - 2)
          + (3 * z / 2) ^ p * (p + 1) * (z / 2) ^ (-p - 2)) * (3 * z / 2) ^ (p + 1))
          * ‖∫ t in z..y, ‖g t‖‖) (nhds z) (nhds 0) := by
      simpa using hH.const_mul (((z / 2) ^ (-q) * (q - 1) * (3 * z / 2) ^ (q - 2)
          + (3 * z / 2) ^ p * (p + 1) * (z / 2) ^ (-p - 2)) * (3 * z / 2) ^ (p + 1))
    exact h.mono_left (nhdsWithin_le_nhds : nhdsWithin z {z}ᶜ ≤ nhds z)
  refine squeeze_zero_norm' ?_ hlim
  have hmem : Set.Ioo (z / 2) (3 * z / 2) ∈ nhdsWithin z {z}ᶜ :=
    (nhdsWithin_le_nhds : nhdsWithin z {z}ᶜ ≤ nhds z)
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  filter_upwards [hmem, self_mem_nhdsWithin] with y hy hyne
  have hy1 : z / 2 ≤ y := hy.1.le
  have hy2 : y ≤ 3 * z / 2 := hy.2.le
  have hIf : IntegrableOn (fun t => ‖g t‖) (Set.uIoc z y) := by
    rcases le_total z y with h | h
    · rw [Set.uIoc_of_le h]
      exact hIg2.mono_set (fun t ht => ⟨ht.1, le_trans ht.2 (by linarith [hy.2])⟩)
    · rw [Set.uIoc_of_ge h]
      exact hIg1.mono_set (fun t ht => ⟨lt_of_le_of_lt hy1 ht.1, ht.2⟩)
  have hrew : (∫ t in z..y, (y ^ (-q) * (c t * t ^ (q - 1)) - y ^ p * (c t * t ^ (-p - 1))))
      = ∫ t in z..y, c t * (y ^ (-q) * t ^ (q - 1) - y ^ p * t ^ (-p - 1)) :=
    intervalIntegral.integral_congr (fun t _ => by ring)
  rw [hrew, norm_div]
  have hpos : 0 < ‖y - z‖ := by
    rw [Real.norm_eq_abs]; exact abs_pos.mpr (sub_ne_zero.mpr hyne)
  rw [div_le_iff₀ hpos]
  have hpoint := rgMeas_CP_pointwise hz hq hp hy1 hy2 hIf
  rw [show (∫ t in (min z y)..(max z y), ‖g t‖) = ‖∫ t in z..y, ‖g t‖‖ from
    rgMeas_intervalIntegral_abs_eq (fun t => norm_nonneg _) z y] at hpoint
  rw [Real.norm_eq_abs (y - z)]
  exact hpoint.trans (le_of_eq (by ring))


end Work.FTS.PhiStar.Honesty
