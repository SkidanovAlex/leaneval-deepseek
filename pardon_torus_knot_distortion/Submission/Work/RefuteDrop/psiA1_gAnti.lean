import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.dropTrace

/-!
# Strict antitonicity of `u ↦ 3 · trN1 u - yclip · (2c - trS u)`

The function `u ↦ 3 * trN1 u - yclip * (2 * (97/100) - trS u)` (with
`yclip = (7/5) · 2^{1/3}`) is the `y`-window of the `A`-branch of the trace of the cutting plane
on the `RefuteDrop` configuration, with the absolute value of `trN1` removed on the sub-arc on
which `trN1` is positive; it is strictly decreasing on `[ang (7/10), ang (9/2)]`.

The derivative is

`(3 / trS u) · (trS u · trN1'(u) - yclip · trA u · trA'(u))`.

Since `trS u ≥ 68/100`, `trN1'(u) ≤ -3/10` and `trA u · trA'(u) ≥ -1/12` on the interval (indeed
the last bound holds for every `u`, by the double-angle formula
`trA u · trA'(u) = (312/10000) cos 2u + (1457/20000) sin 2u` and Cauchy–Schwarz), and
`yclip ≤ 9/5`, the derivative is bounded above by

`(68/100)·(-3/10) - (9/5)·(-1/12) = -51/250 + 3/20 = -27/500 < 0`.
-/

open Work.BoxShrink.PinchOff.RefuteDrop
open Set

namespace Work.RefuteDrop

noncomputable section

/-! ## The function and its derivative -/

/-- `u ↦ 3 · trN1 u - yclip · (2·(97/100) - trS u)`, the object of the theorem. -/
def psiG (u : ℝ) : ℝ := 3 * trN1 u - yclip * (2*(97/100) - trS u)

/-- The derivative of `trN1`. -/
def psiG_trN1d (u : ℝ) : ℝ := -(7761/10000 : ℝ) * Real.sin u + (4907/5000 : ℝ) * Real.cos u

/-- The derivative of `trA`. -/
def psiG_trAd (u : ℝ) : ℝ := (2/25 : ℝ) * Real.sin u - (39/100 : ℝ) * Real.cos u

/-- `trN1` is the sinusoid `(7761/10000) cos u + (4907/5000) sin u`. -/
lemma psiG_trN1_closed (u : ℝ) :
    trN1 u = (7761/10000 : ℝ) * Real.cos u + (4907/5000 : ℝ) * Real.sin u := by
  simp only [trN1, trB1, trA]; ring

lemma psiG_hasDerivAt_trN1 (u : ℝ) : HasDerivAt trN1 (psiG_trN1d u) u := by
  have htrN1 : trN1 = fun v : ℝ => (7761/10000 : ℝ) * Real.cos v + (4907/5000 : ℝ) * Real.sin v := by
    funext v; simp only [trN1, trB1, trA]; ring
  rw [htrN1]
  have h1 : HasDerivAt (fun v : ℝ => (7761/10000 : ℝ) * Real.cos v)
      ((7761/10000 : ℝ) * (-(Real.sin u))) u :=
    (Real.hasDerivAt_cos u).const_mul (7761/10000)
  have h2 : HasDerivAt (fun v : ℝ => (4907/5000 : ℝ) * Real.sin v)
      ((4907/5000 : ℝ) * Real.cos u) u :=
    (Real.hasDerivAt_sin u).const_mul (4907/5000)
  have h := h1.add h2
  have hval : ((7761/10000 : ℝ) * (-(Real.sin u)) + (4907/5000 : ℝ) * Real.cos u)
      = psiG_trN1d u := by
    simp only [psiG_trN1d]; ring
  rwa [hval] at h

lemma psiG_hasDerivAt_trS (u : ℝ) : HasDerivAt trS (-(3 * trA u * psiG_trAd u) / trS u) u := by
  have hA : HasDerivAt trA (psiG_trAd u) u := by
    have htrA : trA = fun v : ℝ => -(2/25 : ℝ) * Real.cos v - (39/100 : ℝ) * Real.sin v := rfl
    rw [htrA]
    have h1 : HasDerivAt (fun v : ℝ => -(2/25 : ℝ) * Real.cos v)
        ((-(2/25 : ℝ)) * (-(Real.sin u))) u :=
      (Real.hasDerivAt_cos u).const_mul (-(2/25))
    have h2 : HasDerivAt (fun v : ℝ => (39/100 : ℝ) * Real.sin v)
        ((39/100 : ℝ) * Real.cos u) u :=
      (Real.hasDerivAt_sin u).const_mul (39/100)
    have h := h1.sub h2
    have hval : ((-(2/25 : ℝ)) * (-(Real.sin u)) - (39/100 : ℝ) * Real.cos u) = psiG_trAd u := by
      simp only [psiG_trAd]; ring
    rwa [hval] at h
  have hp : HasDerivAt (fun v => (trA v)^2) (2 * (trA u)^1 * psiG_trAd u) u := hA.pow 2
  have h2 : HasDerivAt (fun v => (97/100)^2 - 3 * (trA v)^2)
      (0 - 3 * (2 * (trA u)^1 * psiG_trAd u)) u :=
    (hasDerivAt_const u ((97/100)^2)).sub (hp.const_mul 3)
  have h3 := h2.sqrt (ne_of_gt (trS_arg_pos u))
  have hval : (0 - 3 * (2 * (trA u)^1 * psiG_trAd u))
        / (2 * Real.sqrt ((97/100)^2 - 3 * (trA u)^2))
      = -(3 * trA u * psiG_trAd u) / trS u := by
    rw [show (97/100)^2 - 3 * (trA u)^2 = (trS u)^2 from (trS_sq u).symm,
      Real.sqrt_sq (trS_nonneg u)]
    ring
  rwa [hval] at h3

lemma psiG_hasDerivAt (u : ℝ) :
    HasDerivAt psiG (3 * psiG_trN1d u - 3 * yclip * trA u * psiG_trAd u / trS u) u := by
  have h1 : HasDerivAt (fun v => 3 * trN1 v) (3 * psiG_trN1d u) u :=
    (psiG_hasDerivAt_trN1 u).const_mul 3
  have hS : HasDerivAt (fun v => yclip * (2 * (97/100) - trS v))
      (yclip * (0 - (-(3 * trA u * psiG_trAd u) / trS u))) u :=
    ((hasDerivAt_const u (2 * (97/100))).sub (psiG_hasDerivAt_trS u)).const_mul yclip
  have h3 := h1.sub hS
  have hval : (3 * psiG_trN1d u - yclip * (0 - (-(3 * trA u * psiG_trAd u) / trS u)))
      = 3 * psiG_trN1d u - 3 * yclip * trA u * psiG_trAd u / trS u := by ring
  have h4 := h3.congr_deriv hval
  have hfun : (fun v => 3 * trN1 v) - (fun v => yclip * (2 * (97/100) - trS v)) = psiG := by
    funext v; simp only [Pi.sub_apply, psiG]
  exact hfun ▸ h4

lemma psiG_continuous_trN1 : Continuous trN1 := by
  have h : trN1 = fun u : ℝ =>
      (7761/10000 : ℝ) * Real.cos u + (4907/5000 : ℝ) * Real.sin u := by
    funext u; simp only [trN1, trB1, trA]; ring
  rw [h]; fun_prop

lemma psiG_continuous : Continuous psiG := by
  have h1 : Continuous (fun v => 3 * trN1 v) := psiG_continuous_trN1.const_mul 3
  have h2 : Continuous (fun v => yclip * (2*(97/100) - trS v)) :=
    (continuous_const.sub continuous_trS).const_mul yclip
  have hcont : Continuous ((fun v => 3 * trN1 v) - (fun v => yclip * (2*(97/100) - trS v))) :=
    h1.sub h2
  have hfun : ((fun v => 3 * trN1 v) - (fun v => yclip * (2*(97/100) - trS v))) = psiG := by
    funext v; simp only [Pi.sub_apply, psiG]
  rwa [hfun] at hcont

/-! ## The three estimates on the interval -/

/-- `trS` is bounded below by `68/100` (globally). -/
lemma psiG_trS_ge (u : ℝ) : 68/100 ≤ trS u := by
  have h := trS_sq u
  have hA := trA_sq_le u
  have hnn := trS_nonneg u
  nlinarith [h, hA, hnn]

/-- `trN1'` is bounded above by `-3/10` on `(ang (7/10), ang (9/2))`. -/
lemma psiG_trN1d_le (u : ℝ) (hu : u ∈ Ioo (ang (7/10)) (ang (9/2))) : psiG_trN1d u ≤ -3/10 := by
  have hp : (7761/10000 : ℝ) * Real.sin u - (4907/5000 : ℝ) * Real.cos u ≥ 3/10 := by
    rcases le_or_gt u (Real.pi/2) with hu' | hu'
    · have hu1 : ang (7/10) ≤ u := le_of_lt hu.1
      have hu2 : u ≤ ang 1 := by rw [ang_one]; exact hu'
      have hsin := (sin_bounds_ang_lo (t1 := 7/10) (t2 := 1)
        (by norm_num) (by norm_num) (by norm_num) hu1 hu2).1
      have hcos := (cos_bounds_ang (t1 := 7/10) (t2 := 1)
        (by norm_num) (by norm_num) hu1 hu2).2
      nlinarith [hsin, hcos]
    · have hu1 : ang 1 ≤ u := by rw [ang_one]; exact le_of_lt hu'
      have hu2 : u ≤ ang (9/2) := le_of_lt hu.2
      have hsin := (sin_bounds_ang_hi (t1 := 1) (t2 := 9/2)
        (by norm_num) (by norm_num) hu1 hu2).1
      have hcos := (cos_bounds_ang (t1 := 1) (t2 := 9/2)
        (by norm_num) (by norm_num) hu1 hu2).2
      nlinarith [hsin, hcos]
  simp only [psiG_trN1d]; linarith

/-- `trA u · trA'(u)` is bounded below by `-1/12` (globally).  This is the Cauchy–Schwarz bound
on the sinusoid `(312/10000) cos 2u + (1457/20000) sin 2u`. -/
lemma psiG_trA_mul_ge (u : ℝ) : -(1/12 : ℝ) ≤ trA u * psiG_trAd u := by
  have hc : Real.cos (2*u) = Real.cos u ^ 2 - Real.sin u ^ 2 := by
    rw [Real.cos_two_mul]; nlinarith [Real.cos_sq_add_sin_sq u]
  have hs : Real.sin (2*u) = 2 * Real.sin u * Real.cos u := Real.sin_two_mul u
  have hkey : trA u * psiG_trAd u
      = (312/10000 : ℝ) * Real.cos (2*u) + (1457/20000 : ℝ) * Real.sin (2*u) := by
    rw [trA, psiG_trAd, hc, hs]; ring
  have hCS : Real.cos (2*u)^2 + Real.sin (2*u)^2 = 1 := Real.cos_sq_add_sin_sq (2*u)
  have hsq : ((312/10000 : ℝ) * Real.cos (2*u) + (1457/20000 : ℝ) * Real.sin (2*u))^2
      ≤ (312/10000 : ℝ)^2 + (1457/20000)^2 := by
    nlinarith [hCS, sq_nonneg ((312/10000 : ℝ) * Real.sin (2*u)
      - (1457/20000 : ℝ) * Real.cos (2*u))]
  have hb : (312/10000 : ℝ)^2 + (1457/20000)^2 ≤ (1/12 : ℝ)^2 := by norm_num
  have h2 : (trA u * psiG_trAd u)^2 ≤ (1/12 : ℝ)^2 := by rw [hkey]; linarith
  have h3 : |trA u * psiG_trAd u| ≤ 1/12 := by
    have := sq_le_sq.mp h2
    rwa [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/12)] at this
  linarith [(abs_le.mp h3).1]

/-- `yclip ≤ 9/5`. -/
lemma psiG_yclip_le : yclip ≤ 9/5 := by
  rw [yclip]
  have h3 : (2:ℝ) ≤ (9/7)^((3:ℕ):ℝ) := by rw [Real.rpow_natCast]; norm_num
  have h := (Real.rpow_le_rpow_iff (by norm_num : (0:ℝ) ≤ 2) (by positivity)
    (by norm_num : (0:ℝ) < (1/3:ℝ))).mpr h3
  have h2 : (((9/7:ℝ))^((3:ℕ):ℝ))^(1/3:ℝ) = 9/7 := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (9/7:ℝ))]
    norm_num
  rw [h2] at h
  nlinarith [h]

/-! ## The sign of the derivative -/

/-- On any point where `trS ≥ Slo > 0`, `trN1' ≤ N1hi < 0` and `trA·trA' ≥ Ulo`, the derivative
of `psiG` is negative as soon as the certificate `Slo·N1hi - yclip·Ulo` is negative. -/
lemma psiG_deriv_neg {x Slo N1hi Ulo : ℝ} (hSp : 0 < Slo) (hS1 : Slo ≤ trS x)
    (hN : psiG_trN1d x ≤ N1hi) (hNneg : N1hi < 0)
    (hU : Ulo ≤ trA x * psiG_trAd x)
    (hcert : Slo * N1hi - yclip * Ulo < 0) : deriv psiG x < 0 := by
  have htrS : 0 < trS x := lt_of_lt_of_le hSp hS1
  have hd : deriv psiG x = 3 * psiG_trN1d x - 3 * yclip * trA x * psiG_trAd x / trS x :=
    (psiG_hasDerivAt x).deriv
  have hrew : deriv psiG x
      = (3 / trS x) * (trS x * psiG_trN1d x - yclip * (trA x * psiG_trAd x)) := by
    rw [hd]; field_simp
  rw [hrew]
  refine mul_neg_of_pos_of_neg (div_pos (by norm_num) htrS) ?_
  have h1 : trS x * psiG_trN1d x ≤ Slo * N1hi := by
    have ha : trS x * psiG_trN1d x ≤ trS x * N1hi :=
      mul_le_mul_of_nonneg_left hN (le_of_lt htrS)
    have hb : trS x * N1hi ≤ Slo * N1hi :=
      mul_le_mul_of_nonpos_right hS1 (le_of_lt hNneg)
    linarith
  have hyc : -yclip ≤ 0 := by linarith [yclip_lower]
  have h2 : -yclip * (trA x * psiG_trAd x) ≤ -yclip * Ulo :=
    mul_le_mul_of_nonpos_left hU hyc
  linarith

/-! ## The theorem -/

lemma psiG_strictAntiOn :
    StrictAntiOn psiG (Set.Icc (ang (7/10)) (ang (9/2))) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) psiG_continuous.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  refine psiG_deriv_neg (Slo := 68/100) (N1hi := -3/10) (Ulo := -(1/12))
    (by norm_num) (psiG_trS_ge x) (psiG_trN1d_le x hx) (by norm_num) (psiG_trA_mul_ge x) ?_
  have hy := psiG_yclip_le
  nlinarith [hy]

end

end Work.RefuteDrop

namespace Work.RefuteDrop

theorem psiA1_gAnti :
    StrictAntiOn (fun u : ℝ => 3 * Work.BoxShrink.PinchOff.RefuteDrop.trN1 u - Work.BoxShrink.PinchOff.RefuteDrop.yclip * (2 * (97/100) - Work.BoxShrink.PinchOff.RefuteDrop.trS u))
      (Set.Icc (Work.BoxShrink.PinchOff.RefuteDrop.ang (7/10)) (Work.BoxShrink.PinchOff.RefuteDrop.ang (9/2))) := by
  exact psiG_strictAntiOn

end Work.RefuteDrop
