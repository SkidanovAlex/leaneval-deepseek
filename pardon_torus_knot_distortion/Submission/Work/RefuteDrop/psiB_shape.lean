import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.dropTrace

/-!
# The shape of the window function `psiB` for the `RefuteDrop` configuration

`psiB u = 3 * |trN2 u| - (7/5) * (2 * (97/100) + trS u)` is the obstruction to the `B` branch of
the trace of the cutting plane leaving the box through the `z`-face: it is `≤ 0` exactly on the
arcs of the longitude circle on which the `z`-coordinate of the branch lies inside the box.

This file proves `Work.RefuteDrop.psiB_shape`: `psiB` has exactly four zeros in `[0, 2π]`, one in
each of the four windows entering the definitions of `uB1, …, uB4`, and those zeros give the sign
pattern `-, +, -, +, -` of `psiB` on the longitude circle.
-/

namespace Work.RefuteDrop

open Work.BoxShrink.PinchOff.RefuteDrop
open Set

noncomputable section

/-! ## Closed forms, derivatives and continuity -/

lemma trN2_closed (u : ℝ) :
    trN2 u = (209/400 : ℝ) * Real.cos u + (14329/10000 : ℝ) * Real.sin u := by
  simp only [trN2, trB2, trA]; ring

lemma trA_closed (u : ℝ) :
    trA u = (-(2/25) : ℝ) * Real.cos u + (-(39/100) : ℝ) * Real.sin u := by
  simp only [trA]; ring

lemma continuous_trN2 : Continuous trN2 := by
  have h : trN2 = fun u : ℝ => (209/400) * Real.cos u + (14329/10000) * Real.sin u := by
    funext u; exact trN2_closed u
  rw [h]; fun_prop

/-- The derivative of `trN2`. -/
def trN2d (u : ℝ) : ℝ := (14329/10000 : ℝ) * Real.cos u - (209/400 : ℝ) * Real.sin u

/-- The derivative of `trA`. -/
def trAd (u : ℝ) : ℝ := (2/25 : ℝ) * Real.sin u - (39/100 : ℝ) * Real.cos u

/-- `psiB` on the region where `trN2 ≥ 0`. -/
def psiP (u : ℝ) : ℝ := 3 * trN2 u - (7/5) * (2 * (97/100) + trS u)

/-- `psiB` on the region where `trN2 ≤ 0`. -/
def psiM (u : ℝ) : ℝ := -3 * trN2 u - (7/5) * (2 * (97/100) + trS u)

lemma hasDerivAt_trA (x : ℝ) : HasDerivAt trA (trAd x) x := by
  have hfun : trA = (fun u : ℝ => (-(2/25)) * Real.cos u)
      + (fun u : ℝ => (-(39/100)) * Real.sin u) := by
    funext u; simp only [Pi.add_apply, trA]; ring
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => (-(2/25)) * Real.cos u) ((-(2/25)) * (-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul (-(2/25) : ℝ)
  have h2 : HasDerivAt (fun u : ℝ => (-(39/100)) * Real.sin u) ((-(39/100)) * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul (-(39/100) : ℝ)
  have h3 := h1.add h2
  have hval : ((-(2/25)) * (-Real.sin x) + (-(39/100)) * Real.cos x) = trAd x := by
    simp only [trAd]; ring
  rw [hval] at h3
  exact h3

lemma hasDerivAt_trN2 (x : ℝ) : HasDerivAt trN2 (trN2d x) x := by
  have hfun : trN2 = (fun u : ℝ => (209/400) * Real.cos u)
      + (fun u : ℝ => (14329/10000) * Real.sin u) := by
    funext u; simp only [Pi.add_apply, trN2, trB2, trA]; ring
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => (209/400) * Real.cos u) ((209/400) * (-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul (209/400 : ℝ)
  have h3 : HasDerivAt (fun u : ℝ => (14329/10000) * Real.sin u) ((14329/10000) * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul (14329/10000 : ℝ)
  have h4 := h1.add h3
  have hval : ((209/400) * (-Real.sin x) + (14329/10000) * Real.cos x) = trN2d x := by
    simp only [trN2d]; ring
  rw [hval] at h4
  exact h4

lemma hasDerivAt_trS (x : ℝ) : HasDerivAt trS (-(3 * trA x * trAd x / trS x)) x := by
  have hA := hasDerivAt_trA x
  have hpow : HasDerivAt (fun u => (trA u)^2) (2 * trA x * trAd x) x := by
    have h := hA.pow 2
    have h3 : HasDerivAt (fun u => trA u ^ 2) (2 * trA x ^ (2-1) * trAd x) x := h
    have hval : (2 * trA x ^ (2-1) * trAd x) = 2 * trA x * trAd x := by norm_num
    rw [hval] at h3
    exact h3
  have h3 : HasDerivAt (fun u => 3 * (trA u)^2) (3 * (2 * trA x * trAd x)) x := hpow.const_mul 3
  have h4 : HasDerivAt (fun u => (97/100:ℝ)^2 - 3 * (trA u)^2) (-(3 * (2 * trA x * trAd x))) x :=
    h3.const_sub ((97/100:ℝ)^2)
  have h5 : trS = fun u : ℝ => Real.sqrt ((97/100)^2 - 3 * (trA u)^2) := rfl
  rw [h5]
  have h6 := h4.sqrt (ne_of_gt (trS_arg_pos x))
  have hv : (-(3 * (2 * trA x * trAd x))) / (2 * Real.sqrt ((97/100)^2 - 3 * (trA x)^2))
      = -(3 * trA x * trAd x / trS x) := by
    rw [show Real.sqrt ((97/100:ℝ)^2 - 3 * (trA x)^2) = trS x from rfl]
    field_simp
  rw [hv] at h6
  exact h6

lemma HasDerivAt.congr_fun' {f g : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) (hfg : f = g) :
    HasDerivAt g f' x := hfg ▸ h

lemma hasDerivAt_psiP (x : ℝ) :
    HasDerivAt psiP (3 * trN2d x + (21/5) * (trA x * trAd x / trS x)) x := by
  have hN := hasDerivAt_trN2 x
  have hS := hasDerivAt_trS x
  have h1 : HasDerivAt (fun u => 3 * trN2 u) (3 * trN2d x) x := hN.const_mul 3
  have h2 : HasDerivAt (fun u => (7/5) * (2 * (97/100) + trS u))
      ((7/5) * (-(3 * trA x * trAd x / trS x))) x :=
    (hS.const_add (2 * (97/100))).const_mul (7/5)
  have h3 := h1.sub h2
  have hval : (3 * trN2d x - (7/5) * (-(3 * trA x * trAd x / trS x)))
      = 3 * trN2d x + (21/5) * (trA x * trAd x / trS x) := by
    field_simp
    ring
  have h4 := h3.congr_deriv hval
  have hfun : (fun u => 3 * trN2 u) - (fun u => (7/5) * (2 * (97/100) + trS u)) = psiP := by
    funext u; simp only [Pi.sub_apply, psiP]
  exact HasDerivAt.congr_fun' h4 hfun

lemma hasDerivAt_psiM (x : ℝ) :
    HasDerivAt psiM (-3 * trN2d x + (21/5) * (trA x * trAd x / trS x)) x := by
  have hN := hasDerivAt_trN2 x
  have hS := hasDerivAt_trS x
  have h1 : HasDerivAt (fun u => (-3) * trN2 u) ((-3) * trN2d x) x := hN.const_mul (-3)
  have h2 : HasDerivAt (fun u => (7/5) * (2 * (97/100) + trS u))
      ((7/5) * (-(3 * trA x * trAd x / trS x))) x :=
    (hS.const_add (2 * (97/100))).const_mul (7/5)
  have h3 := h1.sub h2
  have hval : ((-3) * trN2d x - (7/5) * (-(3 * trA x * trAd x / trS x)))
      = -3 * trN2d x + (21/5) * (trA x * trAd x / trS x) := by
    field_simp
    ring
  have h4 := h3.congr_deriv hval
  have hfun : (fun u => (-3) * trN2 u) - (fun u => (7/5) * (2 * (97/100) + trS u)) = psiM := by
    funext u; simp only [Pi.sub_apply, psiM]
  exact HasDerivAt.congr_fun' h4 hfun

lemma psiB_eq_psiP {u : ℝ} (h : 0 ≤ trN2 u) : psiB u = psiP u := by
  simp only [psiB, psiP, abs_of_nonneg h]

lemma psiB_eq_psiM {u : ℝ} (h : trN2 u ≤ 0) : psiB u = psiM u := by
  simp only [psiB, psiM, abs_of_nonpos h]
  ring

lemma continuous_psiP : Continuous psiP :=
  (continuous_trN2.const_mul 3).sub
    ((continuous_trS.const_add (2 * (97/100))).const_mul (7/5))

lemma continuous_psiM : Continuous psiM :=
  (continuous_trN2.const_mul (-3)).sub
    ((continuous_trS.const_add (2 * (97/100))).const_mul (7/5))

lemma continuous_psiB : Continuous psiB := by
  have h : psiB = fun u : ℝ => 3 * |trN2 u| - (7/5) * (2 * (97/100) + trS u) := rfl
  rw [h]
  exact ((continuous_trN2.abs.const_mul 3).sub
    ((continuous_trS.const_add (2 * (97/100))).const_mul (7/5)))

/-! ## Bounds for `psiB` from bounds on `cos`, `sin` -/

lemma sq_le_max_sq {A Alo Ahi : ℝ} (h1 : Alo ≤ A) (h2 : A ≤ Ahi) :
    A^2 ≤ max (Alo^2) (Ahi^2) := by
  have h : |A| ≤ max |Alo| |Ahi| := by
    rw [abs_le]
    exact ⟨by linarith [neg_le_abs Alo, le_max_left |Alo| |Ahi|],
           by linarith [le_abs_self Ahi, le_max_right |Alo| |Ahi|]⟩
  have h2' : A^2 ≤ (max |Alo| |Ahi|)^2 := by
    rw [← sq_abs A]
    exact pow_le_pow_left₀ (abs_nonneg A) h 2
  have h3 : (max |Alo| |Ahi|)^2 = max (Alo^2) (Ahi^2) := by
    rcases le_total |Alo| |Ahi| with hh | hh
    · have hle : Alo^2 ≤ Ahi^2 := by
        nlinarith [sq_abs Alo, sq_abs Ahi, abs_nonneg Alo, abs_nonneg Ahi, hh]
      rw [max_eq_right hh, max_eq_right hle, sq_abs]
    · have hle : Ahi^2 ≤ Alo^2 := by
        nlinarith [sq_abs Alo, sq_abs Ahi, abs_nonneg Alo, abs_nonneg Ahi, hh]
      rw [max_eq_left hh, max_eq_left hle, sq_abs]
  linarith [h2', h3.le]

/-- **Negative sign of `psiB` from bounds.** -/
lemma psiB_neg_of_bounds {u Nlo Nhi M r : ℝ}
    (hN1 : Nlo ≤ trN2 u) (hN2 : trN2 u ≤ Nhi)
    (hA : (trA u)^2 ≤ M)
    (hr : 0 ≤ r) (hr2 : r^2 ≤ (97/100)^2 - 3 * M)
    (hfin : 3 * max |Nlo| |Nhi| < (7/5) * (2 * (97/100) + r)) : psiB u < 0 := by
  have hS : r ≤ trS u := by
    rw [trS, Real.le_sqrt hr (le_of_lt (trS_arg_pos u))]
    nlinarith [hr2, hA]
  have hN : |trN2 u| ≤ max |Nlo| |Nhi| := by
    rw [abs_le]
    exact ⟨by linarith [neg_le_abs Nlo, le_max_left |Nlo| |Nhi|],
           by linarith [le_abs_self Nhi, le_max_right |Nlo| |Nhi|]⟩
  rw [psiB]
  nlinarith [hS, hN, hfin]

/-- **Positive sign of `psiB` from bounds.** -/
lemma psiB_pos_of_bounds {u Nlo Nhi : ℝ}
    (hN1 : Nlo ≤ trN2 u) (hN2 : trN2 u ≤ Nhi)
    (hfin : (7/5) * (3 * (97/100)) < 3 * max Nlo (-Nhi)) : 0 < psiB u := by
  have h : max Nlo (-Nhi) ≤ |trN2 u| := by
    rw [max_le_iff]
    exact ⟨le_trans hN1 (le_abs_self _), by linarith [neg_le_abs (trN2 u)]⟩
  have hS := trS_le u
  rw [psiB]
  nlinarith [h, hS, trS_nonneg u]

/-- Bounds on `trN2` from bounds on `cos` and `sin` (the coefficients `209/400`, `14329/10000`
are positive). -/
lemma trN2_bounds {u cl ch sl sh : ℝ} (hc1 : cl ≤ Real.cos u) (hc2 : Real.cos u ≤ ch)
    (hs1 : sl ≤ Real.sin u) (hs2 : Real.sin u ≤ sh) :
    (209/400) * cl + (14329/10000) * sl ≤ trN2 u ∧
      trN2 u ≤ (209/400) * ch + (14329/10000) * sh := by
  rw [trN2_closed]
  constructor <;> nlinarith

/-- Bounds on `trA` from bounds on `cos` and `sin` (the coefficients `-2/25`, `-39/100`
are negative). -/
lemma trA_bounds {u cl ch sl sh : ℝ} (hc1 : cl ≤ Real.cos u) (hc2 : Real.cos u ≤ ch)
    (hs1 : sl ≤ Real.sin u) (hs2 : Real.sin u ≤ sh) :
    (-(2/25)) * ch + (-(39/100)) * sh ≤ trA u ∧
      trA u ≤ (-(2/25)) * cl + (-(39/100)) * sl := by
  rw [trA_closed]
  constructor <;> nlinarith

/-- **Positive sign of `psiB` from bounds on `cos` and `sin`.** -/
lemma psiB_pos_of_cos_sin_bounds {u cl ch sl sh : ℝ}
    (hc1 : cl ≤ Real.cos u) (hc2 : Real.cos u ≤ ch)
    (hs1 : sl ≤ Real.sin u) (hs2 : Real.sin u ≤ sh)
    (hfin : (7/5) * (3 * (97/100))
      < 3 * max ((209/400) * cl + (14329/10000) * sl)
              (-((209/400) * ch + (14329/10000) * sh))) : 0 < psiB u := by
  obtain ⟨h1, h2⟩ := trN2_bounds hc1 hc2 hs1 hs2
  exact psiB_pos_of_bounds h1 h2 hfin

/-- **Negative sign of `psiB` from bounds on `cos` and `sin`.** -/
lemma psiB_neg_of_cos_sin_bounds {u cl ch sl sh r : ℝ}
    (hc1 : cl ≤ Real.cos u) (hc2 : Real.cos u ≤ ch)
    (hs1 : sl ≤ Real.sin u) (hs2 : Real.sin u ≤ sh)
    (hr : 0 ≤ r)
    (hr2 : r^2 ≤ (97/100)^2 - 3 * max (((-(2/25)) * ch + (-(39/100)) * sh)^2)
                                          (((-(2/25)) * cl + (-(39/100)) * sl)^2))
    (hfin : 3 * max |(209/400) * cl + (14329/10000) * sl|
                |(209/400) * ch + (14329/10000) * sh|
      < (7/5) * (2 * (97/100) + r)) : psiB u < 0 := by
  obtain ⟨h1, h2⟩ := trN2_bounds hc1 hc2 hs1 hs2
  obtain ⟨ha1, ha2⟩ := trA_bounds hc1 hc2 hs1 hs2
  exact psiB_neg_of_bounds h1 h2 (sq_le_max_sq ha1 ha2) hr hr2 hfin

/-- **Positive sign of `psiB` at a point with known `cos` and `sin`.** -/
lemma psiB_pos_of_cos_sin {u cv sv : ℝ} (hcv : Real.cos u = cv) (hsv : Real.sin u = sv)
    (hfin : (7/5) * (3 * (97/100))
      < 3 * |(209/400) * cv + (14329/10000) * sv|) : 0 < psiB u := by
  rw [← hcv, ← hsv] at hfin
  rw [← trN2_closed u] at hfin
  rw [psiB]
  nlinarith [hfin, trS_le u, trS_nonneg u]

/-- **Negative sign of `psiB` at a point with known `cos` and `sin`.** -/
lemma psiB_neg_of_cos_sin {u cv sv r : ℝ} (hcv : Real.cos u = cv) (hsv : Real.sin u = sv)
    (hr : 0 ≤ r)
    (hr2 : r^2 ≤ (97/100)^2 - 3 * ((-(2/25)) * cv + (-(39/100)) * sv)^2)
    (hfin : 3 * |(209/400) * cv + (14329/10000) * sv|
      < (7/5) * (2 * (97/100) + r)) : psiB u < 0 := by
  rw [← hcv, ← hsv] at hfin hr2
  rw [← trN2_closed u] at hfin
  rw [← trA_closed u] at hr2
  have hS : r ≤ trS u := by
    rw [trS, Real.le_sqrt hr (le_of_lt (trS_arg_pos u))]
    nlinarith [hr2]
  rw [psiB]
  nlinarith [hS, hfin]

/-! ## Bounds for products from bounds on both factors -/

lemma mul_Icc_lower {S X Slo Shi Xlo Xhi : ℝ} (hSlo : 0 ≤ Slo) (hS1 : Slo ≤ S)
    (hS2 : S ≤ Shi) (hX1 : Xlo ≤ X) (hX2 : X ≤ Xhi) :
    min (min (Slo * Xlo) (Slo * Xhi)) (min (Shi * Xlo) (Shi * Xhi)) ≤ S * X := by
  rcases le_or_gt 0 X with h | h
  · have h1 : Slo * X ≤ S * X := mul_le_mul_of_nonneg_right hS1 h
    have h2 : Slo * Xlo ≤ Slo * X := mul_le_mul_of_nonneg_left hX1 hSlo
    have h5 : min (min (Slo * Xlo) (Slo * Xhi)) (min (Shi * Xlo) (Shi * Xhi)) ≤ Slo * Xlo :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  · have h1 : Shi * X ≤ S * X := mul_le_mul_of_nonpos_right hS2 (le_of_lt h)
    have h2 : Shi * Xlo ≤ Shi * X := mul_le_mul_of_nonneg_left hX1 (le_trans hSlo (le_trans hS1 hS2))
    have h5 : min (min (Slo * Xlo) (Slo * Xhi)) (min (Shi * Xlo) (Shi * Xhi)) ≤ Shi * Xlo :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith

lemma mul_Icc_upper {S X Slo Shi Xlo Xhi : ℝ} (hSlo : 0 ≤ Slo) (hS1 : Slo ≤ S)
    (hS2 : S ≤ Shi) (hX1 : Xlo ≤ X) (hX2 : X ≤ Xhi) :
    S * X ≤ max (max (Slo * Xlo) (Slo * Xhi)) (max (Shi * Xlo) (Shi * Xhi)) := by
  rcases le_or_gt 0 X with h | h
  · have h1 : S * X ≤ Shi * X := mul_le_mul_of_nonneg_right hS2 h
    have h2 : Shi * X ≤ Shi * Xhi := mul_le_mul_of_nonneg_left hX2 (le_trans hSlo (le_trans hS1 hS2))
    have h5 : Shi * Xhi ≤ max (max (Slo * Xlo) (Slo * Xhi)) (max (Shi * Xlo) (Shi * Xhi)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  · have h1 : S * X ≤ Slo * X := mul_le_mul_of_nonpos_right hS1 (le_of_lt h)
    have h2 : Slo * X ≤ Slo * Xhi := mul_le_mul_of_nonneg_left hX2 hSlo
    have h5 : Slo * Xhi ≤ max (max (Slo * Xlo) (Slo * Xhi)) (max (Shi * Xlo) (Shi * Xhi)) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    linarith

/-! ## Sign of the derivative -/

/-- **`psiP` is increasing** when the corner certificate is positive. -/
lemma deriv_psiP_pos {x Slo Nlo Nhi Ulo : ℝ} (hSp : 0 < Slo) (hS1 : Slo ≤ trS x)
    (hS2 : trS x ≤ 97/100) (hNd1 : Nlo ≤ trN2d x) (hNd2 : trN2d x ≤ Nhi)
    (hU : Ulo ≤ trA x * trAd x)
    (hcert : 0 < min (min (Slo * Nlo) (Slo * Nhi))
        (min ((97/100) * Nlo) ((97/100) * Nhi)) + (7/5) * Ulo) : 0 < deriv psiP x := by
  have hd : deriv psiP x = 3 * trN2d x + (21/5) * (trA x * trAd x / trS x) :=
    (hasDerivAt_psiP x).deriv
  have hpos : 0 < trS x := lt_of_lt_of_le hSp hS1
  have hrew : 3 * trN2d x + (21/5) * (trA x * trAd x / trS x)
      = (3 / trS x) * (trS x * trN2d x + (7/5) * (trA x * trAd x)) := by
    field_simp
    ring
  rw [hd, hrew]
  refine mul_pos (div_pos (by norm_num) hpos) ?_
  have h1 := mul_Icc_lower (le_of_lt hSp) hS1 hS2 hNd1 hNd2
  linarith [h1, hU, hcert]

/-- **`psiP` is decreasing** when the corner certificate is negative. -/
lemma deriv_psiP_neg {x Slo Nlo Nhi Uhi : ℝ} (hSp : 0 < Slo) (hS1 : Slo ≤ trS x)
    (hS2 : trS x ≤ 97/100) (hNd1 : Nlo ≤ trN2d x) (hNd2 : trN2d x ≤ Nhi)
    (hU : trA x * trAd x ≤ Uhi)
    (hcert : max (max (Slo * Nlo) (Slo * Nhi))
        (max ((97/100) * Nlo) ((97/100) * Nhi)) + (7/5) * Uhi < 0) : deriv psiP x < 0 := by
  have hd : deriv psiP x = 3 * trN2d x + (21/5) * (trA x * trAd x / trS x) :=
    (hasDerivAt_psiP x).deriv
  have hpos : 0 < trS x := lt_of_lt_of_le hSp hS1
  have hrew : 3 * trN2d x + (21/5) * (trA x * trAd x / trS x)
      = (3 / trS x) * (trS x * trN2d x + (7/5) * (trA x * trAd x)) := by
    field_simp
    ring
  rw [hd, hrew]
  refine mul_neg_of_pos_of_neg (div_pos (by norm_num) hpos) ?_
  have h1 := mul_Icc_upper (le_of_lt hSp) hS1 hS2 hNd1 hNd2
  linarith [h1, hU, hcert]

/-- **`psiM` is increasing** when the corner certificate is positive. -/
lemma deriv_psiM_pos {x Slo Nlo Nhi Ulo : ℝ} (hSp : 0 < Slo) (hS1 : Slo ≤ trS x)
    (hS2 : trS x ≤ 97/100) (hNd1 : Nlo ≤ trN2d x) (hNd2 : trN2d x ≤ Nhi)
    (hU : Ulo ≤ trA x * trAd x)
    (hcert : 0 < min (min (Slo * (-Nhi)) (Slo * (-Nlo)))
        (min ((97/100) * (-Nhi)) ((97/100) * (-Nlo))) + (7/5) * Ulo) : 0 < deriv psiM x := by
  have hd : deriv psiM x = -3 * trN2d x + (21/5) * (trA x * trAd x / trS x) :=
    (hasDerivAt_psiM x).deriv
  have hpos : 0 < trS x := lt_of_lt_of_le hSp hS1
  have hrew : -3 * trN2d x + (21/5) * (trA x * trAd x / trS x)
      = (3 / trS x) * (trS x * (-trN2d x) + (7/5) * (trA x * trAd x)) := by
    field_simp
    ring
  rw [hd, hrew]
  refine mul_pos (div_pos (by norm_num) hpos) ?_
  have h1 := mul_Icc_lower (le_of_lt hSp) hS1 hS2
    (by linarith : -Nhi ≤ -trN2d x) (by linarith : -trN2d x ≤ -Nlo)
  linarith [h1, hU, hcert]

/-- **`psiM` is decreasing** when the corner certificate is negative. -/
lemma deriv_psiM_neg {x Slo Nlo Nhi Uhi : ℝ} (hSp : 0 < Slo) (hS1 : Slo ≤ trS x)
    (hS2 : trS x ≤ 97/100) (hNd1 : Nlo ≤ trN2d x) (hNd2 : trN2d x ≤ Nhi)
    (hU : trA x * trAd x ≤ Uhi)
    (hcert : max (max (Slo * (-Nhi)) (Slo * (-Nlo)))
        (max ((97/100) * (-Nhi)) ((97/100) * (-Nlo))) + (7/5) * Uhi < 0) : deriv psiM x < 0 := by
  have hd : deriv psiM x = -3 * trN2d x + (21/5) * (trA x * trAd x / trS x) :=
    (hasDerivAt_psiM x).deriv
  have hpos : 0 < trS x := lt_of_lt_of_le hSp hS1
  have hrew : -3 * trN2d x + (21/5) * (trA x * trAd x / trS x)
      = (3 / trS x) * (trS x * (-trN2d x) + (7/5) * (trA x * trAd x)) := by
    field_simp
    ring
  rw [hd, hrew]
  refine mul_neg_of_pos_of_neg (div_pos (by norm_num) hpos) ?_
  have h1 := mul_Icc_upper (le_of_lt hSp) hS1 hS2
    (by linarith : -Nhi ≤ -trN2d x) (by linarith : -trN2d x ≤ -Nlo)
  linarith [h1, hU, hcert]

/-! ## Monotonicity from the derivative certificates -/

lemma strictMonoOn_congr {f g : ℝ → ℝ} {s : Set ℝ} (h : ∀ x ∈ s, f x = g x)
    (hf : StrictMonoOn f s) : StrictMonoOn g s := by
  intro x hx y hy hxy
  rw [← h x hx, ← h y hy]
  exact hf hx hy hxy

lemma strictAntiOn_congr {f g : ℝ → ℝ} {s : Set ℝ} (h : ∀ x ∈ s, f x = g x)
    (hf : StrictAntiOn f s) : StrictAntiOn g s := by
  intro x hx y hy hxy
  rw [← h x hx, ← h y hy]
  exact hf hx hy hxy

lemma strictMonoOn_psiP_of_deriv {a b Slo Nlo Nhi Ulo : ℝ} (hSp : 0 < Slo)
    (hbound : ∀ x ∈ Ioo a b, Slo ≤ trS x ∧ trS x ≤ 97/100 ∧ Nlo ≤ trN2d x ∧
      trN2d x ≤ Nhi ∧ Ulo ≤ trA x * trAd x)
    (hcert : 0 < min (min (Slo * Nlo) (Slo * Nhi))
      (min ((97/100) * Nlo) ((97/100) * Nhi)) + (7/5) * Ulo) :
    StrictMonoOn psiP (Icc a b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) continuous_psiP.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hbound x hx
  exact deriv_psiP_pos hSp h1 h2 h3 h4 h5 hcert

lemma strictAntiOn_psiP_of_deriv {a b Slo Nlo Nhi Uhi : ℝ} (hSp : 0 < Slo)
    (hbound : ∀ x ∈ Ioo a b, Slo ≤ trS x ∧ trS x ≤ 97/100 ∧ Nlo ≤ trN2d x ∧
      trN2d x ≤ Nhi ∧ trA x * trAd x ≤ Uhi)
    (hcert : max (max (Slo * Nlo) (Slo * Nhi))
      (max ((97/100) * Nlo) ((97/100) * Nhi)) + (7/5) * Uhi < 0) :
    StrictAntiOn psiP (Icc a b) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc a b) continuous_psiP.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hbound x hx
  exact deriv_psiP_neg hSp h1 h2 h3 h4 h5 hcert

lemma strictMonoOn_psiM_of_deriv {a b Slo Nlo Nhi Ulo : ℝ} (hSp : 0 < Slo)
    (hbound : ∀ x ∈ Ioo a b, Slo ≤ trS x ∧ trS x ≤ 97/100 ∧ Nlo ≤ trN2d x ∧
      trN2d x ≤ Nhi ∧ Ulo ≤ trA x * trAd x)
    (hcert : 0 < min (min (Slo * (-Nhi)) (Slo * (-Nlo)))
      (min ((97/100) * (-Nhi)) ((97/100) * (-Nlo))) + (7/5) * Ulo) :
    StrictMonoOn psiM (Icc a b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) continuous_psiM.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hbound x hx
  exact deriv_psiM_pos hSp h1 h2 h3 h4 h5 hcert

lemma strictAntiOn_psiM_of_deriv {a b Slo Nlo Nhi Uhi : ℝ} (hSp : 0 < Slo)
    (hbound : ∀ x ∈ Ioo a b, Slo ≤ trS x ∧ trS x ≤ 97/100 ∧ Nlo ≤ trN2d x ∧
      trN2d x ≤ Nhi ∧ trA x * trAd x ≤ Uhi)
    (hcert : max (max (Slo * (-Nhi)) (Slo * (-Nlo)))
      (max ((97/100) * (-Nhi)) ((97/100) * (-Nlo))) + (7/5) * Uhi < 0) :
    StrictAntiOn psiM (Icc a b) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc a b) continuous_psiM.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hbound x hx
  exact deriv_psiM_neg hSp h1 h2 h3 h4 h5 hcert

/-! ## The unique zero of a monotone function changing sign -/

lemma unique_zero_of_strictMonoOn {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hmono : StrictMonoOn f (Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ z, a < z ∧ z < b ∧ f z = 0 ∧
      (∀ u ∈ Icc a b, f u < 0 ↔ u < z) ∧ (∀ u ∈ Icc a b, f u = 0 ↔ u = z) ∧
      (∀ u ∈ Icc a b, 0 < f u ↔ z < u) := by
  set Z : Set ℝ := {u : ℝ | u ∈ Icc a b ∧ f u = 0} with hZdef
  have hclosed : IsClosed Z := by
    rw [hZdef]
    exact isClosed_Icc.inter (isClosed_eq hf continuous_const)
  have hne : Z.Nonempty := by
    have h0 : (0:ℝ) ∈ Icc (f a) (f b) := ⟨le_of_lt ha, le_of_lt hb⟩
    obtain ⟨u, hu, hfu⟩ := (intermediate_value_Icc (le_of_lt hab) hf.continuousOn) h0
    exact ⟨u, hu, hfu⟩
  have hbdd : BddBelow Z := ⟨a, fun u hu => hu.1.1⟩
  have hmem : sInf Z ∈ Z := hclosed.csInf_mem hne hbdd
  have hZ : f (sInf Z) = 0 := hmem.2
  have hgt : a < sInf Z := by
    rcases lt_or_eq_of_le hmem.1.1 with h | h
    · exact h
    · exfalso; rw [← h] at hZ; exact (ne_of_lt ha) hZ
  have hlt : sInf Z < b := by
    rcases lt_or_eq_of_le hmem.1.2 with h | h
    · exact h
    · exfalso; rw [h] at hZ; exact (ne_of_gt hb) hZ
  refine ⟨sInf Z, hgt, hlt, hZ, ?_, ?_, ?_⟩
  · intro u hu
    constructor
    · intro hfu
      by_contra hcon
      rcases lt_or_eq_of_le (not_lt.mp hcon) with h | h
      · have h1 := hmono hmem.1 hu h
        rw [hZ] at h1; linarith
      · rw [← h] at hfu; linarith
    · intro huz
      have h1 := hmono hu hmem.1 huz
      rw [hZ] at h1; exact h1
  · intro u hu
    constructor
    · intro hfu
      have hle : sInf Z ≤ u := csInf_le hbdd ⟨hu, hfu⟩
      rcases lt_or_eq_of_le hle with h | h
      · have h1 := hmono hmem.1 hu h
        rw [hZ] at h1; linarith
      · exact h.symm
    · intro huz; rw [huz]; exact hZ
  · intro u hu
    constructor
    · intro hfu
      by_contra hcon
      rcases lt_or_eq_of_le (not_lt.mp hcon) with h | h
      · have h1 := hmono hu hmem.1 h
        rw [hZ] at h1; linarith
      · rw [h] at hfu; linarith
    · intro hzu
      have h1 := hmono hmem.1 hu hzu
      rw [hZ] at h1; exact h1

lemma unique_zero_of_strictAntiOn {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hanti : StrictAntiOn f (Icc a b)) (ha : 0 < f a) (hb : f b < 0) :
    ∃ z, a < z ∧ z < b ∧ f z = 0 ∧
      (∀ u ∈ Icc a b, 0 < f u ↔ u < z) ∧ (∀ u ∈ Icc a b, f u = 0 ↔ u = z) ∧
      (∀ u ∈ Icc a b, f u < 0 ↔ z < u) := by
  have hmono : StrictMonoOn (fun u => -f u) (Icc a b) := by
    intro x hx y hy hxy
    have := hanti hx hy hxy
    linarith
  obtain ⟨z, hz1, hz2, hz3, hz4, hz5, hz6⟩ :=
    unique_zero_of_strictMonoOn (f := fun u => -f u) (by fun_prop) hab hmono
      (by linarith) (by linarith)
  refine ⟨z, hz1, hz2, by linarith, ?_, ?_, ?_⟩
  · intro u hu
    have h := hz4 u hu
    constructor
    · intro h1; exact h.mp (by linarith)
    · intro h1; linarith [h.mpr h1]
  · intro u hu
    have h := hz5 u hu
    constructor
    · intro h1; exact h.mp (by linarith)
    · intro h1; have h2 := h.mpr h1; linarith
  · intro u hu
    have h := hz6 u hu
    constructor
    · intro h1; exact h.mp (by linarith)
    · intro h1; linarith [h.mpr h1]

/-! ## The endpoint evaluations -/

/-- `psiB` is negative at `0`. -/
lemma psiB_zero_neg : psiB 0 < 0 := by
  refine psiB_neg_of_cos_sin (u := 0) (cv := 1) (sv := 0) (r := 24/25) ?_ ?_ ?_ ?_ ?_
  · simp
  · simp
  · norm_num
  · norm_num
  · norm_num

/-- `psiB` is positive at `ang (7/10)`. -/
lemma psiB_ang710_pos : 0 < psiB (ang (7/10)) := by
  have hcv : Real.cos (ang (7/10)) = 51/149 := by rw [cos_ang]; norm_num
  have hsv : Real.sin (ang (7/10)) = 140/149 := by rw [sin_ang]; norm_num
  exact psiB_pos_of_cos_sin hcv hsv (by norm_num)

/-- `psiB` is positive at `ang (9/10)`. -/
lemma psiB_ang910_pos : 0 < psiB (ang (9/10)) := by
  have hcv : Real.cos (ang (9/10)) = 19/181 := by rw [cos_ang]; norm_num
  have hsv : Real.sin (ang (9/10)) = 180/181 := by rw [sin_ang]; norm_num
  exact psiB_pos_of_cos_sin hcv hsv (by norm_num)

/-- `psiB` is negative at `ang 5`. -/
lemma psiB_ang5_neg : psiB (ang 5) < 0 := by
  have hcv : Real.cos (ang 5) = -12/13 := by rw [cos_ang]; norm_num
  have hsv : Real.sin (ang 5) = 5/13 := by rw [sin_ang]; norm_num
  exact psiB_neg_of_cos_sin (r := 24/25) hcv hsv (by norm_num) (by norm_num) (by norm_num)

/-- `psiB` is negative at `2π - ang 400`. -/
lemma psiB_low400_neg : psiB (2*Real.pi - ang 400) < 0 := by
  have hcv : Real.cos (2*Real.pi - ang 400) = -159999/160001 := by
    rw [Real.cos_two_pi_sub, cos_ang]; norm_num
  have hsv : Real.sin (2*Real.pi - ang 400) = -800/160001 := by
    rw [Real.sin_two_pi_sub, sin_ang]; norm_num
  exact psiB_neg_of_cos_sin (r := 959/1000) hcv hsv (by norm_num) (by norm_num) (by norm_num)

/-- `psiB` is positive at `2π - ang (3/2)`. -/
lemma psiB_low32_pos : 0 < psiB (2*Real.pi - ang (3/2)) := by
  have hcv : Real.cos (2*Real.pi - ang (3/2)) = -5/13 := by
    rw [Real.cos_two_pi_sub, cos_ang]; norm_num
  have hsv : Real.sin (2*Real.pi - ang (3/2)) = -12/13 := by
    rw [Real.sin_two_pi_sub, sin_ang]; norm_num
  exact psiB_pos_of_cos_sin hcv hsv (by norm_num)

/-- `psiB` is positive at `2π - ang (11/10)`. -/
lemma psiB_low1110_pos : 0 < psiB (2*Real.pi - ang (11/10)) := by
  have hcv : Real.cos (2*Real.pi - ang (11/10)) = -21/221 := by
    rw [Real.cos_two_pi_sub, cos_ang]; norm_num
  have hsv : Real.sin (2*Real.pi - ang (11/10)) = -220/221 := by
    rw [Real.sin_two_pi_sub, sin_ang]; norm_num
  exact psiB_pos_of_cos_sin hcv hsv (by norm_num)

/-- `psiB` is negative at `2π - ang (1/5)`. -/
lemma psiB_low15_neg : psiB (2*Real.pi - ang (1/5)) < 0 := by
  have hcv : Real.cos (2*Real.pi - ang (1/5)) = 12/13 := by
    rw [Real.cos_two_pi_sub, cos_ang]; norm_num
  have hsv : Real.sin (2*Real.pi - ang (1/5)) = -5/13 := by
    rw [Real.sin_two_pi_sub, sin_ang]; norm_num
  exact psiB_neg_of_cos_sin (r := 24/25) hcv hsv (by norm_num) (by norm_num) (by norm_num)

/-- `psiB` is negative at `2π`. -/
lemma psiB_two_pi_neg : psiB (2*Real.pi) < 0 := by
  refine psiB_neg_of_cos_sin (u := 2*Real.pi) (cv := 1) (sv := 0) (r := 24/25) ?_ ?_ ?_ ?_ ?_
  · simp
  · simp
  · norm_num
  · norm_num
  · norm_num

/-! ## The five gaps between the windows -/

lemma psiB_pos_G1 {u : ℝ} (hu : u ∈ Icc (ang (7/10)) (ang (9/10))) : 0 < psiB u := by
  obtain ⟨hc1, hc2⟩ :=
    cos_bounds_ang (t1 := 7/10) (t2 := 9/10) (by norm_num) (by norm_num) hu.1 hu.2
  obtain ⟨hs1, hs2⟩ :=
    sin_bounds_ang_lo (t1 := 7/10) (t2 := 9/10) (by norm_num) (by norm_num)
      (by norm_num) hu.1 hu.2
  norm_num at hc1 hc2 hs1 hs2
  exact psiB_pos_of_cos_sin_bounds hc1 hc2 hs1 hs2 (by norm_num)

lemma psiB_neg_G2a {u : ℝ} (hu : u ∈ Icc (ang 5) (ang 100)) : psiB u < 0 := by
  have hcos := cos_bounds_ang (t1 := (5 : ℝ)) (t2 := (100 : ℝ))
    (by norm_num) (by norm_num) hu.1 hu.2
  have hsin := sin_bounds_ang_hi (t1 := (5 : ℝ)) (t2 := (100 : ℝ))
    (by norm_num) (by norm_num) hu.1 hu.2
  have t1 := hcos.1
  have t2 := hcos.2
  have t3 := hsin.1
  have t4 := hsin.2
  norm_num at t1 t2 t3 t4
  exact psiB_neg_of_cos_sin_bounds (cl := -(9999 / 10001)) (ch := -(12 / 13))
    (sl := 200 / 10001) (sh := 5 / 13) (r := 24 / 25) t1 t2 t3 t4
    (by norm_num) (by norm_num) (by norm_num)

/-- For `u ∈ [ang t, 2π - ang t]` with `1 ≤ t` one has `cos u ≤ cos (ang t)`. -/
lemma psiB_proof_cos_le_cos_ang {t u : ℝ} (ht : 1 ≤ t)
    (hu1 : ang t ≤ u) (hu2 : u ≤ 2 * Real.pi - ang t) :
    Real.cos u ≤ Real.cos (ang t) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hang_pos : 0 < ang t := ang_pos htpos
  have hπ : ang t < Real.pi := ang_lt_pi htpos
  have hxlo : -(Real.pi - ang t) ≤ u - Real.pi := by linarith
  have hxhi : u - Real.pi ≤ Real.pi - ang t := by linarith
  have hxabs : |u - Real.pi| ≤ Real.pi - ang t := abs_le.mpr ⟨hxlo, hxhi⟩
  have hnn : 0 ≤ |u - Real.pi| := abs_nonneg _
  have hmem1 : |u - Real.pi| ∈ Set.Icc (0:ℝ) Real.pi := ⟨hnn, by linarith⟩
  have hmem2 : Real.pi - ang t ∈ Set.Icc (0:ℝ) Real.pi := ⟨by linarith, by linarith⟩
  have h1 : Real.cos (Real.pi - ang t) ≤ Real.cos |u - Real.pi| :=
    (Real.strictAntiOn_cos.le_iff_ge hmem2 hmem1).mpr hxabs
  rw [Real.cos_pi_sub, Real.cos_abs] at h1
  have h2 : Real.cos u = -Real.cos (u - Real.pi) := by
    rw [← Real.cos_add_pi (u - Real.pi)]
    congr 1
    ring
  linarith [h1, h2]

/-- For `u ∈ [ang t, 2π - ang t]` with `1 ≤ t` one has `|sin u| ≤ sin (ang t)`. -/
lemma psiB_proof_abs_sin_le_sin_ang {t u : ℝ} (ht : 1 ≤ t)
    (hu1 : ang t ≤ u) (hu2 : u ≤ 2 * Real.pi - ang t) :
    |Real.sin u| ≤ Real.sin (ang t) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hang_pos : 0 < ang t := ang_pos htpos
  have hπ : ang t < Real.pi := ang_lt_pi htpos
  have hge : Real.pi / 2 ≤ ang t := by
    have h := ang_le_ang ht
    rwa [ang_one] at h
  have hxlo : -(Real.pi - ang t) ≤ u - Real.pi := by linarith
  have hxhi : u - Real.pi ≤ Real.pi - ang t := by linarith
  have hxabs : |u - Real.pi| ≤ Real.pi - ang t := abs_le.mpr ⟨hxlo, hxhi⟩
  have hnn : 0 ≤ |u - Real.pi| := abs_nonneg _
  have hmem1 : |u - Real.pi| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hmem2 : Real.pi - ang t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have h1 : Real.sin |u - Real.pi| ≤ Real.sin (Real.pi - ang t) :=
    (Real.strictMonoOn_sin.le_iff_le hmem1 hmem2).mpr hxabs
  rw [Real.sin_pi_sub] at h1
  have h2 : |Real.sin u| = Real.sin |u - Real.pi| := by
    have h3 : Real.sin u = -Real.sin (u - Real.pi) := by
      rw [← Real.sin_add_pi (u - Real.pi)]
      congr 1
      ring
    rw [h3, abs_neg]
    exact Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith)
  linarith [h1, h2]

lemma psiB_neg_G2b {u : ℝ} (hu : u ∈ Icc (ang 100) (2 * Real.pi - ang 400)) : psiB u < 0 := by
  have h1 : ang 100 ≤ u := hu.1
  have hu2 : u ≤ 2 * Real.pi - ang 400 := hu.2
  have h2 : u ≤ 2 * Real.pi - ang 100 := by
    have h := ang_le_ang (show (100:ℝ) ≤ 400 by norm_num)
    linarith
  have ht : (1:ℝ) ≤ 100 := by norm_num
  have hc := psiB_proof_cos_le_cos_ang ht h1 h2
  have hsv := psiB_proof_abs_sin_le_sin_ang ht h1 h2
  rw [cos_ang] at hc
  rw [sin_ang] at hsv
  have hc' : Real.cos u ≤ (-9999/10001 : ℝ) := by
    have hnum : ((1:ℝ) - 100^2) / (1 + 100^2) = -9999/10001 := by norm_num
    linarith
  have hsv' : |Real.sin u| ≤ (200/10001 : ℝ) := by
    have hnum : (2 * (100:ℝ)) / (1 + 100^2) = 200/10001 := by norm_num
    linarith
  have hc1 : (-1:ℝ) ≤ Real.cos u := Real.neg_one_le_cos u
  obtain ⟨hs1, hs2⟩ := abs_le.mp hsv'
  have hs1' : (-200/10001 : ℝ) ≤ Real.sin u := by linarith
  have hs2' : Real.sin u ≤ (200/10001 : ℝ) := by linarith
  exact psiB_neg_of_cos_sin_bounds (cl := -1) (ch := -9999/10001)
    (sl := -200/10001) (sh := 200/10001) (r := 479/500)
    hc1 hc' hs1' hs2' (by norm_num) (by norm_num) (by norm_num)

lemma psiB_pos_G3 {u : ℝ} (hu : u ∈ Icc (2 * Real.pi - ang (3/2)) (2 * Real.pi - ang (11/10))) :
    0 < psiB u := by
  have hcos := cos_bounds_ang_low (t1 := 11/10) (t2 := 3/2) (u := u)
    (by norm_num) (by norm_num) hu.1 hu.2
  have hsin := sin_bounds_ang_hi (t1 := 11/10) (t2 := 3/2) (u := 2 * Real.pi - u)
    (by norm_num) (by norm_num) (by linarith [hu.2]) (by linarith [hu.1])
  rw [Real.sin_two_pi_sub] at hsin
  have hc1 : (-5/13 : ℝ) ≤ Real.cos u := by
    have h1 := hcos.1
    have h2 : (1 - (3/2 : ℝ)^2) / (1 + (3/2)^2) = -5/13 := by norm_num
    linarith
  have hc2 : Real.cos u ≤ (-21/221 : ℝ) := by
    have h1 := hcos.2
    have h2 : (1 - (11/10 : ℝ)^2) / (1 + (11/10)^2) = -21/221 := by norm_num
    linarith
  have hs1 : (-220/221 : ℝ) ≤ Real.sin u := by
    have h1 := hsin.2
    have h2 : 2 * (11/10 : ℝ) / (1 + (11/10)^2) = 220/221 := by norm_num
    linarith
  have hs2 : Real.sin u ≤ (-12/13 : ℝ) := by
    have h1 := hsin.1
    have h2 : 2 * (3/2 : ℝ) / (1 + (3/2)^2) = 12/13 := by norm_num
    linarith
  exact psiB_pos_of_cos_sin_bounds hc1 hc2 hs1 hs2 (by norm_num)

lemma psiB_neg_G4 {u : ℝ} (hu : u ∈ Icc (2 * Real.pi - ang (1/5)) (2 * Real.pi)) : psiB u < 0 := by
  obtain ⟨hu1, hu2⟩ := hu
  have h15pos : (0:ℝ) < 1/5 := by norm_num
  have h15lt : (1:ℝ)/5 < 1 := by norm_num
  have hv1 : 0 ≤ 2 * Real.pi - u := by linarith
  have hv2 : 2 * Real.pi - u ≤ ang (1/5) := by linarith
  have hang_lt_pi : ang (1/5) < Real.pi := ang_lt_pi h15pos
  have hang_le_half : ang (1/5) ≤ Real.pi / 2 := le_of_lt (ang_lt_pi_div_two h15pos h15lt)
  have hf_cos : ang (1/5) ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨le_of_lt (ang_pos h15pos), le_of_lt hang_lt_pi⟩
  have hv_cos : 2 * Real.pi - u ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨hv1, le_trans hv2 (le_of_lt hang_lt_pi)⟩
  have hf_sin : ang (1/5) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [ang_pos h15pos], hang_le_half⟩
  have hv_sin : 2 * Real.pi - u ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [Real.pi_pos], le_trans hv2 hang_le_half⟩
  have hcosang : Real.cos (ang (1/5)) = 12/13 := by rw [cos_ang]; norm_num
  have hsinang : Real.sin (ang (1/5)) = 5/13 := by rw [sin_ang]; norm_num
  have hc1 : (12:ℝ)/13 ≤ Real.cos u := by
    rw [← hcosang, ← Real.cos_two_pi_sub u]
    exact (Real.strictAntiOn_cos.le_iff_ge hf_cos hv_cos).mpr hv2
  have hc2 : Real.cos u ≤ 1 := Real.cos_le_one u
  have hs2 : Real.sin u ≤ 0 := by
    have h0 : 0 ≤ Real.sin (2 * Real.pi - u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hv1 (le_trans hv2 (le_of_lt hang_lt_pi))
    rw [Real.sin_two_pi_sub] at h0
    linarith
  have hs1 : (-5:ℝ)/13 ≤ Real.sin u := by
    have h1 : Real.sin (2 * Real.pi - u) ≤ 5/13 := by
      rw [← hsinang]
      exact (Real.strictMonoOn_sin.le_iff_le hv_sin hf_sin).mpr hv2
    rw [Real.sin_two_pi_sub] at h1
    linarith
  exact psiB_neg_of_cos_sin_bounds (u := u) (cl := 12/13) (ch := 1) (sl := (-5:ℝ)/13)
    (sh := 0) (r := 24/25) hc1 hc2 hs1 hs2 (by norm_num) (by norm_num) (by norm_num)

/-! ## The four windows -/

lemma bounds_W1 {u : ℝ} (hu : u ∈ Icc 0 (ang (7/10))) :
    (51/149 : ℝ) ≤ Real.cos u ∧ Real.cos u ≤ 1 ∧ (0:ℝ) ≤ Real.sin u ∧
      Real.sin u ≤ 140/149 := by
  have hpos : (0:ℝ) < 7/10 := by norm_num
  have hlt1 : (7:ℝ)/10 < 1 := by norm_num
  have hang_lt_pi : ang (7/10) < Real.pi := ang_lt_pi hpos
  have hang_le_half : ang (7/10) ≤ Real.pi/2 := le_of_lt (ang_lt_pi_div_two hpos hlt1)
  have hmem : ang (7/10) ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨le_of_lt (ang_pos hpos), le_of_lt hang_lt_pi⟩
  have humem : u ∈ Set.Icc (0:ℝ) Real.pi := ⟨hu.1, le_trans hu.2 (le_of_lt hang_lt_pi)⟩
  have hmem2 : ang (7/10) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [ang_pos hpos], hang_le_half⟩
  have humem2 : u ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [hu.1, Real.pi_pos], le_trans hu.2 hang_le_half⟩
  refine ⟨?_, Real.cos_le_one u, ?_, ?_⟩
  · have h := (Real.strictAntiOn_cos.le_iff_ge hmem humem).mpr hu.2
    rw [cos_ang] at h
    norm_num at h
    exact h
  · exact Real.sin_nonneg_of_nonneg_of_le_pi hu.1 (le_trans hu.2 (le_of_lt hang_lt_pi))
  · have h := (Real.strictMonoOn_sin.le_iff_le humem2 hmem2).mpr hu.2
    rw [sin_ang] at h
    norm_num at h
    exact h

lemma psiB_window1 : ∃ z : ℝ, 0 < z ∧ z < ang (7/10) ∧ psiB z = 0 ∧
    (∀ u ∈ Icc 0 (ang (7/10)), psiB u < 0 ↔ u < z) ∧
    (∀ u ∈ Icc 0 (ang (7/10)), psiB u = 0 ↔ u = z) ∧
    (∀ u ∈ Icc 0 (ang (7/10)), 0 < psiB u ↔ z < u) := by
  have hNpos : ∀ u ∈ Icc 0 (ang (7/10)), 0 < trN2 u := by
    intro u hu
    obtain ⟨hc1, hc2, hs1, hs2⟩ := bounds_W1 hu
    obtain ⟨h1, h2⟩ := trN2_bounds hc1 hc2 hs1 hs2
    nlinarith
  have hp : StrictMonoOn psiP (Icc 0 (ang (7/10))) := by
    refine strictMonoOn_psiP_of_deriv (Slo := 117/200) (Nlo := -721/1490000)
      (Nhi := 14329/10000) (Ulo := 44319/27751250) (by norm_num) ?_ (by norm_num)
    intro x hx
    obtain ⟨hc1, hc2, hs1, hs2⟩ := bounds_W1 ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    obtain ⟨ha1, ha2⟩ := trA_bounds hc1 hc2 hs1 hs2
    refine ⟨?_, trS_le x, ?_, ?_, ?_⟩
    · rw [trS, Real.le_sqrt (by norm_num) (le_of_lt (trS_arg_pos x))]
      nlinarith [ha1, ha2, sq_nonneg (trA x)]
    · rw [trN2d]; nlinarith [hc1, hc2, hs1, hs2]
    · rw [trN2d]; nlinarith [hc1, hc2, hs1, hs2]
    · rw [trAd]; nlinarith [ha1, ha2, hc1, hc2, hs1, hs2]
  have hmono : StrictMonoOn psiB (Icc 0 (ang (7/10))) :=
    strictMonoOn_congr (fun u hu => (psiB_eq_psiP (le_of_lt (hNpos u hu))).symm) hp
  exact unique_zero_of_strictMonoOn continuous_psiB (ang_pos (by norm_num)) hmono
    psiB_zero_neg psiB_ang710_pos

lemma bounds_W2 {u : ℝ} (hu : u ∈ Icc (ang (9/10)) (ang 5)) :
    (-(12/13) : ℝ) ≤ Real.cos u ∧ Real.cos u ≤ 19/181 ∧ (5/13 : ℝ) ≤ Real.sin u ∧
      Real.sin u ≤ 1 := by
  obtain ⟨hc1, hc2⟩ := cos_bounds_ang (t1 := 9/10) (t2 := 5) (by norm_num) (by norm_num)
    hu.1 hu.2
  obtain ⟨hs1, hs2⟩ := sin_bounds_ang_mid (t1 := 9/10) (t2 := 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hu.1 hu.2
  norm_num at hc1 hc2 hs1 hs2
  exact ⟨hc1, hc2, hs1, hs2⟩

lemma psiB_window2 : ∃ z : ℝ, ang (9/10) < z ∧ z < ang 5 ∧ psiB z = 0 ∧
    (∀ u ∈ Icc (ang (9/10)) (ang 5), psiB u < 0 ↔ z < u) ∧
    (∀ u ∈ Icc (ang (9/10)) (ang 5), psiB u = 0 ↔ u = z) ∧
    (∀ u ∈ Icc (ang (9/10)) (ang 5), 0 < psiB u ↔ u < z) := by
  have hNpos : ∀ u ∈ Icc (ang (9/10)) (ang 5), 0 < trN2 u := by
    intro u hu
    obtain ⟨hc1, hc2, hs1, hs2⟩ := bounds_W2 hu
    obtain ⟨h1, h2⟩ := trN2_bounds hc1 hc2 hs1 hs2
    nlinarith
  have hp : StrictAntiOn psiP (Icc (ang (9/10)) (ang 5)) := by
    refine strictAntiOn_psiP_of_deriv (Slo := 681/1000) (Nlo := -239873/130000)
      (Nhi := -594681/11765000) (Uhi := 17255923/4258930000) (by norm_num) ?_ (by norm_num)
    intro x hx
    obtain ⟨hc1, hc2, hs1, hs2⟩ := bounds_W2 ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    obtain ⟨ha1, ha2⟩ := trA_bounds hc1 hc2 hs1 hs2
    refine ⟨?_, trS_le x, ?_, ?_, ?_⟩
    · rw [trS, Real.le_sqrt (by norm_num) (le_of_lt (trS_arg_pos x))]
      nlinarith [ha1, ha2, sq_nonneg (trA x)]
    · rw [trN2d]; nlinarith [hc1, hc2, hs1, hs2]
    · rw [trN2d]; nlinarith [hc1, hc2, hs1, hs2]
    · rw [trAd]; nlinarith [ha1, ha2, hc1, hc2, hs1, hs2]
  have hanti : StrictAntiOn psiB (Icc (ang (9/10)) (ang 5)) :=
    strictAntiOn_congr (fun u hu => (psiB_eq_psiP (le_of_lt (hNpos u hu))).symm) hp
  obtain ⟨z, hz1, hz2, hz3, hz4, hz5, hz6⟩ := unique_zero_of_strictAntiOn continuous_psiB
    (ang_lt_ang (show (9/10 : ℝ) < 5 by norm_num)) hanti psiB_ang910_pos psiB_ang5_neg
  exact ⟨z, hz1, hz2, hz3, hz6, hz5, hz4⟩

lemma bounds_W3 {u : ℝ} (hu : u ∈ Icc (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2))) :
    (-159999/160001 : ℝ) ≤ Real.cos u ∧ Real.cos u ≤ (-5/13 : ℝ) ∧
      (-(12/13) : ℝ) ≤ Real.sin u ∧ Real.sin u ≤ (-(800/160001) : ℝ) := by
  obtain ⟨hc1, hc2⟩ := cos_bounds_ang_low (t1 := 3/2) (t2 := 400) (by norm_num) (by norm_num)
    hu.1 hu.2
  have hs := sin_bounds_ang_hi (t1 := 3/2) (t2 := 400) (u := 2 * Real.pi - u) (by norm_num)
    (by norm_num) (by linarith [hu.2]) (by linarith [hu.1])
  rw [Real.sin_two_pi_sub] at hs
  have h1 : (1 - (400:ℝ)^2) / (1 + 400^2) = -159999/160001 := by norm_num
  have h2 : (1 - ((3:ℝ)/2)^2) / (1 + ((3:ℝ)/2)^2) = -5/13 := by norm_num
  have h3 : 2 * (400:ℝ) / (1 + 400^2) = 800/160001 := by norm_num
  have h4 : 2 * ((3:ℝ)/2) / (1 + ((3:ℝ)/2)^2) = 12/13 := by norm_num
  rw [h1] at hc1; rw [h2] at hc2; rw [h3] at hs; rw [h4] at hs
  exact ⟨hc1, hc2, by linarith [hs.2], by linarith [hs.1]⟩

lemma psiB_window3 : ∃ z : ℝ, 2 * Real.pi - ang 400 < z ∧ z < 2 * Real.pi - ang (3/2) ∧
    psiB z = 0 ∧
    (∀ u ∈ Icc (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2)), psiB u < 0 ↔ u < z) ∧
    (∀ u ∈ Icc (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2)), psiB u = 0 ↔ u = z) ∧
    (∀ u ∈ Icc (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2)), 0 < psiB u ↔ z < u) := by
  have hNneg : ∀ u ∈ Icc (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2)), trN2 u < 0 := by
    intro u hu
    obtain ⟨hc1, hc2, hs1, hs2⟩ := bounds_W3 hu
    obtain ⟨h1, h2⟩ := trN2_bounds hc1 hc2 hs1 hs2
    nlinarith
  have hp : StrictMonoOn psiM (Icc (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2))) := by
    refine strictMonoOn_psiM_of_deriv (Slo := 3/5) (Nlo := -2288445671/1600010000)
      (Nhi := -1789/26000) (Ulo := 16843959/6760042250) (by norm_num) ?_ (by norm_num)
    intro x hx
    obtain ⟨hc1, hc2, hs1, hs2⟩ := bounds_W3 ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    obtain ⟨ha1, ha2⟩ := trA_bounds hc1 hc2 hs1 hs2
    refine ⟨?_, trS_le x, ?_, ?_, ?_⟩
    · rw [trS, Real.le_sqrt (by norm_num) (le_of_lt (trS_arg_pos x))]
      nlinarith [ha1, ha2, sq_nonneg (trA x)]
    · rw [trN2d]; nlinarith [hc1, hc2, hs1, hs2]
    · rw [trN2d]; nlinarith [hc1, hc2, hs1, hs2]
    · rw [trAd]; nlinarith [ha1, ha2, hc1, hc2, hs1, hs2]
  have hmono : StrictMonoOn psiB (Icc (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2))) :=
    strictMonoOn_congr (fun u hu => (psiB_eq_psiM (le_of_lt (hNneg u hu))).symm) hp
  refine unique_zero_of_strictMonoOn continuous_psiB ?_ hmono psiB_low400_neg psiB_low32_pos
  have h1 := ang_lt_ang (show (3/2 : ℝ) < 400 by norm_num)
  linarith

lemma bounds_W4 {u : ℝ}
    (hu : u ∈ Icc (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5))) :
    (-21/221 : ℝ) ≤ Real.cos u ∧ Real.cos u ≤ 12/13 ∧ (-1:ℝ) ≤ Real.sin u ∧
      Real.sin u ≤ (-(5/13) : ℝ) := by
  obtain ⟨hc1, hc2⟩ := cos_bounds_ang_low (t1 := 1/5) (t2 := 11/10) (by norm_num) (by norm_num)
    hu.1 hu.2
  have hs := sin_bounds_ang_mid (t1 := 1/5) (t2 := 11/10) (u := 2 * Real.pi - u) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by linarith [hu.2]) (by linarith [hu.1])
  rw [Real.sin_two_pi_sub] at hs
  have h1 : (1 - ((11:ℝ)/10)^2) / (1 + ((11:ℝ)/10)^2) = -21/221 := by norm_num
  have h2 : (1 - ((1:ℝ)/5)^2) / (1 + ((1:ℝ)/5)^2) = 12/13 := by norm_num
  have h4 : min (2 * ((1:ℝ)/5) / (1 + ((1:ℝ)/5)^2)) (2 * ((11:ℝ)/10) / (1 + ((11:ℝ)/10)^2))
      = 5/13 := by norm_num
  rw [h1] at hc1; rw [h2] at hc2; rw [h4] at hs
  exact ⟨hc1, hc2, by linarith [hs.2], by linarith [hs.1]⟩

lemma psiB_window4 : ∃ z : ℝ, 2 * Real.pi - ang (11/10) < z ∧ z < 2 * Real.pi - ang (1/5) ∧
    psiB z = 0 ∧
    (∀ u ∈ Icc (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5)), psiB u < 0 ↔ z < u) ∧
    (∀ u ∈ Icc (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5)), psiB u = 0 ↔ u = z) ∧
    (∀ u ∈ Icc (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5)), 0 < psiB u ↔ u < z) := by
  have hNneg : ∀ u ∈ Icc (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5)), trN2 u < 0 := by
    intro u hu
    obtain ⟨hc1, hc2, hs1, hs2⟩ := bounds_W4 hu
    obtain ⟨h1, h2⟩ := trN2_bounds hc1 hc2 hs1 hs2
    nlinarith
  have hp : StrictAntiOn psiM (Icc (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5))) := by
    refine strictAntiOn_psiM_of_deriv (Slo := 683/1000) (Nlo := 8951/138125)
      (Nhi := 239873/130000) (Uhi := 1221393/488410000) (by norm_num) ?_ (by norm_num)
    intro x hx
    obtain ⟨hc1, hc2, hs1, hs2⟩ := bounds_W4 ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    obtain ⟨ha1, ha2⟩ := trA_bounds hc1 hc2 hs1 hs2
    refine ⟨?_, trS_le x, ?_, ?_, ?_⟩
    · rw [trS, Real.le_sqrt (by norm_num) (le_of_lt (trS_arg_pos x))]
      nlinarith [ha1, ha2, sq_nonneg (trA x)]
    · rw [trN2d]; nlinarith [hc1, hc2, hs1, hs2]
    · rw [trN2d]; nlinarith [hc1, hc2, hs1, hs2]
    · rw [trAd]; nlinarith [ha1, ha2, hc1, hc2, hs1, hs2]
  have hanti : StrictAntiOn psiB (Icc (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5))) :=
    strictAntiOn_congr (fun u hu => (psiB_eq_psiM (le_of_lt (hNneg u hu))).symm) hp
  obtain ⟨z, hz1, hz2, hz3, hz4, hz5, hz6⟩ := unique_zero_of_strictAntiOn continuous_psiB
    (by have h1 := ang_lt_ang (show (1/5 : ℝ) < 11/10 by norm_num); linarith)
    hanti psiB_low1110_pos psiB_low15_neg
  exact ⟨z, hz1, hz2, hz3, hz6, hz5, hz4⟩

/-! ## Ordering of the pieces -/

lemma ang100_add_ang400_lt_two_pi : ang 100 + ang 400 < 2 * Real.pi := by
  have h1 : ang 100 < Real.pi := ang_lt_pi (by norm_num)
  have h2 : ang 400 < Real.pi := ang_lt_pi (by norm_num)
  linarith

lemma ang100_lt_two_pi_sub_ang400 : ang 100 < 2 * Real.pi - ang 400 := by
  linarith [ang100_add_ang400_lt_two_pi]

/-- Every point of `[0, 2π]` lies in one of the nine pieces. -/
lemma cover9 {u : ℝ} (hu : u ∈ Icc 0 (2 * Real.pi)) :
    u ∈ Icc 0 (ang (7/10)) ∨ u ∈ Icc (ang (7/10)) (ang (9/10)) ∨
    u ∈ Icc (ang (9/10)) (ang 5) ∨ u ∈ Icc (ang 5) (ang 100) ∨
    u ∈ Icc (ang 100) (2 * Real.pi - ang 400) ∨
    u ∈ Icc (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2)) ∨
    u ∈ Icc (2 * Real.pi - ang (3/2)) (2 * Real.pi - ang (11/10)) ∨
    u ∈ Icc (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5)) ∨
    u ∈ Icc (2 * Real.pi - ang (1/5)) (2 * Real.pi) := by
  rcases le_or_gt u (ang (7/10)) with h | h
  · left; exact ⟨hu.1, h⟩
  · rcases le_or_gt u (ang (9/10)) with h2 | h2
    · right; left; exact ⟨le_of_lt h, h2⟩
    · rcases le_or_gt u (ang 5) with h3 | h3
      · right; right; left; exact ⟨le_of_lt h2, h3⟩
      · rcases le_or_gt u (ang 100) with h4 | h4
        · right; right; right; left; exact ⟨le_of_lt h3, h4⟩
        · rcases le_or_gt u (2 * Real.pi - ang 400) with h5 | h5
          · right; right; right; right; left; exact ⟨le_of_lt h4, h5⟩
          · rcases le_or_gt u (2 * Real.pi - ang (3/2)) with h6 | h6
            · right; right; right; right; right; left; exact ⟨le_of_lt h5, h6⟩
            · rcases le_or_gt u (2 * Real.pi - ang (11/10)) with h7 | h7
              · right; right; right; right; right; right; left
                exact ⟨le_of_lt h6, h7⟩
              · rcases le_or_gt u (2 * Real.pi - ang (1/5)) with h8 | h8
                · right; right; right; right; right; right; right; left
                  exact ⟨le_of_lt h7, h8⟩
                · right; right; right; right; right; right; right; right
                  exact ⟨le_of_lt h8, hu.2⟩

/-- Membership in the open union, as a disjunction of the local conditions. -/
lemma mem_open_union_iff {u z1 z2 z3 z4 : ℝ} (hu1 : 0 ≤ u) (hu2 : u ≤ 2 * Real.pi) :
    (u ∈ Ico (0:ℝ) z1 ∪ Ioo z2 z3 ∪ Ioc z4 (2 * Real.pi) ↔
      (u < z1 ∨ (z2 < u ∧ u < z3) ∨ z4 < u)) := by
  simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioo, Set.mem_Ioc]
  constructor
  · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact Or.inl h2
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr h1)
  · intro hd
    rcases hd with hd | hd
    · exact Or.inl (Or.inl ⟨hu1, hd⟩)
    · rcases hd with hd | hd
      · exact Or.inl (Or.inr hd)
      · exact Or.inr ⟨hd, hu2⟩

/-- Membership in the closed union, as a disjunction of the local conditions. -/
lemma mem_closed_union_iff {u z1 z2 z3 z4 : ℝ} (hu1 : 0 ≤ u) (hu2 : u ≤ 2 * Real.pi) :
    (u ∈ Icc (0:ℝ) z1 ∪ Icc z2 z3 ∪ Icc z4 (2 * Real.pi) ↔
      (u ≤ z1 ∨ (z2 ≤ u ∧ u ≤ z3) ∨ z4 ≤ u)) := by
  simp only [Set.mem_union, Set.mem_Icc]
  constructor
  · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact Or.inl h2
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr h1)
  · intro hd
    rcases hd with hd | hd
    · exact Or.inl (Or.inl ⟨hu1, hd⟩)
    · rcases hd with hd | hd
      · exact Or.inl (Or.inr hd)
      · exact Or.inr ⟨hd, hu2⟩

/-! ## The main theorem -/

theorem psiB_shape :
    (0 < Work.BoxShrink.PinchOff.RefuteDrop.uB1 ∧
        Work.BoxShrink.PinchOff.RefuteDrop.uB1 < Work.BoxShrink.PinchOff.RefuteDrop.uB2 ∧
        Work.BoxShrink.PinchOff.RefuteDrop.uB2 < Work.BoxShrink.PinchOff.RefuteDrop.uB3 ∧
        Work.BoxShrink.PinchOff.RefuteDrop.uB3 < Work.BoxShrink.PinchOff.RefuteDrop.uB4 ∧
        Work.BoxShrink.PinchOff.RefuteDrop.uB4 < 2 * Real.pi) ∧
      (Work.BoxShrink.PinchOff.RefuteDrop.uB1 ∈ Set.Ioo (0:ℝ) (Work.BoxShrink.PinchOff.RefuteDrop.ang (7/10)) ∧
        Work.BoxShrink.PinchOff.RefuteDrop.uB2 ∈ Set.Ioo (Work.BoxShrink.PinchOff.RefuteDrop.ang (9/10)) (Work.BoxShrink.PinchOff.RefuteDrop.ang 5) ∧
        Work.BoxShrink.PinchOff.RefuteDrop.uB3 ∈ Set.Ioo (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang 400) (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (3/2)) ∧
        Work.BoxShrink.PinchOff.RefuteDrop.uB4 ∈ Set.Ioo (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (11/10)) (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (1/5))) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (Work.BoxShrink.PinchOff.RefuteDrop.psiB u ≤ 0 ↔
          u ∈ Set.Icc (0:ℝ) Work.BoxShrink.PinchOff.RefuteDrop.uB1 ∪ Set.Icc Work.BoxShrink.PinchOff.RefuteDrop.uB2 Work.BoxShrink.PinchOff.RefuteDrop.uB3 ∪ Set.Icc Work.BoxShrink.PinchOff.RefuteDrop.uB4 (2 * Real.pi))) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (Work.BoxShrink.PinchOff.RefuteDrop.psiB u < 0 ↔
          u ∈ Set.Ico (0:ℝ) Work.BoxShrink.PinchOff.RefuteDrop.uB1 ∪ Set.Ioo Work.BoxShrink.PinchOff.RefuteDrop.uB2 Work.BoxShrink.PinchOff.RefuteDrop.uB3 ∪ Set.Ioc Work.BoxShrink.PinchOff.RefuteDrop.uB4 (2 * Real.pi))) := by
  obtain ⟨z1, hz1lo, hz1hi, hz1z, hz1lt, hz1eq, hz1gt⟩ := psiB_window1
  obtain ⟨z2, hz2lo, hz2hi, hz2z, hz2lt, hz2eq, hz2gt⟩ := psiB_window2
  obtain ⟨z3, hz3lo, hz3hi, hz3z, hz3lt, hz3eq, hz3gt⟩ := psiB_window3
  obtain ⟨z4, hz4lo, hz4hi, hz4z, hz4lt, hz4eq, hz4gt⟩ := psiB_window4
  have e1 : ang (7/10) < ang (9/10) := ang_lt_ang (by norm_num)
  have e2 : ang (9/10) < ang 5 := ang_lt_ang (by norm_num)
  have e3 : ang 5 < ang 100 := ang_lt_ang (by norm_num)
  have e4 : ang 100 < 2 * Real.pi - ang 400 := ang100_lt_two_pi_sub_ang400
  have e5 : 2 * Real.pi - ang 400 < 2 * Real.pi - ang (3/2) := by
    have h := ang_lt_ang (show (3/2 : ℝ) < 400 by norm_num); linarith
  have e6 : 2 * Real.pi - ang (3/2) < 2 * Real.pi - ang (11/10) := by
    have h := ang_lt_ang (show (11/10 : ℝ) < 3/2 by norm_num); linarith
  have e7 : 2 * Real.pi - ang (11/10) < 2 * Real.pi - ang (1/5) := by
    have h := ang_lt_ang (show (1/5 : ℝ) < 11/10 by norm_num); linarith
  have e8 : 2 * Real.pi - ang (1/5) < 2 * Real.pi := by
    have h := ang_pos (show (0 : ℝ) < 1/5 by norm_num); linarith
  have huB1 : uB1 = z1 := by
    unfold uB1
    have hset : {u : ℝ | u ∈ Set.Icc 0 (ang (7/10)) ∧ psiB u = 0} = {z1} := by
      ext u; constructor
      · rintro ⟨hu, h0⟩; exact (hz1eq u hu).mp h0
      · rintro rfl; exact ⟨⟨le_of_lt hz1lo, le_of_lt hz1hi⟩, hz1z⟩
    rw [hset]; simp
  have huB2 : uB2 = z2 := by
    unfold uB2
    have hset : {u : ℝ | u ∈ Set.Icc (ang (9/10)) (ang 5) ∧ psiB u = 0} = {z2} := by
      ext u; constructor
      · rintro ⟨hu, h0⟩; exact (hz2eq u hu).mp h0
      · rintro rfl; exact ⟨⟨le_of_lt hz2lo, le_of_lt hz2hi⟩, hz2z⟩
    rw [hset]; simp
  have huB3 : uB3 = z3 := by
    unfold uB3
    have hset : {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang 400) (2 * Real.pi - ang (3/2)) ∧
        psiB u = 0} = {z3} := by
      ext u; constructor
      · rintro ⟨hu, h0⟩; exact (hz3eq u hu).mp h0
      · rintro rfl; exact ⟨⟨le_of_lt hz3lo, le_of_lt hz3hi⟩, hz3z⟩
    rw [hset]; simp
  have huB4 : uB4 = z4 := by
    unfold uB4
    have hset : {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang (11/10)) (2 * Real.pi - ang (1/5)) ∧
        psiB u = 0} = {z4} := by
      ext u; constructor
      · rintro ⟨hu, h0⟩; exact (hz4eq u hu).mp h0
      · rintro rfl; exact ⟨⟨le_of_lt hz4lo, le_of_lt hz4hi⟩, hz4z⟩
    rw [hset]; simp
  rw [huB1, huB2, huB3, huB4]
  have key_lt : ∀ u : ℝ, u ∈ Icc (0:ℝ) (2 * Real.pi) →
      (psiB u < 0 ↔ (u < z1 ∨ (z2 < u ∧ u < z3) ∨ z4 < u)) := by
    intro u hu
    rcases cover9 hu with h | h | h | h | h | h | h | h | h
    · obtain ⟨h1, h2⟩ := h
      rw [(hz1lt u ⟨h1, h2⟩)]
      constructor
      · intro h3; exact Or.inl h3
      · intro hd
        rcases hd with hd | hd
        · exact hd
        · rcases hd with hd | hd
          · exact absurd hd.1 (by linarith)
          · exact absurd hd (by linarith [h2, e1, e2, e3, e4, e5, e6, e7, hz4lo])
    · obtain ⟨h1, h2⟩ := h
      constructor
      · intro h3; exact absurd h3 (not_lt.mpr (le_of_lt (psiB_pos_G1 ⟨h1, h2⟩)))
      · intro hd
        rcases hd with hd | hd
        · exact absurd hd (by linarith [h1, hz1hi])
        · rcases hd with hd | hd
          · exact absurd hd.1 (by linarith [h2, hz2lo])
          · exact absurd hd (by linarith [h2, e2, e3, e4, e5, e6, hz4lo])
    · obtain ⟨h1, h2⟩ := h
      rw [(hz2lt u ⟨h1, h2⟩)]
      constructor
      · intro h3; exact Or.inr (Or.inl ⟨h3, by linarith [h2, e3, e4, e5, hz3lo]⟩)
      · intro hd
        rcases hd with hd | hd
        · exact absurd hd (by linarith [h1, hz1hi, e1, hz2lo])
        · rcases hd with hd | hd
          · exact hd.1
          · exact absurd hd (by linarith [h2, e3, e4, e5, e6, hz4lo])
    · obtain ⟨h1, h2⟩ := h
      constructor
      · intro _
        exact Or.inr (Or.inl ⟨by linarith [h1, e2, hz2lo],
          by linarith [h2, e3, e4, e5, hz3lo]⟩)
      · intro _; exact psiB_neg_G2a ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := h
      constructor
      · intro _
        exact Or.inr (Or.inl ⟨by linarith [h1, e2, e3, hz2lo],
          by linarith [h2, e5, hz3lo]⟩)
      · intro _; exact psiB_neg_G2b ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := h
      rw [(hz3lt u ⟨h1, h2⟩)]
      constructor
      · intro h3; exact Or.inr (Or.inl ⟨by linarith [h1, e2, e3, e4, hz2lo], h3⟩)
      · intro hd
        rcases hd with hd | hd
        · exact absurd hd (by linarith [h1, e4, e5, hz3lo])
        · rcases hd with hd | hd
          · exact hd.2
          · exact absurd hd (by linarith [h2, e6, e7, hz4lo])
    · obtain ⟨h1, h2⟩ := h
      constructor
      · intro h3; exact absurd h3 (not_lt.mpr (le_of_lt (psiB_pos_G3 ⟨h1, h2⟩)))
      · intro hd
        rcases hd with hd | hd
        · exact absurd hd (by linarith [h1, hz1hi, e1, e2, e3, e4, e5, hz3lo])
        · rcases hd with hd | hd
          · exact absurd hd.2 (by linarith [h1, e6, hz3hi])
          · exact absurd hd (by linarith [h2, e7, hz4lo])
    · obtain ⟨h1, h2⟩ := h
      rw [(hz4lt u ⟨h1, h2⟩)]
      constructor
      · intro h3; exact Or.inr (Or.inr h3)
      · intro hd
        rcases hd with hd | hd
        · exact absurd hd (by linarith [h1, hz1hi, e1, e2, e3, e4, e5, e6, e7, hz4lo])
        · rcases hd with hd | hd
          · exact absurd hd.2 (by linarith [h1, e6, e7, hz4lo])
          · exact hd
    · obtain ⟨h1, h2⟩ := h
      constructor
      · intro _
        exact Or.inr (Or.inr (by linarith [h1, e7, hz4lo]))
      · intro _; exact psiB_neg_G4 ⟨h1, h2⟩
  have key_zero : ∀ u : ℝ, u ∈ Icc (0:ℝ) (2 * Real.pi) →
      psiB u = 0 → (u ≤ z1 ∨ (z2 ≤ u ∧ u ≤ z3) ∨ z4 ≤ u) := by
    intro u hu h0
    rcases cover9 hu with h | h | h | h | h | h | h | h | h
    · obtain ⟨h1, h2⟩ := h
      exact Or.inl (le_of_eq ((hz1eq u ⟨h1, h2⟩).mp h0))
    · exact absurd h0 (ne_of_gt (psiB_pos_G1 h))
    · obtain ⟨h1, h2⟩ := h
      exact Or.inr (Or.inl ⟨le_of_eq ((hz2eq u ⟨h1, h2⟩).mp h0).symm,
        by linarith [h2, e3, e4, e5, hz3lo]⟩)
    · exact absurd h0 (ne_of_lt (psiB_neg_G2a h))
    · exact absurd h0 (ne_of_lt (psiB_neg_G2b h))
    · obtain ⟨h1, h2⟩ := h
      exact Or.inr (Or.inl ⟨by linarith [h1, e2, e3, e4, hz2lo],
        le_of_eq ((hz3eq u ⟨h1, h2⟩).mp h0)⟩)
    · exact absurd h0 (ne_of_gt (psiB_pos_G3 h))
    · obtain ⟨h1, h2⟩ := h
      exact Or.inr (Or.inr (le_of_eq ((hz4eq u ⟨h1, h2⟩).mp h0).symm))
    · exact absurd h0 (ne_of_lt (psiB_neg_G4 h))
  have key_nonpos : ∀ u : ℝ, u ∈ Icc (0:ℝ) (2 * Real.pi) →
      (u ≤ z1 ∨ (z2 ≤ u ∧ u ≤ z3) ∨ z4 ≤ u) → psiB u ≤ 0 := by
    intro u hu hd
    have hlt := key_lt u hu
    rcases hd with hd | hd
    · rcases lt_or_eq_of_le hd with h3 | h3
      · exact le_of_lt (hlt.mpr (Or.inl h3))
      · rw [h3]; exact le_of_eq hz1z
    · rcases hd with hd | hd
      · rcases lt_or_eq_of_le hd.1 with h3 | h3
        · rcases lt_or_eq_of_le hd.2 with h4 | h4
          · exact le_of_lt (hlt.mpr (Or.inr (Or.inl ⟨h3, h4⟩)))
          · rw [h4]; exact le_of_eq hz3z
        · rw [← h3]; exact le_of_eq hz2z
      · rcases lt_or_eq_of_le hd with h3 | h3
        · exact le_of_lt (hlt.mpr (Or.inr (Or.inr h3)))
        · rw [← h3]; exact le_of_eq hz4z
  refine ⟨⟨hz1lo, ?_, ?_, ?_, ?_⟩,
    ⟨⟨hz1lo, hz1hi⟩, ⟨hz2lo, hz2hi⟩, ⟨hz3lo, hz3hi⟩, ⟨hz4lo, hz4hi⟩⟩, ?_, ?_⟩
  · exact lt_trans hz1hi (lt_trans e1 hz2lo)
  · exact lt_trans hz2hi (lt_trans e3 (lt_trans e4 hz3lo))
  · exact lt_trans hz3hi (lt_trans e6 hz4lo)
  · exact lt_trans hz4hi e8
  · intro u hu
    rw [mem_closed_union_iff hu.1 hu.2]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h1 | h1
      · rcases (key_lt u hu).mp h1 with h2 | h2
        · exact Or.inl (le_of_lt h2)
        · rcases h2 with h2 | h2
          · exact Or.inr (Or.inl ⟨le_of_lt h2.1, le_of_lt h2.2⟩)
          · exact Or.inr (Or.inr (le_of_lt h2))
      · exact key_zero u hu h1
    · intro hd; exact key_nonpos u hu hd
  · intro u hu
    rw [mem_open_union_iff hu.1 hu.2]
    exact key_lt u hu

end

end Work.RefuteDrop
