/-
# The cusp-`0` layer of CKMRV at the `w`-dependent threshold `T w = Im (S • w) + 1`

This module sets up the layer that proves the seminorm bound
`Work.Asymptotics.SeminormK_E ℓ d` on the cusp-`0` tile `E = KEpsilon` for `d ∈ {8, 24}`
(`Submission/Work/Asymptotics/SeminormK_E_clean.lean`).

## Why a new threshold

The cusp model `Aexp (Gcusp ℓ d) w t` of the contour kernel `t ↦ Kaxis (Kfun ℓ d) w t` is only
valid above the highest pole of `z ↦ K(w,z)`, whose height is `Im (S • w)`.  In dimension `24`
the model contains the term `e^{2πt}·(Gcusp24 1 0 w + tI·Gcusp24 1 1 w)` with a non-vanishing
coefficient, so *no* bound of the shape `C (scale w)^N (1+t)^M` can hold up to the threshold
`scale w` used by `Work.Asymptotics.ERegimes`.  The split must therefore be taken at the
`w`-dependent height

  `T w = Im (S • w) + 1`   (`Work.Asymptotics.E_T`),

which satisfies `1 ≤ T w` and `T w ≤ scale w` on `E` (`Work.Asymptotics.one_le_E_T`,
`Work.Asymptotics.E_T_le_scale`), and the window hypothesis on `[1, T w]` must be allowed the
cusp model's factor `1 + e^{2πt}`.

## The layer

`Work.Asymptotics.E_ExprT` is `LayerLow + E_WinT + E_DevT + E_TailClosed(Gcusp ℓ d) (T w)`:

* `layerLow` — the contour piece over `(0,1]` (`Work.Asymptotics.layerLow`);
* `E_WinT` — the piece over `[1, T w]`;
* `E_DevT` — the deviation piece `∫_{t ≥ T w} (K - Aexp) e^{-πr²t} dt`;
* `E_TailClosed (Gcusp ℓ d) (T w)` — the closed form of `sinSq r ∫_{t ≥ T w} Aexp · e^{-πr²t}dt`.

`Work.Asymptotics.E_F2T` is the punctured layer fed to
`Work.Asymptotics.E_kernelTransform_seminorm_of_layer0`: `E_ExprT` on the convergence region
`E_R` (where the contour integral is absolutely convergent) and `0` elsewhere.

All definitions are those of the workspace's existing layer `E_Expr`/`E_F₂` with the threshold
`E_Bw N₀ w = (scale w)^{N₀}` replaced by `E_T w`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.E_TailClosed
import Submission.Work.Kernels.All

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

open Work.Kernels

/-- **The threshold of the cusp expansion on the cusp-`0` tile**: the height `Im (S • w)` of the
highest pole of `z ↦ K(w,z)`, plus one (the margin needed by the cusp tail estimates). -/
def E_T (w : ℍ) : ℝ := (ModularGroup.S • w).im + 1

/-- On `E` one has `3 ≤ T w`. -/
lemma three_le_E_T {w : ℍ} (hw : w ∈ KEpsilon) : 3 ≤ E_T w := by
  have h : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  rw [E_T]; linarith

/-- In particular `1 ≤ T w` on `E`. -/
lemma one_le_E_T {w : ℍ} (hw : w ∈ KEpsilon) : 1 ≤ E_T w :=
  le_trans (by norm_num) (three_le_E_T hw)

/-- `T w` is positive on `E`. -/
lemma E_T_pos {w : ℍ} (hw : w ∈ KEpsilon) : 0 < E_T w :=
  lt_of_lt_of_le (by norm_num) (three_le_E_T hw)

/-- **`T w ≤ scale w` on `E`**: the threshold of the cusp expansion is controlled by the scale.

This is the elementary comparison `Im w · ‖w‖^{-2} + 1 ≤ 1 + (Im w)⁻¹ + ‖w‖` which holds because
`(Im w)² ≤ ‖w‖²`. -/
lemma E_T_le_scale {w : ℍ} (_hw : w ∈ KEpsilon) : E_T w ≤ scale w := by
  have hS : (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 := by
    rw [Work.Kernels.im_smul_eq, Work.Kernels.jFun_apply]
    simp
  have hsq : w.im ^ 2 ≤ ‖(w : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    nlinarith [sq_nonneg w.re]
  have hpos : 0 < w.im := w.im_pos
  have h6 : w.im ≤ ‖(w : ℂ)‖ ^ 2 / w.im := by
    rw [le_div_iff₀ hpos]; nlinarith [hsq]
  have h4 : (w.im / ‖(w : ℂ)‖ ^ 2) = w.im * (‖(w : ℂ)‖ ^ 2)⁻¹ := div_eq_mul_inv _ _
  rw [E_T, Work.Kernels.scale, hS, h4]
  have h2 : w.im * (‖(w : ℂ)‖ ^ 2)⁻¹ ≤ w.im⁻¹ + ‖(w : ℂ)‖ := by
    rw [mul_inv_le_iff₀ (pow_pos (norm_pos_iff.mpr w.ne_zero) 2)]
    have h8 : w.im⁻¹ * w.im ^ 2 = w.im := by field_simp
    have h9 : w.im ≤ w.im⁻¹ * ‖(w : ℂ)‖ ^ 2 := by
      calc w.im = w.im⁻¹ * w.im ^ 2 := h8.symm
        _ ≤ w.im⁻¹ * ‖(w : ℂ)‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hpos.le)
    have h10 : w.im⁻¹ * ‖(w : ℂ)‖ ^ 2 ≤ (w.im⁻¹ + ‖(w : ℂ)‖) * ‖(w : ℂ)‖ ^ 2 := by
      nlinarith [norm_nonneg (w : ℂ), sq_nonneg (‖(w : ℂ)‖)]
    linarith
  linarith

/-- The threshold is `≥` the pole height. -/
lemma E_T_ge_im_S (w : ℍ) : (ModularGroup.S • w).im ≤ E_T w := by
  rw [E_T]; linarith

/-- **The window piece of the layer**: the contribution of the contour over `[1, T w]`. -/
def E_WinT (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) : ℂ :=
  sinSq r * ∫ t in (1 : ℝ)..(E_T w),
    Kaxis (Kfun ℓ d) w t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))

/-- **The deviation piece of the layer**: the contribution of the contour over `[T w, ∞)` with the
cusp model subtracted. -/
def E_DevT (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) : ℂ :=
  sinSq r * tailIntegral (fun t : ℝ => if t < E_T w then 0
    else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t) (r ^ 2)

/-- **The layer expression at the threshold `T w`**: `low + window + deviation + closed form`. -/
def E_ExprT (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) : ℂ :=
  layerLow ℓ d w r + E_WinT ℓ d w r + E_DevT ℓ d w r
    + E_TailClosed (Gcusp ℓ d) (E_T w) w r

/-- **The punctured layer** fed to `Work.Asymptotics.E_kernelTransform_seminorm_of_layer0`:
`E_ExprT` on the convergence region `E_R` (and away from `r = 0`), and `0` elsewhere. -/
def E_F2T (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) : ℂ := by
  classical
  exact if r ≠ 0 ∧ E_R ℓ d w r then E_ExprT ℓ d w r else 0

lemma E_F2T_of_R (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ)
    (h : r ≠ 0 ∧ E_R ℓ d w r) : E_F2T ℓ d w r = E_ExprT ℓ d w r := by
  classical
  rw [E_F2T]; exact if_pos h

lemma E_F2T_of_not_R (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ)
    (h : ¬ (r ≠ 0 ∧ E_R ℓ d w r)) : E_F2T ℓ d w r = 0 := by
  classical
  rw [E_F2T]; exact if_neg h

/-- The window piece is even in `r`. -/
lemma E_WinT_neg (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) :
    E_WinT ℓ d w (-r) = E_WinT ℓ d w r := by
  have hsqc : (((-r : ℝ)) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by rw [Complex.ofReal_neg, neg_sq]
  rw [E_WinT, E_WinT, hsqc]
  congr 1
  simp only [sinSq, hsqc]

/-- The deviation piece is even in `r`. -/
lemma E_DevT_neg (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) :
    E_DevT ℓ d w (-r) = E_DevT ℓ d w r := by
  have hsq' : (-r) ^ 2 = r ^ 2 := by ring
  rw [E_DevT, E_DevT, hsq']
  congr 1
  simp only [sinSq]
  rw [show (((-r : ℝ)) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 from by rw [Complex.ofReal_neg, neg_sq]]

/-- `layerLow` is even in `r`. -/
lemma E_layerLow_negT (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) :
    layerLow ℓ d w (-r) = layerLow ℓ d w r := by
  have hsq : (((-r : ℝ)) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by rw [Complex.ofReal_neg, neg_sq]
  rw [layerLow, layerLow, hsq]
  congr 1
  simp only [sinSq, hsq]

/-- The layer expression is even in `r`. -/
lemma E_ExprT_neg (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (r : ℝ) :
    E_ExprT ℓ d w (-r) = E_ExprT ℓ d w r := by
  rw [E_ExprT, E_ExprT, E_layerLow_negT, E_WinT_neg, E_DevT_neg, E_TailClosed_neg]

end Work.Asymptotics
