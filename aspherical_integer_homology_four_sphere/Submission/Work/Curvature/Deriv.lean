import Submission.Work.Curvature.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Derivatives of the model metric components

This file computes `dG G q v a c = D_v (G · a c)` for the three model metrics
`uhsMetric`, `warpedMetric` and `flatMetric` of `Work.Curvature.Basic`.

These are the first input of the Koszul formula `koszulRHS`; the second input is
the derivative of the Christoffel symbol, computed in the companion files
`Work.Curvature.UHS` and `Work.Curvature.Warped`.
-/

open scoped RealInnerProductSpace
open Filter Topology

namespace Work.Curvature

noncomputable section

/-! ## UHS -/

/-- The derivative of `s ↦ s⁻¹ ^ 2` at `s ≠ 0`. -/
theorem hasDerivAt_inv_sq (s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun y : ℝ => y⁻¹ ^ 2) (-(2 * s⁻¹ ^ 3)) s := by
  have h1 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * s⁻¹) (s⁻¹) := by
    simpa using hasDerivAt_pow 2 s⁻¹
  have h2 := h1.comp s (hasDerivAt_inv hs)
  have h3 : (2 * s⁻¹ * -(s ^ 2)⁻¹) = -(2 * s⁻¹ ^ 3) := by
    field_simp
  rw [h3] at h2
  have hfun : ((fun z : ℝ => z ^ 2) ∘ fun y : ℝ => y⁻¹) = fun y : ℝ => y⁻¹ ^ 2 := by
    funext y
    rw [Function.comp_apply]
  rwa [hfun] at h2

theorem hasFDerivAt_uhsMetric (a c : E4) (q : E4) (hq : q 3 ≠ 0) :
    HasFDerivAt (fun q' : E4 => uhsMetric q' a c)
      ((⟪a, c⟫ * (-(2 * (q 3)⁻¹ ^ 3))) • coord 3) q := by
  have h2 := (hasFDerivAt_comp_coord (fun y : ℝ => y⁻¹ ^ 2) 3 q
    (hasDerivAt_inv_sq (q 3) hq)).mul_const ⟪a, c⟫
  convert h2 using 1
  · funext q'
    rw [uhsMetric_apply]
  · rw [smul_smul]

/-- **Derivative of the UHS metric components.** -/
theorem dG_uhsMetric (a c v : E4) (q : E4) (hq : q 3 ≠ 0) :
    dG uhsMetric q v a c = -(2 * (q 3)⁻¹ ^ 3) * ⟪a, c⟫ * (v 3) := by
  rw [dG, (hasFDerivAt_uhsMetric a c q hq).fderiv, coord_smul_apply]
  ring

/-! ## Warped -/

theorem hasDerivAt_sq (f : ℝ → ℝ) (s : ℝ) (hs : DifferentiableAt ℝ f s) :
    HasDerivAt (fun y : ℝ => f y ^ 2) (2 * f s * deriv f s) s := by
  have h : HasDerivAt (fun y : ℝ => f y * f y) (2 * f s * deriv f s) s := by
    have h1 := hs.hasDerivAt.mul hs.hasDerivAt
    convert h1 using 1
    ring
  convert h using 1
  funext y
  rw [pow_two]

theorem hasFDerivAt_warpedMetric (f h : ℝ → ℝ) (a c : E4) (q : E4)
    (hfd : DifferentiableAt ℝ f (q 0)) (hhd : DifferentiableAt ℝ h (q 0)) :
    HasFDerivAt (fun q' : E4 => warpedMetric f h q' a c)
      ((2 * (deriv f (q 0) * f (q 0)) * (a 1 * c 1)
        + 2 * (deriv h (q 0) * h (q 0)) * (a 2 * c 2 + a 3 * c 3)) • coord 0) q := by
  have hF : HasFDerivAt (fun q' : E4 => f (q' 0) ^ 2 * (a 1 * c 1))
      ((2 * (deriv f (q 0) * f (q 0)) * (a 1 * c 1)) • coord 0) q := by
    have hd := (hasFDerivAt_comp_coord (fun y : ℝ => f y ^ 2) 0 q
      (hasDerivAt_sq f (q 0) hfd)).mul_const (a 1 * c 1)
    have hclm : (a 1 * c 1) • (2 * f (q 0) * deriv f (q 0)) • coord 0
        = (2 * (deriv f (q 0) * f (q 0)) * (a 1 * c 1)) • coord 0 := by
      rw [smul_smul]
      congr 1
      ring
    rwa [hclm] at hd
  have hH : HasFDerivAt (fun q' : E4 => h (q' 0) ^ 2 * (a 2 * c 2 + a 3 * c 3))
      ((2 * (deriv h (q 0) * h (q 0)) * (a 2 * c 2 + a 3 * c 3)) • coord 0) q := by
    have hd := (hasFDerivAt_comp_coord (fun y : ℝ => h y ^ 2) 0 q
      (hasDerivAt_sq h (q 0) hhd)).mul_const (a 2 * c 2 + a 3 * c 3)
    have hclm : (a 2 * c 2 + a 3 * c 3) • (2 * h (q 0) * deriv h (q 0)) • coord 0
        = (2 * (deriv h (q 0) * h (q 0)) * (a 2 * c 2 + a 3 * c 3)) • coord 0 := by
      rw [smul_smul]
      congr 1
      ring
    rwa [hclm] at hd
  have hK : HasFDerivAt (fun _ : E4 => a 0 * c 0) (0 : E4 →L[ℝ] ℝ) q :=
    hasFDerivAt_const (a 0 * c 0) q
  have hall := (hK.add hF).add hH
  have hfun : (fun q' : E4 => warpedMetric f h q' a c)
      = ((fun _ : E4 => a 0 * c 0) + fun q' : E4 => f (q' 0) ^ 2 * (a 1 * c 1))
        + fun q' : E4 => h (q' 0) ^ 2 * (a 2 * c 2 + a 3 * c 3) := by
    funext q'
    rw [warpedMetric_apply]
    simp only [Pi.add_apply]
  have hclm : 0 + (2 * (deriv f (q 0) * f (q 0)) * (a 1 * c 1)) • coord 0
      + (2 * (deriv h (q 0) * h (q 0)) * (a 2 * c 2 + a 3 * c 3)) • coord 0
      = (2 * (deriv f (q 0) * f (q 0)) * (a 1 * c 1)
        + 2 * (deriv h (q 0) * h (q 0)) * (a 2 * c 2 + a 3 * c 3)) • coord 0 := by
    rw [zero_add, ← add_smul]
  rw [← hfun, hclm] at hall
  exact hall

/-- **Derivative of the warped metric components**, in the shape in which it enters
the Koszul formula (the whole expression is multiplied by `v 0`). -/
theorem dG_warpedMetric (f h : ℝ → ℝ) (a c v : E4) (q : E4)
    (hfd : DifferentiableAt ℝ f (q 0)) (hhd : DifferentiableAt ℝ h (q 0)) :
    dG (warpedMetric f h) q v a c
      = (2 * (deriv f (q 0) * f (q 0)) * (a 1 * c 1)
          + 2 * (deriv h (q 0) * h (q 0)) * (a 2 * c 2 + a 3 * c 3)) * (v 0) := by
  have hd : fderiv ℝ (fun q' : E4 => warpedMetric f h q' a c) q
      = ((2 * (deriv f (q 0) * f (q 0)) * (a 1 * c 1)
          + 2 * (deriv h (q 0) * h (q 0)) * (a 2 * c 2 + a 3 * c 3)) • coord 0) :=
    (hasFDerivAt_warpedMetric f h a c q hfd hhd).fderiv
  rw [dG, hd]
  exact coord_smul_apply _ _ _

/-! ## Flat -/

theorem hasFDerivAt_flatMetric (h₀ : ℝ) (a c : E4) (q : E4) :
    HasFDerivAt (fun q' : E4 => flatMetric h₀ q' a c) (0 : E4 →L[ℝ] ℝ) q :=
  hasFDerivAt_const (flatMetric h₀ q a c) q

/-- **Derivative of the flat metric components**: they are constant. -/
theorem dG_flatMetric (h₀ : ℝ) (a c v : E4) (q : E4) :
    dG (flatMetric h₀) q v a c = 0 := by
  have hd : fderiv ℝ (fun q' : E4 => flatMetric h₀ q' a c) q = (0 : E4 →L[ℝ] ℝ) :=
    (hasFDerivAt_flatMetric h₀ a c q).fderiv
  rw [dG, hd]
  simp

end

end Work.Curvature
