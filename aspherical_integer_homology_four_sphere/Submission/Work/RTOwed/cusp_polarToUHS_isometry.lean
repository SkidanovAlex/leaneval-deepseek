/-
# The polar chart of the cusp is an isometry from the warped filling metric to the UHS metric

`Work.Cusp.polarToUHS v` maps the polar coordinates `(r,θ,w₁,w₂)` of the filling piece of the
`v`-th cusp to the upper half space coordinates `(x,s)` of the collar by

  `x = (‖σ_v‖/2π) θ · frame1 + w₁ · frame2 + w₂ · frame3`,   `s = e^{R₀−r}`,

i.e. it is the map `Work.HypModel.polarToUHS C D` (whose pullback of the UHS metric is the warped
metric with `f r = C eʳ`, `h r = D eʳ`, `Work.HypModel.polarToUHS_isometry`) followed by the
rotation `polarRot v` of the horizontal `ℝ³` that replaces the standard basis `(e₀,e₁,e₂)` by the
orthonormal frame `(frame1 v, frame2 v, frame3 v)` of the cusp.

Since the rotation `polarRot v` fixes the height coordinate and preserves the (Euclidean) inner
product of `E4` — the frame is orthonormal, `Work.Cusp.frame_orthonormal` — it leaves the upper half
space metric invariant (`uhsMetric_polarRot`), so the pullback of the UHS metric along
`polarToUHS v` is the warped metric of the profile constants `C_v = fillC v`,
`D = fillD` of the filling atlas.

## Contents

* `polarRot`, `polarMix`: the rotation and the frame combination;
* `polarRot_horiz`, `polarMix_inner`, `polarRot_inner`, `uhsMetric_polarRot`: `polarRot` is an
  inner-product preserving map fixing the last coordinate, hence an isometry of `uhsMetric`;
* `polarToUHS_eq_polarRot`: `Work.Cusp.polarToUHS v = polarRot v ∘ Work.HypModel.polarToUHS C_v D`;
* `fderiv_polarToUHS_apply`: the chain rule for the derivative;
* `cusp_polarToUHS_isometry`: the statement.
-/
import Mathlib
import Submission.Work.RTOwed.FillAtlas

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Work
open scoped Real InnerProductSpace

namespace Work.RTOWed

/-! ## The rotation of the horizontal space into the cusp frame -/

/-- The `i`-th coordinate projection of `E4`, as a continuous linear map. -/
private abbrev ccoord (i : Fin 4) : Work.Cusp.E4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) i

/-- **The rotation of the horizontal `ℝ³` into the cusp frame**: the `ℝ`-linear isometry of
`E4 = ℝ⁴` that sends `(a,b,c,d)` to `a · frame1 v + b · frame2 v + c · frame3 v` in the first three
coordinates and keeps the last coordinate `d`.  It is the map that rewrites the standard horizontal
coordinates of `Work.HypModel.polarToUHS` in the orthonormal frame `(frame1 v, frame2 v, frame3 v)`
of the cusp `v`. -/
private noncomputable def polarRot (v : Fin 5) : Work.Cusp.E4 →L[ℝ] Work.Cusp.E4 :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm : (Fin 4 → ℝ) →L[ℝ] Work.Cusp.E4).comp
    (ContinuousLinearMap.pi ![
      (Work.Cusp.frame1 v 0) • ccoord 0 + (Work.Cusp.frame2 v 0) • ccoord 1
        + (Work.Cusp.frame3 v 0) • ccoord 2,
      (Work.Cusp.frame1 v 1) • ccoord 0 + (Work.Cusp.frame2 v 1) • ccoord 1
        + (Work.Cusp.frame3 v 1) • ccoord 2,
      (Work.Cusp.frame1 v 2) • ccoord 0 + (Work.Cusp.frame2 v 2) • ccoord 1
        + (Work.Cusp.frame3 v 2) • ccoord 2,
      ccoord 3])

/-- The frame combination `c₀ · frame1 v + c₁ · frame2 v + c₂ · frame3 v` of a coefficient vector
`c : ℝ³`. -/
private noncomputable def polarMix (v : Fin 5) (c : Work.Cusp.E3) : Work.Cusp.E3 :=
  c 0 • Work.Cusp.frame1 v + c 1 • Work.Cusp.frame2 v + c 2 • Work.Cusp.frame3 v

/-- `polarRot v` keeps the last coordinate. -/
private theorem polarRot_apply_three (v : Fin 5) (y : Work.Cusp.E4) : (polarRot v y) 3 = y 3 := by
  simp [polarRot]

/-- The horizontal part of `polarRot v a` is the frame combination of the horizontal part of `a`. -/
private theorem polarRot_horiz (v : Fin 5) (a : Work.Cusp.E4) :
    (show Work.Cusp.E3 from !₂[(polarRot v a) 0, (polarRot v a) 1, (polarRot v a) 2])
      = polarMix v !₂[a 0, a 1, a 2] := by
  ext i; fin_cases i <;> simp [polarRot, polarMix, mul_comm]

/-- **The frame `(frame1 v, frame2 v, frame3 v)` is orthonormal**: the inner product of two frame
combinations is the Euclidean inner product of their coefficients
(`Work.Cusp.frame_orthonormal`). -/
private theorem polarMix_inner (v : Fin 5) (c d : Work.Cusp.E3) :
    inner ℝ (polarMix v c) (polarMix v d) = c 0 * d 0 + c 1 * d 1 + c 2 * d 2 := by
  obtain ⟨h12, h13, h23, h1, h2, h3⟩ := Work.Cusp.frame_orthonormal v
  have h21 : inner ℝ (Work.Cusp.frame2 v) (Work.Cusp.frame1 v) = 0 := by rw [real_inner_comm, h12]
  have h31 : inner ℝ (Work.Cusp.frame3 v) (Work.Cusp.frame1 v) = 0 := by rw [real_inner_comm, h13]
  have h32 : inner ℝ (Work.Cusp.frame3 v) (Work.Cusp.frame2 v) = 0 := by rw [real_inner_comm, h23]
  have e1 : inner ℝ (Work.Cusp.frame1 v) (Work.Cusp.frame1 v) = 1 := by
    rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have e2 : inner ℝ (Work.Cusp.frame2 v) (Work.Cusp.frame2 v) = 1 := by
    rw [real_inner_self_eq_norm_sq, h2]; norm_num
  have e3 : inner ℝ (Work.Cusp.frame3 v) (Work.Cusp.frame3 v) = 1 := by
    rw [real_inner_self_eq_norm_sq, h3]; norm_num
  simp only [polarMix, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    e1, e2, e3, h12, h13, h23, h21, h31, h32]
  ring

/-- The inner product in `E4` written out in coordinates. -/
private theorem inner_four (a b : Work.Cusp.E4) :
    inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 := by
  have h : inner ℝ a b = b 0 * a 0 + b 1 * a 1 + b 2 * a 2 + b 3 * a 3 := by
    simp [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply]
  rw [h]; ring

/-- The inner product of the horizontal parts of `polarRot v a` and `polarRot v b` is the inner
product of the frame combinations of the horizontal parts of `a` and `b`. -/
private theorem inner_horiz (v : Fin 5) (a b : Work.Cusp.E4) :
    (polarRot v a) 0 * (polarRot v b) 0 + (polarRot v a) 1 * (polarRot v b) 1
        + (polarRot v a) 2 * (polarRot v b) 2
      = inner ℝ (polarMix v !₂[a 0, a 1, a 2]) (polarMix v !₂[ b 0, b 1, b 2]) := by
  rw [← polarRot_horiz v a, ← polarRot_horiz v b]
  simp [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]
  ring

/-- **`polarRot v` preserves the inner product**: it is an orthogonal transformation of `E4`. -/
private theorem polarRot_inner (v : Fin 5) (a b : Work.Cusp.E4) :
    inner ℝ (polarRot v a) (polarRot v b) = inner ℝ a b := by
  rw [inner_four (polarRot v a) (polarRot v b), polarRot_apply_three, polarRot_apply_three,
    inner_horiz, polarMix_inner, inner_four a b]
  simp

/-- **`polarRot v` is an isometry of the upper half space metric**: it fixes the height coordinate
and preserves the Euclidean inner product, and `uhsMetric q a b = (q 3)⁻²⟪a,b⟫`. -/
private theorem uhsMetric_polarRot (v : Fin 5) (y a b : Work.Cusp.E4) :
    Work.Curvature.uhsMetric (polarRot v y) (polarRot v a) (polarRot v b)
      = Work.Curvature.uhsMetric y a b := by
  rw [Work.Curvature.uhsMetric_apply, Work.Curvature.uhsMetric_apply, polarRot_apply_three,
    polarRot_inner]

/-! ## The cusp polar chart as the HypModel polar chart followed by the rotation -/

/-- **The cusp polar chart is the `HypModel` polar chart followed by `polarRot`**: with the
constants `C_v = fillC v = ‖σ_v‖e^{−R₀}/2π`, `D = fillD = e^{−R₀}` of the filling atlas, the
coordinates `(r,θ,w₁,w₂) ↦ ((‖σ_v‖/2π)θ · frame1 + w₁ frame2 + w₂ frame3, e^{R₀−r})` of
`Work.Cusp.polarToUHS v` are the coordinates `((C_v/D)θ, w₁, w₂, D⁻¹e^{−r})` of
`Work.HypModel.polarToUHS C_v D` read in the orthonormal frame. -/
private theorem polarToUHS_eq_polarRot (v : Fin 5) (q : Work.Cusp.E4) :
    Work.Cusp.polarToUHS v q
      = polarRot v (Work.HypModel.polarToUHS (Work.RTOwed.fillC v) Work.RTOwed.fillD q) := by
  have hCD : Work.RTOwed.fillC v / Work.RTOwed.fillD = ‖Work.Cusp.slope v‖ / (2 * Real.pi) := by
    rw [Work.RTOwed.fillC, Work.RTOwed.fillD]; field_simp
  have hD : ∀ a : ℝ, Work.RTOwed.fillD⁻¹ * Real.exp (-a) = Real.exp (Work.Cusp.R0 - a) := by
    intro a
    rw [Work.RTOwed.fillD, Real.exp_neg, inv_inv, ← Real.exp_add]
    rw [show Work.Cusp.R0 + -a = Work.Cusp.R0 - a from by ring]
  ext i; fin_cases i <;>
    simp [polarRot, Work.Cusp.polarToUHS, Work.HypModel.polarToUHS, hCD, hD]
  all_goals ring

/-- **The chain rule for the cusp polar chart**: the derivative of `Work.Cusp.polarToUHS v` is the
derivative of `Work.HypModel.polarToUHS C_v D` followed by the (linear) rotation `polarRot v`. -/
private theorem fderiv_polarToUHS_apply (v : Fin 5) (q a : Work.Cusp.E4) :
    fderiv ℝ (Work.Cusp.polarToUHS v) q a
      = polarRot v
          (fderiv ℝ (Work.HypModel.polarToUHS (Work.RTOwed.fillC v) Work.RTOwed.fillD) q a) := by
  set g := Work.HypModel.polarToUHS (Work.RTOwed.fillC v) Work.RTOwed.fillD with hg
  have hd : fderiv ℝ g q = Work.HypModel.dPolarToUHS (Work.RTOwed.fillC v) Work.RTOwed.fillD q :=
    (Work.HypModel.hasFDerivAt_polarToUHS (Work.RTOwed.fillC v) Work.RTOwed.fillD q).fderiv
  have hcomp : HasFDerivAt ((polarRot v) ∘ g) ((polarRot v).comp (fderiv ℝ g q)) q := by
    rw [hd]
    exact (ContinuousLinearMap.hasFDerivAt (polarRot v)).comp q
      (Work.HypModel.hasFDerivAt_polarToUHS (Work.RTOwed.fillC v) Work.RTOwed.fillD q)
  have hfun : Work.Cusp.polarToUHS v = fun p => polarRot v (g p) :=
    funext (polarToUHS_eq_polarRot v)
  calc fderiv ℝ (Work.Cusp.polarToUHS v) q a
      = fderiv ℝ ((polarRot v) ∘ g) q a := by rw [hfun]; rfl
    _ = ((polarRot v).comp (fderiv ℝ g q)) a := by rw [hcomp.fderiv]
    _ = polarRot v (fderiv ℝ g q a) := rfl
    _ = polarRot v
          (fderiv ℝ (Work.HypModel.polarToUHS (Work.RTOwed.fillC v) Work.RTOwed.fillD) q a) := by
        rw [hg] at hd ⊢

/-! ## The statement -/

/-- **The pullback of the upper half space metric along the cusp polar chart is the warped filling
metric**: for every `(r,θ,w₁,w₂) = q` and tangent vectors `u, w` at `q`,
`polarToUHS v` carries the warped metric `dr² + (C_v eʳ)²dθ² + (D eʳ)²|dw|²` (`C_v = fillC v`,
`D = fillD`) to the UHS metric `(|dx|² + ds²)/s²`.  This is the metric statement of the junction
charts of the filling atlas (`Work.RTOWed.jLayer`) against the collar charts
(`Work.RTOWed.cLayer`). -/
theorem cusp_polarToUHS_isometry (v : Work.Space.Cusp) (q u w : Work.Cusp.E4) :
    Work.Curvature.uhsMetric (Work.Cusp.polarToUHS v q)
        (fderiv ℝ (Work.Cusp.polarToUHS v) q u) (fderiv ℝ (Work.Cusp.polarToUHS v) q w)
      = Work.Curvature.warpedMetric (fun r => Work.RTOwed.fillC v * Real.exp r)
          (fun r => Work.RTOwed.fillD * Real.exp r) q u w := by
  rw [fderiv_polarToUHS_apply, fderiv_polarToUHS_apply, polarToUHS_eq_polarRot, uhsMetric_polarRot]
  exact Work.HypModel.polarToUHS_isometry (Work.RTOwed.fillC_pos v) Work.RTOwed.fillD_pos q u w

end Work.RTOWed
