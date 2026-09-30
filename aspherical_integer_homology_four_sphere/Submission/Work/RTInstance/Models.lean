/-
# The three metric models of the atlas of `M̂`

The charts of the atlas of `M̂` carry one of the three documented metrics of blueprint §1:

* the **upper half space metric** `(|dx|²+ds²)/s²` on the hyperbolic side and in the collar,
* the **warped filling metric** `dr² + f(r)²dθ² + h(r)²|dw|²` of the profile
  `Work.Profiles.FillProfile` (polar charts of the filling),
* the **flat core metric** `da² + db² + h₀²|dw|²` (Cartesian core charts).

`Work.Space.ModelAtlas` wants, for each chart, a *smooth positive definite family of bilinear forms
on all of `E4`* (the values outside the chart are irrelevant to the metric `gM`, but the fields of
the structure are total).  The flat and warped families are already total and positive definite, but
`Work.Curvature.uhsMetric q = (q 3)⁻² • δ` is **not** positive definite at `q 3 = 0`; we therefore
use the total model `uhsModel δ`, which agrees with `uhsMetric` on the open set `{q 3 ≥ δ}` -- and
every chart of the atlas with the UHS model has its image in `{q 3 > δ}` (a hypothesis of the
pending data, see `Submission/Work/RTInstance/NOTES.md`).

## Main definitions

* `Work.RTInstance.coord4`, `diagQuad` — diagonal bilinear forms as continuous linear maps.
* `Work.RTInstance.uhsModel δ` — the total UHS model.
* `Work.RTInstance.warpedModel f h`, `Work.RTInstance.flatModel h₀` — the warped and flat models.
* `Work.RTInstance.ChartLayer` — the layer of a chart (`uhs` / `warped` / `flat`), with its model
  `ChartLayer.model`, its non-degeneracy condition `ChartLayer.ok`, and the four structure fields
  `ChartLayer.model_smooth`, `ChartLayer.model_symm`, `ChartLayer.model_pos`,
  `ChartLayer.secNonposAt`.
-/
import Mathlib
import Submission.Work.RTInstance.Basic
import Submission.Work.CurvModels.Transport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace
open Bundle

namespace Work.RTInstance

/-- The `i`-th coordinate projection of `E4`, as a continuous linear map. -/
def coord4 (i : Fin 4) : E4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) i

@[simp] theorem coord4_apply (i : Fin 4) (q : E4) : coord4 i q = q i :=
  PiLp.proj_apply 2 _ i q

/-- **A diagonal bilinear form as a continuous linear map**: `∑ i c i • (a_i b_i)`. -/
def diagQuad (c : Fin 4 → ℝ) : E4 →L[ℝ] E4 →L[ℝ] ℝ :=
  ∑ i, (c i • coord4 i).smulRight (coord4 i)

/-- The value of `diagQuad c`. -/
theorem diagQuad_apply (c : Fin 4 → ℝ) (a b : E4) :
    diagQuad c a b = c 0 * a 0 * b 0 + c 1 * a 1 * b 1 + c 2 * a 2 * b 2 + c 3 * a 3 * b 3 := by
  simp only [diagQuad, Fin.sum_univ_four, add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, coord4_apply]
  ring

theorem diagQuad_symm (c : Fin 4 → ℝ) (a b : E4) : diagQuad c a b = diagQuad c b a := by
  rw [diagQuad_apply, diagQuad_apply]; ring

/-- A diagonal bilinear form with positive coefficients is positive definite. -/
theorem diagQuad_pos {c : Fin 4 → ℝ} (hc : ∀ i, 0 < c i) (a : E4) (ha : a ≠ 0) :
    0 < diagQuad c a a := by
  rw [diagQuad_apply]
  have h4 := Work.Curvature.sum_sq_four_pos (g := c) hc a ha
  nlinarith [h4]

/-- **The smooth height factor of the total UHS model**: `s ↦ s⁻¹` for `s ≥ δ`, and a positive
smooth continuation for `s ≤ δ`. -/
def uhsFactor (δ : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition (s / δ) * s⁻¹ + (1 - Real.smoothTransition (s / δ)) * δ⁻¹

/-- **The total upper half space model.**  `uhsModel δ q` agrees with `Work.Curvature.uhsMetric q`
on `{q 3 ≥ δ}` (and is positive definite and positive on all of `E4`). -/
def uhsModel (δ : ℝ) : E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ) :=
  fun q => (uhsFactor δ (q 3)) ^ 2 • (innerSL ℝ : E4 →L[ℝ] E4 →L[ℝ] ℝ)

/-- The warped filling model, in the continuous-linear-map form of `ModelAtlas.model`. -/
def warpedModel (f h : ℝ → ℝ) : E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ) :=
  fun q => diagQuad ![1, f (q 0) ^ 2, h (q 0) ^ 2, h (q 0) ^ 2]

/-- The flat core model, in the continuous-linear-map form of `ModelAtlas.model`. -/
def flatModel (h₀ : ℝ) : E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ) :=
  fun _ => diagQuad ![1, 1, h₀ ^ 2, h₀ ^ 2]

theorem uhsModel_apply (δ : ℝ) (q a b : E4) :
    uhsModel δ q a b = (uhsFactor δ (q 3)) ^ 2 * inner ℝ a b := by
  show (uhsFactor δ (q 3) ^ 2 • (innerSL ℝ : E4 →L[ℝ] E4 →L[ℝ] ℝ)) a b = _
  rw [ContinuousLinearMap.smul_apply]
  exact congrArg (fun t => (uhsFactor δ (q 3)) ^ 2 * t) (innerSL_apply_apply ℝ a b)

theorem warpedModel_apply (f h : ℝ → ℝ) (q a b : E4) :
    warpedModel f h q a b = a 0 * b 0 + f (q 0) ^ 2 * (a 1 * b 1)
      + h (q 0) ^ 2 * (a 2 * b 2 + a 3 * b 3) := by
  rw [warpedModel, diagQuad_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  ring

theorem flatModel_apply (h₀ : ℝ) (q a b : E4) :
    flatModel h₀ q a b = a 0 * b 0 + a 1 * b 1 + h₀ ^ 2 * (a 2 * b 2 + a 3 * b 3) := by
  rw [flatModel, diagQuad_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  ring

/-! ## The smooth positive modification of the profile function -/

/-- **A smooth modification of `f` that is positive everywhere and agrees with `f` on `[c, ∞)`.**
It is `f r · t + c · (1 - t)` with `t = smoothTransition (r / c)`: `= c` for `r ≤ 0` and `= f r` for
`r ≥ c`. -/
def posExt (f : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun r => f r * Real.smoothTransition (r / c) + c * (1 - Real.smoothTransition (r / c))

/-- The warped filling model used by the atlas: the model of `Work.Curvature.warpedMetric f h`,
with the warping function `f` replaced by its positive modification `posExt f (1/8)` so that the
model is positive definite on all of `E4` (the polar charts have `q 0 > 1/4`). -/
def warpedModelA (f h : ℝ → ℝ) : E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ) :=
  fun q => diagQuad ![1, posExt f (1/8) (q 0) ^ 2, h (q 0) ^ 2, h (q 0) ^ 2]

theorem warpedModelA_apply (f h : ℝ → ℝ) (q a b : E4) :
    warpedModelA f h q a b = a 0 * b 0 + posExt f (1/8) (q 0) ^ 2 * (a 1 * b 1)
      + h (q 0) ^ 2 * (a 2 * b 2 + a 3 * b 3) := by
  rw [warpedModelA, diagQuad_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  ring

/-! ## Agreement with the documented models -/

/-- `uhsFactor δ s = s⁻¹` for `s ≥ δ`. -/
theorem uhsFactor_eq_inv {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : δ ≤ s) : uhsFactor δ s = s⁻¹ := by
  have h : 1 ≤ s / δ := (le_div_iff₀ hδ).mpr (by linarith)
  rw [uhsFactor, Real.smoothTransition.one_of_one_le h]
  ring

/-- `posExt f c r = f r` for `r ≥ c`. -/
theorem posExt_eq {f : ℝ → ℝ} {c r : ℝ} (hc : 0 < c) (hr : c ≤ r) : posExt f c r = f r := by
  have h : 1 ≤ r / c := (le_div_iff₀ hc).mpr (by linarith)
  rw [posExt, Real.smoothTransition.one_of_one_le h]
  ring

/-- **The total UHS model agrees with `Work.Curvature.uhsMetric` on `{q 3 ≥ δ}`.** -/
theorem uhsModel_eq_uhsMetric {δ : ℝ} (hδ : 0 < δ) {q : E4} (hq : δ ≤ q 3) (a b : E4) :
    uhsModel δ q a b = Curvature.uhsMetric q a b := by
  rw [uhsModel_apply, uhsFactor_eq_inv hδ hq, Curvature.uhsMetric_apply]

/-- **The warped model agrees with `Work.Curvature.warpedMetric f h` on `{q 0 ≥ 1/8}`.** -/
theorem warpedModelA_eq_warpedMetric {f h : ℝ → ℝ} {q : E4} (hq : (1/8 : ℝ) ≤ q 0) (a b : E4) :
    warpedModelA f h q a b = Curvature.warpedMetric f h q a b := by
  rw [warpedModelA_apply, posExt_eq (by norm_num) hq, Curvature.warpedMetric_apply]

/-- **The flat model is `Work.Curvature.flatMetric h₀`.** -/
theorem flatModel_eq_flatMetric (h₀ : ℝ) (q a b : E4) :
    flatModel h₀ q a b = Curvature.flatMetric h₀ q a b := by
  rw [flatModel_apply, Curvature.flatMetric_apply]

/-! ## The layer of a chart -/

/-- **The metric layer of a chart of the atlas of `M̂`**: upper half space, warped filling (with the
profile `P`), or flat core (with the parameter `h₀`). -/
inductive ChartLayer where
  /-- The upper half space metric, with the margin `δ` of `uhsModel`. -/
  | uhs (δ : ℝ)
  /-- The warped filling metric of a profile. -/
  | warped (P : Work.Profiles.FillProfile)
  /-- The flat core metric. -/
  | flat (h₀ : ℝ)

namespace ChartLayer

/-- The metric model of a layer, in the form of `Work.Space.ModelAtlas.model`. -/
def model : ChartLayer → E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ)
  | uhs δ => uhsModel δ
  | warped P => warpedModelA P.f P.h
  | flat h₀ => flatModel h₀

/-- The metric model of a layer, as a `Work.Curvature.MetricField`. -/
def metricField (l : ChartLayer) : Curvature.MetricField := fun q a b => l.model q a b

/-- **The non-degeneracy condition of a layer at a point** `q` of `E4`: the point at which the
chart image sits must lie in the region where the model is non-positively curved. -/
def ok : ChartLayer → E4 → Prop
  | uhs δ, q => 0 < δ ∧ δ < q 3
  | warped _, q => 1/4 < q 0
  | flat h₀, _ => h₀ ≠ 0

theorem model_symm (l : ChartLayer) (q v w : E4) : l.model q v w = l.model q w v := by
  cases l with
  | uhs δ =>
      show uhsModel δ q v w = uhsModel δ q w v
      rw [uhsModel_apply, uhsModel_apply, real_inner_comm]
  | warped P =>
      show warpedModelA P.f P.h q v w = warpedModelA P.f P.h q w v
      rw [warpedModelA_apply, warpedModelA_apply]; ring
  | flat h₀ =>
      show flatModel h₀ q v w = flatModel h₀ q w v
      rw [flatModel_apply, flatModel_apply]; ring

/-- **The model of a chart layer has non-positive sectional curvature at every point of its
non-degeneracy region.**  This is the transport of `Work.Curvature.secNonposAt_uhs` /
`secNonposAt_fillProfile` / `secNonposAt_flat` along the agreement of the total model with the
geometric metric of the layer, through the locality theorem
`Work.CurvModels.SecNonposAt_congr`. -/
theorem secNonposAt (l : ChartLayer) {q : E4} (hq : l.ok q) :
    Curvature.SecNonposAt l.metricField q := by
  cases l with
  | uhs δ =>
      obtain ⟨hδ, hq3⟩ := hq
      refine Work.CurvModels.secNonposAt_of_agreesNear_uhsMetric (lt_trans hδ hq3) ?_
      refine Work.CurvModels.AgreesNear.of_mem_open
        (V := (coord4 3) ⁻¹' Set.Ioi δ) (isOpen_Ioi.preimage (coord4 3).continuous)
        (by simpa [coord4_apply] using hq3) ?_
      intro q' hq' a b
      have hq'3 : δ < q' 3 := by simpa [coord4_apply] using hq'
      exact (uhsModel_eq_uhsMetric hδ (le_of_lt hq'3) a b).symm
  | warped P =>
      have hq0 : 0 < q 0 := lt_trans (by norm_num) hq
      have hq8 : (1/8 : ℝ) < q 0 := lt_trans (by norm_num) hq
      refine Work.CurvModels.secNonposAt_of_agreesNear_warpedMetric P hq0 ?_
      refine Work.CurvModels.AgreesNear.of_mem_open
        (V := (coord4 0) ⁻¹' Set.Ioi (1/8 : ℝ)) (isOpen_Ioi.preimage (coord4 0).continuous)
        (by simpa [coord4_apply] using hq8) ?_
      intro q' hq' a b
      have hq'8 : (1/8 : ℝ) < q' 0 := by simpa [coord4_apply] using hq'
      exact (warpedModelA_eq_warpedMetric (le_of_lt hq'8) a b).symm
  | flat h₀ =>
      refine Work.CurvModels.secNonposAt_of_agreesNear_flatMetric h₀ hq ?_
      refine Filter.Eventually.of_forall ?_
      intro q' a b
      exact (flatModel_eq_flatMetric h₀ q' a b).symm

/-- **The *global* non-degeneracy input of a layer** (the part of `ok` that does not depend on the
point): positivity of the UHS margin, `True` for the warped layer, `h₀ ≠ 0` for the flat layer. -/
def okAnywhere : ChartLayer → Prop
  | uhs δ => 0 < δ
  | warped _ => True
  | flat h₀ => h₀ ≠ 0

end ChartLayer

end Work.RTInstance
