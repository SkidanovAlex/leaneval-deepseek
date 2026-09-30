/-
# Smoothness of the metric models of the chart layers

`Work.RTInstance.ChartLayer.model` assigns to each chart layer (`uhs`, `warped`, `flat`) a family
`E4 → (E4 →L[ℝ] E4 →L[ℝ] ℝ)` of bilinear forms, total on `E4`.  The field `model_smooth` of
`Work.Space.ModelAtlas`/`Work.RTInstance.PreAtlas` requires that, as a section of the (trivial)
bundle `E4 × (E4 →L[ℝ] E4 →L[ℝ] ℝ)`, it is smooth of all orders.

This module proves that:

* `Work.RTInstance.model_smooth` — the model of every chart layer is smooth.

The proof goes through the smoothness (`ContDiff ℝ ∞`) of the three families of bilinear forms:

* `uhsFactor_contDiff` — `s ↦ smoothTransition (s/δ) * s⁻¹ + (1 - smoothTransition (s/δ)) * δ⁻¹`
  is smooth, using the flatness of `Real.smoothTransition` at `0` (via
  `expNegInvGlue.contDiff_polynomial_eval_inv_mul`);
* `diagQuad_contDiff` — the diagonal form `diagQuad` is linear (hence smooth) in its coefficients;
* `flatModel_contDiff` — the flat model is constant.

The bundle part is `Bundle.contMDiffAt_section`, which reduces smoothness of a section of the
trivial bundle to smoothness of its coordinate expression.
-/
import Mathlib
import Submission.Work.RTInstance.Models

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter Polynomial
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace
open Bundle

namespace Work.RTInstance

/-- The model fibre of the metric models: the space of bilinear forms on `E4`. -/
abbrev RTForm4 : Type := E4 →L[ℝ] E4 →L[ℝ] ℝ

/-! ## Smoothness of the upper half space factor -/

/-- **`x ↦ x⁻¹ * smoothTransition x` is smooth.**  This is the only point where the flatness of
`Real.smoothTransition` at the origin is used. -/
lemma smoothTransition_inv_mul_contDiff :
    ContDiff ℝ ∞ (fun x : ℝ => x⁻¹ * Real.smoothTransition x) := by
  -- `x⁻¹ * smoothTransition x = (x⁻¹ * expNegInvGlue x) * (expNegInvGlue x + expNegInvGlue (1-x))⁻¹`
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => x⁻¹ * expNegInvGlue x) := by
    simpa using expNegInvGlue.contDiff_polynomial_eval_inv_mul (Polynomial.X : ℝ[X])
  have hD : ContDiff ℝ ∞ (fun x : ℝ => expNegInvGlue x + expNegInvGlue (1 - x)) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun x : ℝ => (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹) :=
    hD.inv (fun x => (Real.smoothTransition.pos_denom x).ne')
  simpa [Real.smoothTransition, div_eq_mul_inv, mul_assoc] using h1.mul h2

/-- **`uhsFactor δ` is smooth** for every real `δ`. -/
lemma uhsFactor_contDiff (δ : ℝ) : ContDiff ℝ ∞ (uhsFactor δ) := by
  rcases eq_or_ne δ 0 with rfl | hδ
  · -- for `δ = 0` the factor vanishes identically
    have h : uhsFactor 0 = fun _ : ℝ => 0 := by funext s; simp [uhsFactor]
    rw [h]; exact contDiff_const
  · -- rewrite `smoothTransition (s/δ) * s⁻¹` with the change of variable `x = s / δ`
    have hcomp : ContDiff ℝ ∞ (fun s : ℝ => (s / δ)⁻¹ * Real.smoothTransition (s / δ)) :=
      smoothTransition_inv_mul_contDiff.comp (contDiff_id.div_const δ)
    have hstc : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (s / δ)) :=
      Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)
    have hA' : ContDiff ℝ ∞
        (fun s : ℝ => δ⁻¹ * ((s / δ)⁻¹ * Real.smoothTransition (s / δ))) :=
      contDiff_const.mul hcomp
    have hA : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (s / δ) * s⁻¹) := by
      rw [← contDiffOn_univ]
      exact hA'.contDiffOn.congr (fun s _ => by rw [inv_div]; field_simp)
    have hB : ContDiff ℝ ∞ (fun s : ℝ => (1 - Real.smoothTransition (s / δ)) * δ⁻¹) :=
      (contDiff_const.sub hstc).mul contDiff_const
    change ContDiff ℝ ∞ (fun s : ℝ =>
      Real.smoothTransition (s / δ) * s⁻¹ + (1 - Real.smoothTransition (s / δ)) * δ⁻¹)
    exact hA.add hB

/-! ## Smoothness of the three models -/

/-- The total upper half space model is smooth. -/
lemma uhsModel_contDiff (δ : ℝ) : ContDiff ℝ ∞ (uhsModel δ) := by
  have h1 : ContDiff ℝ ∞ (fun q : E4 => uhsFactor δ (q 3)) :=
    (uhsFactor_contDiff δ).comp (coord4 3).contDiff
  have h2 : ContDiff ℝ ∞ (fun q : E4 => uhsFactor δ (q 3) ^ 2) := h1.pow 2
  have h3 : ContDiff ℝ ∞ (fun q : E4 =>
      (ContinuousLinearMap.toSpanSingleton ℝ (innerSL ℝ) : ℝ →L[ℝ] RTForm4)
        (uhsFactor δ (q 3) ^ 2)) :=
    (ContinuousLinearMap.contDiff _).comp h2
  have h4 : ContDiff ℝ ∞ (fun q : E4 => uhsFactor δ (q 3) ^ 2 • (innerSL ℝ : RTForm4)) := by
    rw [← contDiffOn_univ]
    exact h3.contDiffOn.congr (fun q _ => by rw [ContinuousLinearMap.toSpanSingleton_apply])
  convert h4 using 1
  · rfl
  · rfl

/-- The diagonal bilinear form is linear, hence smooth, in its coefficients. -/
lemma diagQuad_contDiff : ContDiff ℝ ∞ (fun c : Fin 4 → ℝ => diagQuad c) := by
  simp only [diagQuad]; fun_prop

/-- The warped filling model is smooth whenever the profile functions are. -/
lemma warpedModelA_contDiff (f h : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (warpedModelA f h) := by
  have hv : ContDiff ℝ ∞ (fun q : E4 => ![1, posExt f (1/8) (q 0)^2, h (q 0)^2, h (q 0)^2]) := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · show ContDiff ℝ ∞ (fun _ : E4 => (1:ℝ)); exact contDiff_const
    · show ContDiff ℝ ∞ (fun x : E4 => posExt f (1/8) (x 0)^2)
      simp only [posExt]; fun_prop
    · show ContDiff ℝ ∞ (fun x : E4 => h (x 0)^2); fun_prop
    · show ContDiff ℝ ∞ (fun x : E4 => h (x 0)^2); fun_prop
  have h := diagQuad_contDiff.comp hv
  convert h using 1
  rfl

/-- The flat core model is smooth (it is constant). -/
lemma flatModel_contDiff (h₀ : ℝ) : ContDiff ℝ ∞ (flatModel h₀) := by
  show ContDiff ℝ ∞ (fun q : E4 => flatModel h₀ q)
  simp only [flatModel]; fun_prop

/-- **The model of every chart layer is smooth**, as a map `E4 → E4 →L[ℝ] E4 →L[ℝ] ℝ`. -/
lemma ChartLayer_model_contDiff (l : ChartLayer) : ContDiff ℝ ∞ (l.model) := by
  cases l with
  | uhs δ => exact uhsModel_contDiff δ
  | warped P => exact warpedModelA_contDiff P.f P.h P.f_smooth P.h_smooth
  | flat h₀ => exact flatModel_contDiff h₀

/-! ## The section of the trivial bundle -/

/-- The trivialization of the trivial bundle is the identity, so its second coordinate
is the value of the section. -/
lemma trivializationAt_trivial_snd (x : E4) (y : RTForm4) :
    (trivializationAt RTForm4 (Bundle.Trivial E4 RTForm4) x ⟨x, y⟩).2 = y := by
  rw [show trivializationAt RTForm4 (Bundle.Trivial E4 RTForm4) x =
        Bundle.Trivial.trivialization E4 RTForm4 from rfl,
    Bundle.Trivial.trivialization_apply]

/-- **The model of a chart layer is a smooth section of the trivial bundle
`E4 × (E4 →L[ℝ] E4 →L[ℝ] ℝ)`.** -/
theorem model_smooth (l : ChartLayer) :
    ContMDiff (modelWithCornersSelf ℝ E4)
      ((modelWithCornersSelf ℝ E4).prod (modelWithCornersSelf ℝ (E4 →L[ℝ] E4 →L[ℝ] ℝ)))
      (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun q : E4 => Bundle.TotalSpace.mk' (E4 →L[ℝ] E4 →L[ℝ] ℝ) q (l.model q)) := by
  have hMd : ContMDiff 𝓘(ℝ, E4) 𝓘(ℝ, RTForm4) (((⊤ : ℕ∞) : WithTop ℕ∞)) (l.model) :=
    (ChartLayer_model_contDiff l).contMDiff
  intro q₀
  -- `Bundle.contMDiffAt_section` reduces the section to its trivialization coordinate
  rw [Bundle.contMDiffAt_section (F := RTForm4) (E := Bundle.Trivial E4 RTForm4) q₀]
  refine hMd.contMDiffAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  -- the trivialization of the trivial bundle is the identity
  exact trivializationAt_trivial_snd x (l.model x)

end Work.RTInstance
