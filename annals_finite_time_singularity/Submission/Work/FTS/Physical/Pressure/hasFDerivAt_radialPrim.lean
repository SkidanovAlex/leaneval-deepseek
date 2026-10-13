/-
# `Work.FTS.Physical.Pressure.hasFDerivAt_radialPrim`

The radial primitive `p(x,t) = ∫₀¹ ⟪G(sx,t), x⟫ ds` of a curl-free field `G` has gradient `G`:

  `hasFDerivAt_radialPrim : HasFDerivAt (fun y => ∫₀¹ ⟪G(sy,t), y⟫) (⟪G(x,t), ·⟫) x`.

The mathematical content is the Poincaré lemma on `ℝ³` (star-shaped, hence simply connected):
a `C¹` curl-free field `G(·,t)` is the gradient of a potential `P`, and then the fundamental
theorem of calculus along the segment `[0,y]` gives

  `∫₀¹ ⟪G(sy,t), y⟫ ds = P y - P 0`,

so the radial primitive *is* `P` up to an additive constant and its derivative is `G(x,t)`.
The route through the potential avoids differentiating under the integral sign altogether.

Two pieces of the argument are delegated:

* `Work.FTS.Physical.Pressure.fderiv_symm_of_vorticity_eq_zero` — the linear algebra fact that
  `vorticity F x = 0` says exactly that `fderiv ℝ F x` is self-adjoint;
* `Work.FTS.Physical.Pressure.integral_radial_eq_sub` — the chain rule + FTC identity
  `∫₀¹ ⟪F(s•y), y⟫ ds = P y - P 0` for `∇P = F`.

The Poincaré lemma itself is Mathlib's `Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`
applied to the closed `1`-form `ω z = ⟪F z, ·⟫` on the convex set `ℝ³`, giving a primitive
*with* the `HasFDerivAt` regularity (this is the form needed here: the `fderiv`-shaped variant
`Work.LWP.CurlFree.curlFree_isGradient` does not by itself record differentiability of the
primitive).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Pressure.fderiv_symm_of_vorticity_eq_zero
import Submission.Work.FTS.Physical.Pressure.integral_radial_eq_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Topology

set_option autoImplicit false

namespace Work.FTS.Physical.Pressure

/-- **Poincaré lemma on `ℝ³`, with the regularity of the primitive.**  A `C¹`, curl-free vector
field on `ℝ³` is the gradient of a `C¹` scalar potential: there is `P` with
`HasFDerivAt P (innerSL ℝ (F z)) z` for every `z`.

The `1`-form `ω z = ⟪F z, ·⟫` is closed on the convex set `ℝ³`: its derivative is
`innerSL ℝ ∘ fderiv ℝ F z`, which is symmetric because `F` is curl-free
(`fderiv_symm_of_vorticity_eq_zero`).  Mathlib's
`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric` (`Mathlib.MeasureTheory.Integral.
CurveIntegral.Poincare`) then produces the primitive. -/
theorem exists_hasFDerivAt_of_curlFree {F : R3 → R3} (hF : ContDiff ℝ 1 F)
    (hcurl : ∀ x, vorticity F x = 0) :
    ∃ P : R3 → ℝ, ∀ x, HasFDerivAt P (innerSL ℝ (F x)) x := by
  let ω : R3 → (R3 →L[ℝ] ℝ) := fun z => innerSL ℝ (F z)
  have hω : DifferentiableOn ℝ ω Set.univ := by
    apply Differentiable.differentiableOn
    exact (ContinuousLinearMap.differentiable (innerSL ℝ : R3 →L[ℝ] (R3 →L[ℝ] ℝ))).comp
      hF.differentiable_one
  have hfderivω : ∀ a, fderiv ℝ ω a =
      (innerSL ℝ : R3 →L[ℝ] (R3 →L[ℝ] ℝ)).comp (fderiv ℝ F a) := by
    intro a
    have hF' : HasFDerivAt F (fderiv ℝ F a) a := (hF.differentiable_one a).hasFDerivAt
    exact ((ContinuousLinearMap.hasFDerivAt (innerSL ℝ : R3 →L[ℝ] (R3 →L[ℝ] ℝ))
      (x := F a)).comp a hF').fderiv
  have hsymm : ∀ a ∈ Set.univ, ∀ x y, (fderiv ℝ ω a x) y = (fderiv ℝ ω a y) x := by
    intro a _ x y
    rw [hfderivω a, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, innerSL_apply_apply]
    exact fderiv_symm_of_vorticity_eq_zero (hcurl a) x y
  obtain ⟨P, hP⟩ := Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric
    (𝕜 := ℝ) (E := R3) (F := ℝ) convex_univ isOpen_univ hω hsymm
  exact ⟨P, fun x => hP x (Set.mem_univ x)⟩

theorem hasFDerivAt_radialPrim {G : Work.FTS.Physical.R3 → ℝ → Work.FTS.Physical.R3} {x : Work.FTS.Physical.R3} {t : ℝ} (hC1 : ContDiff ℝ 1 (fun y => G y t)) (hcurl : ∀ y : Work.FTS.Physical.R3, FiniteTimeSingularity.vorticity (fun z => G z t) y = 0) : HasFDerivAt (fun y => ∫ s in (0 : ℝ)..1, inner ℝ (G (s • y) t) y) (innerSL ℝ (G x t)) x := by
  obtain ⟨P, hP⟩ := exists_hasFDerivAt_of_curlFree hC1 hcurl
  have hfun : (fun y => ∫ s in (0 : ℝ)..1, inner ℝ (G (s • y) t) y)
      = fun y => P y - P 0 := by
    funext y
    exact integral_radial_eq_sub hC1.continuous hP y
  rw [hfun]
  exact (hP x).sub_const (P 0)

end Work.FTS.Physical.Pressure
