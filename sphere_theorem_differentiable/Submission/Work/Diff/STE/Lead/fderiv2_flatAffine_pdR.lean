import Mathlib
import Submission.Work.Diff.STE.Lead.chartMatJetDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second derivative of a function pulled back along the flat affine chart map

`flatAffine c z = (finBasis.equivFun)⁻¹ (c + z)` is the flat coordinate map of the chart at a
point `x₀` of a manifold (see `chartMatJetDefs`).  The main result here,

`Work.Diff.STE.Lead.fderiv2_flatAffine_pdR`,

identifies the second derivative of `F : E → ℝ` at `flatAffine c z` in the directions
`bB p = finBasis p` with the iterated coordinate partial derivative `∂_q ∂_p` of the pulled-back
function `w ↦ F (flatAffine c w)` at `z`.

The proof is a general reparametrisation statement (`fderiv2_affine_reparam`): for a continuous
linear map `A` and a vector `b`, the second derivative of `F` at `b + A z` in the directions
`A u`, `A v` equals `∂_v ∂_u` of `w ↦ F (b + A w)` at `z`.  It is proved by the chain rule
twice (the outer derivative `fderiv F` and the evaluation of a continuous linear map), the
symmetry of the second derivative (`IsSymmSndFDerivAt`), and congruence of the `fderiv` along a
germ.

The gluing vocabulary is the linear map `flatLM E`, the continuous-linear version of
`(finBasis.equivFun)⁻¹`, together with `flatAffine_eq_flatLM` and `flatLM_single`.
-/

noncomputable section

namespace Work.Diff.STE.Lead

set_option linter.unusedSectionVars false

open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The canonical linear identification of the flat coordinate space
`Fin (finrank ℝ E) → ℝ` with `E`, as a continuous linear map. -/
def flatLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E :=
  (Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap

lemma flatLM_apply (x : Fin (Module.finrank ℝ E) → ℝ) :
    flatLM E x = (Module.finBasis ℝ E).equivFun.symm x := by
  rw [flatLM, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_toLinearMap]

/-- The affine flat coordinate map of the chart at a point of flat coordinate `c` is
`z ↦ flatLM c + flatLM z`. -/
lemma flatAffine_eq_flatLM (c z : Fin (Module.finrank ℝ E) → ℝ) :
    flatAffine (E := E) c z = flatLM E c + flatLM E z := by
  simp only [flatAffine_apply, flatLM_apply, map_add]

/-- `flatLM` of the `p`-th canonical basis vector of the coordinate space is the `p`-th vector of
the canonical basis of `E`. -/
lemma flatLM_single (p : Fin (Module.finrank ℝ E)) :
    flatLM E (Pi.single p (1 : ℝ)) = Work.Diff.EXT.bB (E := E) p := by
  rw [flatLM_apply, equivFun_symm_single]

/-- **Reparametrisation of the second derivative by an affine map.**
For a continuous linear map `A : E' →L[ℝ] E`, a vector `b : E` and `F : E → ℝ` which is `C²` at
`b + A z`, the second derivative of `F` at `b + A z` in the directions `A u`, `A v` is the
second derivative at `z` of `w ↦ F (b + A w)` in the directions `u`, `v`. -/
lemma fderiv2_affine_reparam {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (A : E' →L[ℝ] E) (b : E) {F : E → ℝ} {z : E'}
    (hF : ContDiffAt ℝ 2 F (b + A z)) (u v : E') :
    (fderiv ℝ (fun y : E => fderiv ℝ F y) (b + A z) (A u)) (A v)
      = fderiv ℝ (fun w => fderiv ℝ (fun v => F (b + A v)) w u) z v := by
  -- the affine map `v ↦ b + A v` is differentiable with derivative `A`
  have hA : HasFDerivAt (fun v : E' => b + A v) A z :=
    (ContinuousLinearMap.hasFDerivAt A).const_add b
  -- `fderiv F` is `C¹` (hence differentiable) at `b + A z`
  have hDF : ContDiffAt ℝ 1 (fun y : E => fderiv ℝ F y) (b + A z) :=
    hF.fderiv_right (by norm_num)
  have hDF' : DifferentiableAt ℝ (fun y : E => fderiv ℝ F y) (b + A z) :=
    hDF.differentiableAt (by norm_num)
  -- the derivative of `w ↦ fderiv F (b + A w)`
  have hΨ : HasFDerivAt (fun w : E' => fderiv ℝ F (b + A w))
      ((fderiv ℝ (fun y : E => fderiv ℝ F y) (b + A z)).comp A) z := by
    have h := (hDF'.hasFDerivAt).comp z hA
    exact h
  -- the evaluation map `L ↦ L (A u)` as a continuous linear map
  set ev : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (A u) with hev
  have hev' : HasFDerivAt (⇑ev) ev (fderiv ℝ F (b + A z)) :=
    ContinuousLinearMap.hasFDerivAt ev
  have hcomp : HasFDerivAt (⇑ev ∘ fun w : E' => fderiv ℝ F (b + A w))
      (ev.comp ((fderiv ℝ (fun y : E => fderiv ℝ F y) (b + A z)).comp A)) z := by
    have h := hev'.comp z hΨ
    exact h
  -- the two candidate `u`-derivatives agree near `z`
  have hgerm : ∀ᶠ w in nhds z,
      fderiv ℝ (fun v : E' => F (b + A v)) w = (fderiv ℝ F (b + A w)).comp A := by
    have hev2 : ∀ᶠ w in nhds z, ContDiffAt ℝ 2 F (b + A w) :=
      ((continuous_const.add A.continuous).tendsto z).eventually (hF.eventually (by norm_num))
    filter_upwards [hev2] with w hw
    have h1 : HasFDerivAt (fun v : E' => F (b + A v)) ((fderiv ℝ F (b + A w)).comp A) w :=
      (hw.differentiableAt (by norm_num)).hasFDerivAt.comp w
        ((ContinuousLinearMap.hasFDerivAt A).const_add b)
    exact h1.fderiv
  have hFunEv : (fun w : E' => fderiv ℝ (fun v : E' => F (b + A v)) w u)
      =ᶠ[nhds z] (⇑ev ∘ fun w : E' => fderiv ℝ F (b + A w)) := by
    filter_upwards [hgerm] with w hw
    rw [Function.comp_apply, hw]
    simp [ev, ContinuousLinearMap.apply_apply]
  have key : fderiv ℝ (fun w : E' => fderiv ℝ (fun v : E' => F (b + A v)) w u) z
      = ev.comp ((fderiv ℝ (fun y : E => fderiv ℝ F y) (b + A z)).comp A) := by
    rw [hFunEv.fderiv_eq, hcomp.fderiv]
  -- assemble, using the symmetry of the second derivative of `F`
  calc (fderiv ℝ (fun y : E => fderiv ℝ F y) (b + A z) (A u)) (A v)
      = ((fderiv ℝ (fun y : E => fderiv ℝ F y) (b + A z) (A v)) (A u)) :=
        (hF.isSymmSndFDerivAt (by simp)).eq (A u) (A v)
    _ = (ev.comp ((fderiv ℝ (fun y : E => fderiv ℝ F y) (b + A z)).comp A)) v := by
        simp [ev, ContinuousLinearMap.apply_apply]
    _ = fderiv ℝ (fun w : E' => fderiv ℝ (fun v : E' => F (b + A v)) w u) z v := by
        rw [key]

theorem fderiv2_flatAffine_pdR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (c : Fin (Module.finrank ℝ E) → ℝ) {F : E → ℝ} {z : Fin (Module.finrank ℝ E) → ℝ}
    (hF : ContDiffAt ℝ 2 F (Work.Diff.STE.Lead.flatAffine (E := E) c z))
    (p q : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ (fun y : E => fderiv ℝ F y) (Work.Diff.STE.Lead.flatAffine (E := E) c z)
        (Work.Diff.EXT.bB (E := E) p)) (Work.Diff.EXT.bB (E := E) q)
      = Work.Diff.STE.pdR q (Work.Diff.STE.pdR p
          (fun w => F (Work.Diff.STE.Lead.flatAffine (E := E) c w))) z := by
  -- rewrite the base point in terms of `flatLM`
  rw [flatAffine_eq_flatLM] at hF
  -- the pulled-back function is `w ↦ F (flatLM c + flatLM w)`
  have hinner : (fun w : Fin (Module.finrank ℝ E) → ℝ => F (flatAffine (E := E) c w))
      = fun w => F (flatLM E c + flatLM E w) := by
    funext w; rw [flatAffine_eq_flatLM]
  have h := fderiv2_affine_reparam (E := E) (E' := Fin (Module.finrank ℝ E) → ℝ)
      (A := flatLM E) (b := flatLM E c) (F := F) (z := z) hF (Pi.single p 1) (Pi.single q 1)
  rw [hinner]
  rw [flatAffine_eq_flatLM c z]
  rw [← flatLM_single (E := E) p, ← flatLM_single (E := E) q]
  exact h

end Work.Diff.STE.Lead
