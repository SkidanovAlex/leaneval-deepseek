import Mathlib
import Submission.Work.Noncompact.CompressionTube.CorridorDefs

/-!
# A self-map of `ℝ` with non-zero derivative is immersive

The reparametrised germ chain needs: if `θ : ℝ → ℝ` has non-zero derivative at `s`, then
`mfderiv MCreal MCreal θ s` is injective (so that the chain rule makes `γ ∘ θ` an immersion
whenever `γ` is).

The route here stays entirely at the **Fréchet** level, where no `TangentSpace`-model instances are
involved (that is the trap recorded in `Work.Noncompact.CompressionTube.injective_mfderiv_affine`):

* `HasStrictDerivAt.hasStrictFDerivAt_equiv` turns `deriv θ s ≠ 0` into an INVERTIBLE
  `HasStrictFDerivAt`;
* `HasStrictFDerivAt.localInverse` (inverse function theorem) produces a local left inverse `ψ`;
* `HasFDerivAt.comp` against `ψ ∘ θ =ᶠ[𝓝 s] id` exhibits a left inverse of `fderiv ℝ θ s`;
* `mfderiv_eq_fderiv` transfers the statement to the manifold model.
-/

namespace Work.Routing

open Filter
open scoped Manifold Topology

/-- A continuous linear map of `ℝ` with a left inverse is injective. -/
theorem injective_of_comp_eq_id {L M : ℝ →L[ℝ] ℝ} (h : M.comp L = 1) :
    Function.Injective L := by
  intro a b hab
  have h1 := congrArg (fun (N : ℝ →L[ℝ] ℝ) => N a) h
  have h2 := congrArg (fun (N : ℝ →L[ℝ] ℝ) => N b) h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h1 h2
  rw [hab] at h1
  exact h1.symm.trans h2

/-- **The bridge, at the Fréchet level.**  A self-map of `ℝ` with non-zero derivative at `s` (in the
strict sense) has injective Fréchet derivative there. -/
theorem injective_fderiv_of_deriv_ne_zero {θ : ℝ → ℝ} {s : ℝ}
    (hθ : HasStrictDerivAt θ (deriv θ s) s) (h : deriv θ s ≠ 0) :
    Function.Injective (fderiv ℝ θ s) := by
  set e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv θ s) h) with he
  have hsd : HasStrictFDerivAt θ (e : ℝ →L[ℝ] ℝ) s := hθ.hasStrictFDerivAt_equiv h
  set ψ : ℝ → ℝ := hsd.localInverse θ with hψ
  have hψd : HasStrictFDerivAt ψ (e.symm : ℝ →L[ℝ] ℝ) (θ s) := hsd.to_localInverse
  have hone : (fderiv ℝ ψ (θ s)).comp (fderiv ℝ θ s) = 1 := by
    rw [hψd.hasFDerivAt.fderiv, hsd.hasFDerivAt.fderiv]
    ext x
    simp
  exact injective_of_comp_eq_id hone

/-- **The bridge in the form the manifold chain rule consumes.** -/
theorem injective_mfderiv_of_deriv_ne_zero {θ : ℝ → ℝ} {s : ℝ}
    (hθ : HasStrictDerivAt θ (deriv θ s) s) (h : deriv θ s ≠ 0) :
    Function.Injective
      (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) θ s) := by
  have hm : (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) θ s)
      = fderiv ℝ θ s := mfderiv_eq_fderiv
  rw [hm]
  exact injective_fderiv_of_deriv_ne_zero hθ h

end Work.Routing
