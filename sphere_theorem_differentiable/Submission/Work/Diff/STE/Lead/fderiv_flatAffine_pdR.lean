import Mathlib
import Submission.Work.Diff.STE.Lead.chartMatJetDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chain rule for the affine flat coordinate map `flatAffine`

`Work.Diff.STE.Lead.flatAffine c` is the affine map `z ↦ (finBasis.equivFun)⁻¹ (c + z)` of the
model space `E ≃ (Fin (finrank ℝ E) → ℝ)`.  Its derivative at every point is the linear map
`flatLin E := ((finBasis.equivFun).symm : (Fin (finrank ℝ E) → ℝ) →ₗ[ℝ] E)`, and
`flatLin E (Pi.single p 1) = bB p`.

The main consequence (the statement of this file) is the chain rule

`fderiv ℝ F (flatAffine c z) (bB p) = pdR p (fun w => F (flatAffine c w)) z`,

i.e. the directional derivative of `F` at the point of flat coordinate `z` along the `p`-th basis
vector `bB p` of the model space is the `p`-th flat partial derivative of `F ∘ flatAffine` at `z`.

This is STEP 2 of the proof of `chartMatJet_sharp` (see `chartMatJet_sharp.lean`).
-/

namespace Work.Diff.STE.Lead

/-- The linear map underlying the affine map `flatAffine`: the inverse coordinate equivalence
`(Fin (finrank ℝ E) → ℝ) ≃ₗ[ℝ] E` of the canonical basis `finBasis`, made continuous. -/
noncomputable def flatLin (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E :=
  (((Module.finBasis ℝ E).equivFun.symm).toContinuousLinearEquiv :
    (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E)

/-- `flatAffine c` is the translation by `c` followed by `flatLin`. -/
lemma flatAffine_eq_flatLin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    flatAffine (E := E) c = fun z => flatLin E (c + z) := by
  funext z
  rfl

/-- The canonical basis vector of the flat coordinate space maps back to `bB p`. -/
lemma flatLin_apply_single {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : Fin (Module.finrank ℝ E)) :
    flatLin E (Pi.single p 1) = Work.Diff.EXT.bB (E := E) p := by
  simp [flatLin]

/-- The derivative of the affine map `flatAffine c` is the constant `flatLin E`. -/
lemma hasFDerivAt_flatAffine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (c : Fin (Module.finrank ℝ E) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    HasFDerivAt (flatAffine (E := E) c) (flatLin E) z := by
  rw [flatAffine_eq_flatLin (E := E) c]
  have h1 : HasFDerivAt (fun y : Fin (Module.finrank ℝ E) → ℝ => c + y)
      (ContinuousLinearMap.id ℝ (Fin (Module.finrank ℝ E) → ℝ)) z := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) z).const_add c
  have h2 := (flatLin E).hasFDerivAt.comp z h1
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using h2

/-- The Fréchet derivative of the affine map `flatAffine c` is the constant `flatLin E`. -/
lemma fderiv_flatAffine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (c : Fin (Module.finrank ℝ E) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    fderiv ℝ (flatAffine (E := E) c) z = flatLin E :=
  (hasFDerivAt_flatAffine (E := E) c z).fderiv

/-- **Chain rule for the affine flat coordinate map.**  For `F` twice continuously differentiable
at the point of flat coordinate `z`, the derivative of `F` along the `p`-th basis vector `bB p` of
the model space equals the `p`-th flat partial derivative of `F ∘ flatAffine` at `z`. -/
theorem fderiv_flatAffine_pdR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (c : Fin (Module.finrank ℝ E) → ℝ) {F : E → ℝ} {z : Fin (Module.finrank ℝ E) → ℝ}
    (hF : ContDiffAt ℝ 2 F (Work.Diff.STE.Lead.flatAffine (E := E) c z))
    (p : Fin (Module.finrank ℝ E)) :
    fderiv ℝ F (Work.Diff.STE.Lead.flatAffine (E := E) c z) (Work.Diff.EXT.bB (E := E) p)
      = Work.Diff.STE.pdR p (fun w => F (Work.Diff.STE.Lead.flatAffine (E := E) c w)) z := by
  have hL := hasFDerivAt_flatAffine (E := E) c z
  have hFD : HasFDerivAt (fun w => F (Work.Diff.STE.Lead.flatAffine (E := E) c w))
      ((fderiv ℝ F (Work.Diff.STE.Lead.flatAffine (E := E) c z)).comp (flatLin E)) z := by
    have h := (hF.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp z hL
    simpa only [Function.comp_def] using h
  rw [Work.Diff.STE.pdR, hFD.fderiv]
  simp only [ContinuousLinearMap.comp_apply, flatLin_apply_single]

end Work.Diff.STE.Lead
