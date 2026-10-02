import Mathlib
import Submission.Work.Agree.clutchShiftDefs
import Submission.Work.Agree.continuousOn_hTex
import Submission.Work.Agree.continuousOn_hTexInv
import Submission.Work.Thom.Iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

/-!
# The `(a,b)`-shift of the complexified Milnor bundles

`Work.Agree.clutchShift` : the complexification of the rank-`4` real bundle `L^aR^b` over
`S⁴ = OnePoint ℝ⁴` is isomorphic, as a complex bundle, to the complexification of `L^{a-b}`.
The gauge and its algebra are in `Submission/Work/Agree/clutchShiftDefs.lean`; the two continuity
lemmas are `Work.Agree.continuousOn_hTex` and `Work.Agree.continuousOn_hTexInv`.
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-- Port helper (Lean v4.35): a `Work.Thom.BundleIso` from a fibrewise family of continuous linear
maps whose chart expressions are continuous, stated for general vector bundle cores so that it
elaborates without unfolding the concrete fibres of the complexified Milnor bundles. -/
private theorem nonempty_bundleIso_of_clm_gen {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B] {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {ι₁ ι₂ : Type*} (Z₁ : VectorBundleCore 𝕜 B F₁ ι₁) (Z₂ : VectorBundleCore 𝕜 B F₂ ι₂)
    (T : B → F₁ →L[𝕜] F₂) (U : B → F₂ →L[𝕜] F₁)
    (hT : ∀ i₁ i₂, ContinuousOn (fun b =>
      (Z₂.coordChange (Z₂.indexAt b) i₂ b).comp ((T b).comp (Z₁.coordChange i₁ (Z₁.indexAt b) b)))
      (Z₁.baseSet i₁ ∩ Z₂.baseSet i₂))
    (hU : ∀ i₂ i₁, ContinuousOn (fun b =>
      (Z₁.coordChange (Z₁.indexAt b) i₁ b).comp ((U b).comp (Z₂.coordChange i₂ (Z₂.indexAt b) b)))
      (Z₂.baseSet i₂ ∩ Z₁.baseSet i₁))
    (left_inv : ∀ b (x : F₁), U b (T b x) = x)
    (right_inv : ∀ b (y : F₂), T b (U b y) = y) :
    Nonempty (Work.Thom.BundleIso Z₁ Z₂) := by
  have hcont₁ : Continuous (fun p : Z₁.TotalSpace => (⟨p.1, T p.1 p.2⟩ : Z₂.TotalSpace)) :=
    Work.Thom.continuous_totalSpaceMap_clm_gen Z₁ Z₂ (ContinuousMap.id B) T fun i₁ i₂ => by
      simpa using hT i₁ i₂
  have hcont₂ : Continuous (fun p : Z₂.TotalSpace => (⟨p.1, U p.1 p.2⟩ : Z₁.TotalSpace)) :=
    Work.Thom.continuous_totalSpaceMap_clm_gen Z₂ Z₁ (ContinuousMap.id B) U fun i₂ i₁ => by
      simpa using hU i₂ i₁
  exact ⟨{ hom := fun b => (T b : F₁ →ₗ[𝕜] F₂)
           inv := fun b => (U b : F₂ →ₗ[𝕜] F₁)
           left_inv := left_inv
           right_inv := right_inv
           continuous_hom := hcont₁
           continuous_inv := hcont₂ }⟩

theorem clutchShift (a b : ℤ) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.complexificationCore (Work.Agree.clutchBundle a b))
      (Work.Thom.complexificationCore (Work.Agree.clutchBundle (a - b) 0))) :=
  nonempty_bundleIso_of_clm_gen (ZZ a b) (ZZ (a - b) 0) (gaugeOp b) (gaugeInvOp b)
    (fun i₁ i₂ => continuousOn_hTex a b i₁ i₂) (fun i₂ i₁ => continuousOn_hTexInv a b i₁ i₂)
    (fun p x => by
      rw [← ContinuousLinearMap.mul_apply, gaugeInvOp_mul_gaugeOp, ContinuousLinearMap.one_apply])
    (fun p y => by
      rw [← ContinuousLinearMap.mul_apply, gaugeOp_mul_gaugeInvOp, ContinuousLinearMap.one_apply])

end

end Work.Agree
