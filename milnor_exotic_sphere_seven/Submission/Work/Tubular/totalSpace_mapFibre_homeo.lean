import Mathlib
import Submission.Work.Tubular.ThomComparison
import Submission.Work.Thom.manifoldP1
import Submission.Work.Agree.mapFibreIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Changing the model fibre of a real bundle is a homeomorphism of total spaces

For a real vector bundle `Z` over `B` (in the gluing-data model
`Work.TangentClasses.RealBundle B F ι = VectorBundleCore ℝ B F ι`) and a continuous linear
equivalence `e : F ≃L[ℝ] F'` of the model fibres, the bundle `Z.mapFibre e` has the same cover and
index map as `Z`, and transition functions `e ∘ Z.coordChange i j x ∘ e⁻¹`.  The fibrewise map `e`
is therefore a homeomorphism

  `Z.TotalSpace ≃ₜ (Z.mapFibre e).TotalSpace`

lying over the identity of the base; it preserves the zero sections and — because `e` is a linear
*equivalence* — the locus where the fibrewise norm vanishes.

The homeomorphism is produced as `(bundleIsoMapFibre e Z).toHomeomorph`, where
`bundleIsoMapFibre` is the canonical `Work.Thom.BundleIso Z (Z.mapFibre e)` whose fibrewise map is
`e`.  Its continuity is obtained from the general criterion
`Work.Thom.continuous_totalSpaceMap_clm_gen` for a fibrewise family of continuous linear maps
between two gluing data: in every pair of charts the trivialised matrix reduces, by the cocycle
condition of `Z`, to `e ∘ Z.coordChange i j`.
-/

namespace Work.Tubular

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F F' : Type}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {ι : Type}

/-- The map of total spaces induced by a change of the model fibre along `e : F ≃L[ℝ] F'`:
`⟨x, v⟩ ↦ ⟨x, e v⟩`. -/
def mapFibreFun (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) :
    Z.TotalSpace → (Z.mapFibre e).TotalSpace :=
  fun p => ⟨p.1, (e : F →L[ℝ] F') p.2⟩

@[simp] theorem mapFibreFun_apply (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    mapFibreFun e Z p = (⟨p.1, (e : F →L[ℝ] F') p.2⟩ : (Z.mapFibre e).TotalSpace) := rfl

/-- **The change of fibre is continuous on total spaces.** -/
theorem continuous_mapFibreFun (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) :
    Continuous (mapFibreFun e Z) := by
  show Continuous (fun p : Z.TotalSpace =>
      (⟨p.1, (e : F →L[ℝ] F') (show F from p.2)⟩ : (Z.mapFibre e).TotalSpace))
  refine Work.Thom.continuous_totalSpaceMap_clm_gen (𝕜 := ℝ) Z (Z.mapFibre e) (ContinuousMap.id B)
    (fun _ => (e : F →L[ℝ] F')) ?_
  intro i₁ i₂
  simp only [ContinuousMap.coe_id, id_eq, RealBundle.mapFibre_baseSet]
  rw [Set.preimage_id]
  refine ContinuousOn.congr (f := fun b => (e : F →L[ℝ] F') ∘SL Z.coordChange i₁ i₂ b) ?_ ?_
  · exact continuousOn_const.clm_comp (Z.continuousOn_coordChange i₁ i₂)
  · intro b hb
    beta_reduce
    rw [RealBundle.mapFibre_coordChange, RealBundle.mapFibre_indexAt]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [Z.coordChange_comp i₁ (Z.indexAt b) i₂ b ⟨⟨hb.1, Z.mem_baseSet_at b⟩, hb.2⟩ v]

/-- **The inverse change of fibre is continuous on total spaces.** -/
theorem continuous_mapFibreFun_symm (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) :
    Continuous (fun p : (Z.mapFibre e).TotalSpace =>
      (⟨p.1, (e.symm : F' →L[ℝ] F) (show F' from p.2)⟩ : Z.TotalSpace)) := by
  refine Work.Thom.continuous_totalSpaceMap_clm_gen (𝕜 := ℝ) (Z.mapFibre e) Z (ContinuousMap.id B)
    (fun _ => (e.symm : F' →L[ℝ] F)) ?_
  intro i₁ i₂
  simp only [ContinuousMap.coe_id, id_eq, RealBundle.mapFibre_baseSet]
  rw [Set.preimage_id]
  refine ContinuousOn.congr (f := fun b => Z.coordChange i₁ i₂ b ∘SL (e.symm : F' →L[ℝ] F)) ?_ ?_
  · exact (Z.continuousOn_coordChange i₁ i₂).clm_comp continuousOn_const
  · intro b hb
    beta_reduce
    rw [RealBundle.mapFibre_coordChange, RealBundle.mapFibre_indexAt]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [Z.coordChange_comp i₁ (Z.indexAt b) i₂ b ⟨⟨hb.1, Z.mem_baseSet_at b⟩, hb.2⟩ (e.symm v)]

/-- **The canonical bundle isomorphism `Z ≅ Z.mapFibre e`**, whose fibrewise map is `e`. -/
def bundleIsoMapFibre (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) :
    Work.Thom.BundleIso Z (Z.mapFibre e) where
  hom _ := (e : F →L[ℝ] F').toLinearMap
  inv _ := (e.symm : F' →L[ℝ] F).toLinearMap
  left_inv _ x := e.symm_apply_apply x
  right_inv _ y := e.apply_symm_apply y
  continuous_hom := continuous_mapFibreFun e Z
  continuous_inv := continuous_mapFibreFun_symm e Z

@[simp] theorem bundleIsoMapFibre_toHomeomorph_apply (e : F ≃L[ℝ] F') (Z : RealBundle B F ι)
    (p : Z.TotalSpace) :
    (bundleIsoMapFibre e Z).toHomeomorph p = mapFibreFun e Z p := rfl

/-- The fibrewise norm of the image is the norm of the image vector. -/
@[simp] theorem fibreNorm_mapFibreFun (e : F ≃L[ℝ] F') (Z : RealBundle B F ι)
    (p : Z.TotalSpace) :
    Work.Thom.fibreNorm (Z.mapFibre e) (mapFibreFun e Z p) =
      ‖(e : F →L[ℝ] F') p.2‖ := rfl

/-- The change of fibre preserves the zero section. -/
theorem mapFibreFun_zeroSection (e : F ≃L[ℝ] F') (Z : RealBundle B F ι) (x : B) :
    mapFibreFun e Z (Work.Thom.zeroSection Z x)
      = Work.Thom.zeroSection (Z.mapFibre e) x := by
  rw [Work.Thom.zeroSection_apply, mapFibreFun_apply, Work.Thom.zeroSection_apply]
  refine Bundle.TotalSpace.ext rfl ?_
  exact heq_of_eq (map_zero (e : F →L[ℝ] F'))

theorem totalSpace_mapFibre_homeo {B : Type} [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : F ≃L[ℝ] F') {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) :
    ∃ ψ : Z.TotalSpace ≃ₜ (Z.mapFibre e).TotalSpace,
      (∀ p : Z.TotalSpace, (ψ p).1 = p.1) ∧
      (∀ p : Z.TotalSpace, Work.Thom.fibreNorm (Z.mapFibre e) (ψ p) = 0
        ↔ Work.Thom.fibreNorm Z p = 0) ∧
      (∀ x : B, ψ (Work.Thom.zeroSection Z x)
        = Work.Thom.zeroSection (Z.mapFibre e) x) := by
  refine ⟨(bundleIsoMapFibre e Z).toHomeomorph, ?_, ?_, ?_⟩
  · intro p; rfl
  · intro p
    rw [bundleIsoMapFibre_toHomeomorph_apply, fibreNorm_mapFibreFun]
    show ‖(e : F →L[ℝ] F') (show F from p.2)‖ = 0 ↔ ‖(show F from p.2)‖ = 0
    rw [norm_eq_zero, norm_eq_zero]
    exact e.map_eq_zero_iff
  · intro x
    rw [bundleIsoMapFibre_toHomeomorph_apply, mapFibreFun_zeroSection]

end

end Work.Tubular
