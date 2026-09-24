import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open scoped Manifold ContDiff UpperHalfPlane
open TopologicalSpace

namespace Commons.Analysis.Complex.UpperHalfPlane

/-- The open upper half plane of `ℂ`, bundled as an open subset of `ℂ`. -/
private abbrev HPlaneOpen : TopologicalSpace.Opens ℂ :=
  ⟨{z : ℂ | 0 < z.im}, UpperHalfPlane.isOpen_upperHalfPlaneSet⟩

/-- The inclusion of `ℍ` into its image in `ℂ`. -/
private def toU (z : UpperHalfPlane) : HPlaneOpen :=
  ⟨(z : ℂ), by simpa [HPlaneOpen] using z.coe_im_pos⟩

/-- The inverse of the inclusion of `ℍ` into `ℂ`. -/
private def fromU (u : HPlaneOpen) : UpperHalfPlane :=
  ⟨u.1, by
    have hu := u.property
    change 0 < (u : ℂ).im at hu
    simpa using hu⟩

/-- The underlying equivalence between `ℍ` and its image in `ℂ`. -/
private def equivUHP : UpperHalfPlane ≃ HPlaneOpen where
  toFun := toU
  invFun := fromU
  left_inv z := by
    apply UpperHalfPlane.ext
    simp [toU, fromU]
  right_inv u := by
    ext
    simp [toU, fromU]

private lemma contMDiff_toU :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ (toU : UpperHalfPlane → HPlaneOpen) := by
  rw [← ContMDiff.subtypeVal_comp_iff (U := HPlaneOpen) (f := toU)
    (I := modelWithCornersSelf ℂ ℂ) (I' := modelWithCornersSelf ℂ ℂ)]
  change ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
    (UpperHalfPlane.coe : UpperHalfPlane → ℂ)
  simpa using (UpperHalfPlane.contMDiff_coe : ContMDiff (modelWithCornersSelf ℂ ℂ)
    (modelWithCornersSelf ℂ ℂ) ∞ UpperHalfPlane.coe)

private lemma contMDiff_fromU :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ (fromU : HPlaneOpen → UpperHalfPlane) := by
  apply ContMDiff.of_comp_isOpenEmbedding (h' := UpperHalfPlane.isOpenEmbedding_coe)
  change ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ (Subtype.val : HPlaneOpen → ℂ)
  simpa using
    (contMDiff_subtype_val (I := modelWithCornersSelf ℂ ℂ) (n := ∞) (U := HPlaneOpen) :
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ (Subtype.val : HPlaneOpen → ℂ))

/-- The upper half plane is diffeomorphic as a complex manifold to the open subset
`{z : ℂ | 0 < z.im}` of `ℂ` (endowed with its standard open-subset manifold structure). -/
theorem uhpOpenDiffeomorph :
    Nonempty (UpperHalfPlane ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯
      (⟨{z : ℂ | 0 < z.im}, UpperHalfPlane.isOpen_upperHalfPlaneSet⟩ : TopologicalSpace.Opens ℂ)) := by
  refine ⟨?dif⟩
  let e : UpperHalfPlane ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ HPlaneOpen := by
    refine { toEquiv := equivUHP, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
    · simpa [equivUHP] using contMDiff_toU
    · simpa [equivUHP] using contMDiff_fromU
  exact e

end Commons.Analysis.Complex.UpperHalfPlane
