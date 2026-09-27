import Submission.UnifDeps
import Submission.Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph

open LeanEval.Geometry
open scoped Manifold ContDiff UpperHalfPlane

noncomputable section

open TopologicalSpace

namespace Submission.Helpers

/-- The complex plane is diffeomorphic to itself as a complex manifold.  In particular the
first disjunct of the uniformization conclusion holds for `X = ℂ`. -/
theorem complex_plane_realizes_plane : Nonempty (ℂ ≃ₘ⟮mℂ, mℂ⟯ ℂ) :=
  ⟨Diffeomorph.refl mℂ ℂ ∞⟩

/-- The upper half plane is diffeomorphic to itself as a complex manifold.  In particular
the second disjunct of the uniformization conclusion holds for `X = UpperHalfPlane`. -/
theorem upper_half_plane_realizes_upper_half_plane :
    Nonempty (UpperHalfPlane ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  ⟨Diffeomorph.refl mℂ UpperHalfPlane ∞⟩

/-- `ℂ` is non-compact (via the closed embedding of `ℝ`). -/
theorem not_compactSpace_complex : ¬ CompactSpace ℂ := by
  rw [not_compactSpace_iff]
  exact Complex.isometry_ofReal.isClosedEmbedding.noncompactSpace

/-- The upper half plane is non-compact. -/
theorem not_compactSpace_upperHalfPlane : ¬ CompactSpace UpperHalfPlane := by
  rw [not_compactSpace_iff]
  infer_instance

/-- The open upper half plane of `ℂ`, bundled as an open subset. -/
abbrev HPlaneOpen : TopologicalSpace.Opens ℂ :=
  ⟨UpperHalfPlane.upperHalfPlaneSet, UpperHalfPlane.isOpen_upperHalfPlaneSet⟩

/-- The inclusion of `ℍ` into its image in `ℂ`. -/
def toU (z : UpperHalfPlane) : HPlaneOpen :=
  ⟨(z : ℂ), by simpa [HPlaneOpen, UpperHalfPlane.upperHalfPlaneSet] using z.coe_im_pos⟩

/-- The inverse of the inclusion of `ℍ` into `ℂ`. -/
def fromU (u : HPlaneOpen) : UpperHalfPlane :=
  ⟨u.1, by
    have hu := u.property
    change 0 < (u : ℂ).im at hu
    simpa using hu⟩

/-- The underlying equivalence between `ℍ` and its image in `ℂ`. -/
def equivUHP : UpperHalfPlane ≃ HPlaneOpen where
  toFun := toU
  invFun := fromU
  left_inv z := by
    apply UpperHalfPlane.ext
    simp [toU, fromU]
  right_inv u := by
    ext
    simp [toU, fromU]

lemma contMDiff_toU : ContMDiff mℂ mℂ ∞ (toU : UpperHalfPlane → HPlaneOpen) := by
  rw [← ContMDiff.subtypeVal_comp_iff (U := HPlaneOpen) (f := toU) (I := mℂ) (I' := mℂ)]
  change ContMDiff mℂ mℂ ∞ (UpperHalfPlane.coe : UpperHalfPlane → ℂ)
  simpa [mℂ] using (UpperHalfPlane.contMDiff_coe : ContMDiff mℂ mℂ ∞ UpperHalfPlane.coe)

lemma contMDiff_fromU : ContMDiff mℂ mℂ ∞ (fromU : HPlaneOpen → UpperHalfPlane) := by
  apply ContMDiff.of_comp_isOpenEmbedding (h' := UpperHalfPlane.isOpenEmbedding_coe)
  change ContMDiff mℂ mℂ ∞ (Subtype.val : HPlaneOpen → ℂ)
  simpa [mℂ] using
    (contMDiff_subtype_val (I := mℂ) (n := ∞) (U := HPlaneOpen) :
      ContMDiff mℂ mℂ ∞ (Subtype.val : HPlaneOpen → ℂ))

/-- The upper half plane, with its complex manifold structure, is diffeomorphic to the open
subset of `ℂ` consisting of the points of positive imaginary part (which carries the standard
complex manifold structure of an open subset).  This is the bridge between "`X` is
biholomorphic to the upper half plane in `ℂ`" and the conclusion of the uniformization
theorem "`X ≃ₘ UpperHalfPlane`". -/
def uhpOpenDiffeomorph : UpperHalfPlane ≃ₘ⟮mℂ, mℂ⟯ HPlaneOpen where
  toEquiv := equivUHP
  contMDiff_toFun := by
    simpa [equivUHP] using contMDiff_toU
  contMDiff_invFun := by
    simpa [equivUHP] using contMDiff_fromU

/-- First disjunct of the uniformization conclusion follows from a complex diffeomorphism
to the plane. -/
theorem uniformization_of_plane {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₘ⟮mℂ, mℂ⟯ ℂ) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  Or.inl ⟨e⟩

/-- Second disjunct of the uniformization conclusion follows from a complex diffeomorphism
to the upper half plane. -/
theorem uniformization_of_upperHalfPlane {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  Or.inr ⟨e⟩

/-- A diffeomorphism of a manifold to the open upper-half-plane subset of `ℂ` yields a
complex diffeomorphism to `UpperHalfPlane` (compose with the canonical identification), hence
the second disjunct. -/
theorem uniformization_of_upperHalfPlane_openSubset {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (e : X ≃ₘ⟮mℂ, mℂ⟯ HPlaneOpen) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  Or.inr ⟨e.trans uhpOpenDiffeomorph.symm⟩

/-- The upper half plane `ℍ` is diffeomorphic, as a complex manifold, to the open subset
`{z : ℂ | 0 < z.im}` of `ℂ`. -/
theorem upperHalfPlane_equiv_openSubset :
    Nonempty (UpperHalfPlane ≃ₘ⟮mℂ, mℂ⟯ HPlaneOpen) :=
  ⟨uhpOpenDiffeomorph⟩


/-- The open unit disc as an open subset of `ℂ`. -/
abbrev DiscOpen : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩

/-- A diffeomorphism of a manifold to the open unit disc of `ℂ` yields a complex
diffeomorphism to `UpperHalfPlane` (compose with the Cayley identification
`halfPlane_disc_diffeomorph`), hence the second disjunct. -/
theorem uniformization_of_unitDisc_openSubset {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (e : X ≃ₘ⟮mℂ, mℂ⟯ DiscOpen) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  rcases (Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph :
      Nonempty (UpperHalfPlane ≃ₘ⟮mℂ, mℂ⟯ DiscOpen)) with ⟨d⟩
  exact Or.inr ⟨e.trans d.symm⟩

end Submission.Helpers

end
