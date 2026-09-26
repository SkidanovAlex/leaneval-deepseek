import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

/-!
# Slicing data transport along an ambient homeomorphism

The slicing datum `SliceData P S` of `Work.Topology.SphereSlicing.Defs` is a purely
topological object: it is phrased in terms of closed curves of the torus `P`, of embeddings of
the disc, and of the openness in `S` of the interior of a spanning disc.  Consequently it is
carried along by a homeomorphism of `ℝ³`: a slicing of the sphere `S` by the standard torus
transports to a slicing of `φ '' S` by the image torus `ParamTorus.mapHomeomorph φ`, and
conversely.

This file proves that transport (`SliceData.mapForward`, `SliceData.mapBack`) and deduces

  `sliceData_map_homeomorph_iff` : `Nonempty (SliceData (mapHomeomorph φ) (φ '' S)) ↔
  Nonempty (SliceData standard S)`.

The two constructions are inverse to each other on the nose, so the statement is an
equivalence of `Nonempty`-propositions and the two directions are proved independently here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Work.CoreTopology
open Work.InnermostDisk
open Set

namespace Work.Topology.SphereSlicing

noncomputable section

/-! ## The homeomorphism `↥S ≃ₜ ↥(φ '' S)` -/

/-- The homeomorphism `↥S ≃ₜ ↥(φ '' S)` induced by a homeomorphism `φ` of `ℝ³`. -/
def homeoSImage (φ : R3 ≃ₜ R3) (S : Set R3) : S ≃ₜ (φ '' S) where
  toFun x := ⟨φ x, Set.mem_image_of_mem φ x.2⟩
  invFun y := ⟨φ.symm y, by
    show φ.symm (y : R3) ∈ S
    obtain ⟨s, hs, hsy⟩ := y.2
    rw [← hsy, φ.symm_apply_apply]
    exact hs⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply (x : R3))
  right_inv y := Subtype.ext (φ.apply_symm_apply (y : R3))
  continuous_toFun :=
    (φ.continuous.comp continuous_subtype_val).subtype_mk fun x => Set.mem_image_of_mem φ x.2
  continuous_invFun := (φ.symm.continuous.comp continuous_subtype_val).subtype_mk fun y => by
    show φ.symm (y : R3) ∈ S
    obtain ⟨s, hs, hsy⟩ := y.2
    rw [← hsy, φ.symm_apply_apply]
    exact hs

theorem homeoSImage_apply (φ : R3 ≃ₜ R3) (S : Set R3) (x : S) :
    (homeoSImage φ S x : R3) = φ x := rfl

/-- The image under `homeoSImage` of the "interior of the disc `e`" cut out inside `S`. -/
theorem homeoSImage_image_eq (φ : R3 ≃ₜ R3) (S : Set R3) (e : C(Disc, R3)) :
    homeoSImage φ S '' {x : S | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e z = (x : R3)}
      = {y : φ '' S | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ ((homeomorphCMap φ).comp e) z = (y : R3)} := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, hzx⟩, hxy⟩
    refine ⟨z, hz, ?_⟩
    change φ (e z) = (y : R3)
    rw [hzx, ← homeoSImage_apply φ S x]
    exact congrArg Subtype.val hxy
  · rintro ⟨z, hz, hzy⟩
    have hzy' : φ (e z) = (y : R3) := hzy
    obtain ⟨s, hs, hsy⟩ := y.2
    have heq : e z = s := φ.injective (by rw [hzy', hsy])
    refine ⟨⟨e z, ?_⟩, ⟨z, hz, rfl⟩, ?_⟩
    · rw [heq]; exact hs
    · exact Subtype.ext (by
        show φ (e z) = (y : R3)
        rw [heq]; exact hsy)

/-- The preimage under `homeoSImage` of the "interior of the disc `e`" cut out inside `φ '' S`. -/
theorem homeoSImage_preimage_eq (φ : R3 ≃ₜ R3) (S : Set R3) (e : C(Disc, R3)) :
    homeoSImage φ S ⁻¹' {y : φ '' S | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e z = (y : R3)}
      = {x : S | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ ((homeomorphCMap φ.symm).comp e) z = (x : R3)} := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_preimage] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    refine ⟨z, hz, ?_⟩
    change φ.symm (e z) = (x : R3)
    rw [hzx, homeoSImage_apply, φ.symm_apply_apply]
  · intro hx
    rw [Set.mem_preimage]
    obtain ⟨z, hz, hzx⟩ := hx
    refine ⟨z, hz, ?_⟩
    have hzx' : φ.symm (e z) = (x : R3) := hzx
    rw [homeoSImage_apply, ← hzx', φ.apply_symm_apply]

/-! ## Transport of the slicing datum -/

namespace SliceData

/-- Push a slicing datum forward along a homeomorphism `φ` of `ℝ³`: the slicing of `S` by the
standard torus becomes a slicing of `φ '' S` by the image torus.  Curves and discs are moved by
`φ`, and the nesting rank is unchanged. -/
def mapForward (φ : R3 ≃ₜ R3) {S : Set R3} (D : SliceData standard S) :
    SliceData (ParamTorus.mapHomeomorph φ) (φ '' S) where
  ι := D.ι
  fintype := D.fintype
  c i := ClosedCurve.mapHomeomorph φ (D.c i)
  simple i := ClosedCurve.mapHomeomorph_isSimple φ (D.c i) (D.simple i)
  disjoint i j hij := by
    show Disjoint (Set.range (ClosedCurve.mapHomeomorph φ (D.c i)).γ)
      (Set.range (ClosedCurve.mapHomeomorph φ (D.c j)).γ)
    rw [ClosedCurve.range_mapHomeomorph φ (D.c i), ClosedCurve.range_mapHomeomorph φ (D.c j)]
    exact Disjoint.image (D.disjoint hij) (φ.injective.injOn (s := Set.univ))
      (Set.subset_univ _) (Set.subset_univ _)
  mem i t := Set.mem_image_of_mem φ (D.mem i t)
  covers_pt x hxS hxP := by
    obtain ⟨s, hsS, hsx⟩ := hxS
    have hstd : s ∈ standard.carrier := by
      have h : φ s ∈ (ParamTorus.mapHomeomorph φ).carrier := by rw [hsx]; exact hxP
      rwa [mem_carrier_mapHomeomorph_iff] at h
    obtain ⟨i, hi⟩ := D.covers_pt s hsS hstd
    obtain ⟨t, ht⟩ := hi
    exact ⟨i, t, by rw [ClosedCurve.mapHomeomorph_apply, ht]; exact hsx⟩
  disc i := (homeomorphCMap φ).comp (D.disc i)
  disc_inj i z₁ z₂ h := D.disc_inj i (φ.injective h)
  disc_boundary i θ := by
    rw [ContinuousMap.comp_apply, homeomorphCMap_apply, D.disc_boundary i θ,
      ClosedCurve.mapHomeomorph_apply]
  disc_mem i z := Set.mem_image_of_mem φ (D.disc_mem i z)
  open_interior i := by
    rw [← homeoSImage_image_eq φ S (D.disc i)]
    exact (homeoSImage φ S).isOpen_image.mpr (D.open_interior i)
  rank := D.rank
  inside i j h := D.inside i j (by
    obtain ⟨z, hz, hzr⟩ := h
    rw [ClosedCurve.range_mapHomeomorph φ (D.c j)] at hzr
    obtain ⟨y, hy, hyz⟩ := hzr
    exact ⟨z, hz, by rw [← φ.injective hyz]; exact hy⟩)

/-- The range of a curve pulled back along a homeomorphism of `ℝ³`. -/
theorem range_mapHomeomorphInv (φ : R3 ≃ₜ R3) (γ : ClosedCurve (ParamTorus.mapHomeomorph φ)) :
    Set.range (ClosedCurve.mapHomeomorphInv φ γ).γ = φ.symm '' Set.range γ.γ := by
  ext X
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨γ.γ t, ⟨t, rfl⟩, ht⟩
  · rintro ⟨Y, ⟨t, rfl⟩, hY⟩
    exact ⟨t, hY⟩

/-- Pull a slicing datum back along a homeomorphism `φ` of `ℝ³`: the slicing of `φ '' S` by the
image torus becomes a slicing of `S` by the standard torus.  Curves and discs are moved by
`φ.symm`, and the nesting rank is unchanged. -/
def mapBack (φ : R3 ≃ₜ R3) {S : Set R3}
    (D : SliceData (ParamTorus.mapHomeomorph φ) (φ '' S)) : SliceData standard S where
  ι := D.ι
  fintype := D.fintype
  c i := ClosedCurve.mapHomeomorphInv φ (D.c i)
  simple i := (ClosedCurve.isSimple_mapHomeomorphInv_iff φ (D.c i)).mpr (D.simple i)
  disjoint i j hij := by
    show Disjoint (Set.range (ClosedCurve.mapHomeomorphInv φ (D.c i)).γ)
      (Set.range (ClosedCurve.mapHomeomorphInv φ (D.c j)).γ)
    rw [range_mapHomeomorphInv φ (D.c i), range_mapHomeomorphInv φ (D.c j)]
    exact Disjoint.image (D.disjoint hij) (φ.symm.injective.injOn (s := Set.univ))
      (Set.subset_univ _) (Set.subset_univ _)
  mem i t := by
    have h : (D.c i).γ t ∈ φ '' S := D.mem i t
    obtain ⟨s, hs, hsy⟩ := h
    rw [ClosedCurve.mapHomeomorphInv_apply, ← hsy, φ.symm_apply_apply]
    exact hs
  covers_pt x hxS hxstd := by
    have hxS' : φ x ∈ φ '' S := Set.mem_image_of_mem φ hxS
    have hxP : φ x ∈ (ParamTorus.mapHomeomorph φ).carrier := by
      rwa [mem_carrier_mapHomeomorph_iff]
    obtain ⟨i, hi⟩ := D.covers_pt (φ x) hxS' hxP
    obtain ⟨t, ht⟩ := hi
    exact ⟨i, t, by rw [ClosedCurve.mapHomeomorphInv_apply, ht, φ.symm_apply_apply]⟩
  disc i := (homeomorphCMap φ.symm).comp (D.disc i)
  disc_inj i z₁ z₂ h := D.disc_inj i (φ.symm.injective h)
  disc_boundary i θ := by
    rw [ContinuousMap.comp_apply, homeomorphCMap_apply, D.disc_boundary i θ,
      ClosedCurve.mapHomeomorphInv_apply]
  disc_mem i z := by
    have h : D.disc i z ∈ φ '' S := D.disc_mem i z
    obtain ⟨s, hs, hsy⟩ := h
    rw [ContinuousMap.comp_apply, homeomorphCMap_apply, ← hsy, φ.symm_apply_apply]
    exact hs
  open_interior i := by
    rw [← homeoSImage_preimage_eq φ S (D.disc i)]
    exact (D.open_interior i).preimage (homeoSImage φ S).continuous
  rank := D.rank
  inside i j h := D.inside i j (by
    obtain ⟨z, hz, hzr⟩ := h
    rw [range_mapHomeomorphInv φ (D.c j)] at hzr
    obtain ⟨y, hy, hyz⟩ := hzr
    exact ⟨z, hz, by rw [← φ.symm.injective hyz]; exact hy⟩)

end SliceData

/-! ## The equivalence -/

theorem sliceData_map_homeomorph_iff (φ : LeanEval.KnotTheory.PardonDistortion.R3 ≃ₜ
      LeanEval.KnotTheory.PardonDistortion.R3) (S : Set LeanEval.KnotTheory.PardonDistortion.R3) :
    Nonempty (Work.Topology.SphereSlicing.SliceData (Work.CoreTopology.ParamTorus.mapHomeomorph φ) (φ '' S)) ↔
      Nonempty (Work.Topology.SphereSlicing.SliceData Work.CoreTopology.standard S) :=
  ⟨fun ⟨D⟩ => ⟨D.mapBack φ⟩, fun ⟨D⟩ => ⟨D.mapForward φ⟩⟩

end

end Work.Topology.SphereSlicing
