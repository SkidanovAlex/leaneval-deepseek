import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

/-!
# Transversality of a sphere with the torus transports along an ambient homeomorphism

`Work.Topology.SphereSlicing.TransverseSphere P S` says that `S ∩ F` is a finite disjoint union
of simple closed curves of `F = P.carrier`, all of them lying in `S`.  It is a purely topological
condition, so it is carried by a homeomorphism of `ℝ³`: a sphere `S` is transverse to the standard
torus `F` exactly when its image `φ '' S` is transverse to the image torus
`ParamTorus.mapHomeomorph φ`.  Curves are moved by `ClosedCurve.mapHomeomorph φ` and pulled back
by `ClosedCurve.mapHomeomorphInv φ`, and the two constructions are inverse
(`ClosedCurve.mapHomeomorph_mapHomeomorphInv`, `ClosedCurve.mapHomeomorphInv_mapHomeomorph`).

This is the curve-level input of the slicing transport
`Work.Topology.SphereSlicing.sliceData_map_homeomorph_iff`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.Topology.SphereSlicing

noncomputable section

/-- The range of the pull-back of a curve along `φ` is the image under `φ.symm` of its range. -/
theorem range_mapHomeomorphInv_eq (φ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph φ)) :
    Set.range (ClosedCurve.mapHomeomorphInv φ γ).γ = φ.symm '' Set.range γ.γ := by
  ext X
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨γ.γ t, ⟨t, rfl⟩, ht⟩
  · rintro ⟨Y, ⟨t, rfl⟩, hY⟩
    exact ⟨t, hY⟩

theorem transverseSphere_map_homeomorph_iff (φ : LeanEval.KnotTheory.PardonDistortion.R3 ≃ₜ
      LeanEval.KnotTheory.PardonDistortion.R3) (S : Set LeanEval.KnotTheory.PardonDistortion.R3) :
    Work.Topology.SphereSlicing.TransverseSphere (Work.CoreTopology.ParamTorus.mapHomeomorph φ) (φ '' S) ↔
      Work.Topology.SphereSlicing.TransverseSphere Work.CoreTopology.standard S := by
  constructor
  · rintro ⟨ι, hfin, c, hsimple, hdisjoint, hmem, hcovers⟩
    refine ⟨ι, hfin, fun i => ClosedCurve.mapHomeomorphInv φ (c i), ?_, ?_, ?_, ?_⟩
    · intro i
      exact (ClosedCurve.isSimple_mapHomeomorphInv_iff φ (c i)).mpr (hsimple i)
    · intro i j hij
      show Disjoint (Set.range (ClosedCurve.mapHomeomorphInv φ (c i)).γ)
        (Set.range (ClosedCurve.mapHomeomorphInv φ (c j)).γ)
      rw [range_mapHomeomorphInv_eq φ (c i), range_mapHomeomorphInv_eq φ (c j)]
      exact Set.disjoint_image_of_injective φ.symm.injective (hdisjoint hij)
    · intro i t
      have ht : c i t ∈ φ '' S := hmem i t
      obtain ⟨s, hsS, hsc⟩ := ht
      rw [ClosedCurve.mapHomeomorphInv_apply, ← hsc, φ.symm_apply_apply]
      exact hsS
    · intro x hxS hxP
      have hxS' : φ x ∈ φ '' S := Set.mem_image_of_mem φ hxS
      have hxP' : φ x ∈ (ParamTorus.mapHomeomorph φ).carrier := by
        rwa [mem_carrier_mapHomeomorph_iff]
      obtain ⟨i, t, ht⟩ := hcovers (φ x) hxS' hxP'
      exact ⟨i, t, by rw [ClosedCurve.mapHomeomorphInv_apply, ht, φ.symm_apply_apply]⟩
  · rintro ⟨ι, hfin, c, hsimple, hdisjoint, hmem, hcovers⟩
    refine ⟨ι, hfin, fun i => ClosedCurve.mapHomeomorph φ (c i), ?_, ?_, ?_, ?_⟩
    · intro i
      exact ClosedCurve.mapHomeomorph_isSimple φ (c i) (hsimple i)
    · intro i j hij
      show Disjoint (Set.range (ClosedCurve.mapHomeomorph φ (c i)).γ)
        (Set.range (ClosedCurve.mapHomeomorph φ (c j)).γ)
      rw [ClosedCurve.range_mapHomeomorph φ (c i), ClosedCurve.range_mapHomeomorph φ (c j)]
      exact Set.disjoint_image_of_injective φ.injective (hdisjoint hij)
    · intro i t
      exact Set.mem_image_of_mem φ (hmem i t)
    · intro x hxS hxP
      obtain ⟨s, hsS, hsc⟩ := hxS
      have hsP : s ∈ standard.carrier := by
        rw [← mem_carrier_mapHomeomorph_iff φ s, hsc]
        exact hxP
      obtain ⟨i, t, ht⟩ := hcovers s hsS hsP
      exact ⟨i, t, by rw [ClosedCurve.mapHomeomorph_apply, ht, hsc]⟩

end

end Work.Topology.SphereSlicing
