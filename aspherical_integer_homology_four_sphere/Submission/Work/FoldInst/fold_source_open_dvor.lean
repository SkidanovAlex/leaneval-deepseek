import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.actX_image_Dvor
import Submission.Work.FoldInst.Ksub_eq_wallSum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

/-! ### Saturation of the union of the Voronoi pieces

This file is the Voronoi analogue (`Dvor` in place of `Dlift`) of `fold_source_open`: the source
of the fold chart of the class `i`, namely the union of the images in `M̄` of the Voronoi pieces
`Dvor i r`, is open, and the union of the pieces is exactly its preimage under the quotient map.

The mathematical content is the same saturation statement: the identification relation `~₁` maps
the chamber `Dvor i r` onto the chamber of the reflected representative (`actX_image_Dvor`), so
that `mk ⁻¹' (mk '' C) = C` for `C = ⋃ r, Dvor i r`. -/

/-- The identification group of a point of a Voronoi piece is contained in the wall group.  Every
side that is tight at such a point is a wall of the representative (`Dvor_tight`), and the type of
a wall is the corresponding generator of `foldH i`. -/
theorem Ksub_le_foldH_dvor (i : Fin 98) {x : Xbar}
    (hx : x ∈ ⋃ r : Fin (foldCodim i) → Bool, Dvor i r) : Ksub x.2.1 ≤ foldH i := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
  rw [Ksub_eq_closure]
  apply AddSubgroup.closure_mono
  rintro γ ⟨S, hS, rfl⟩
  rw [tightSides_spec] at hS
  obtain ⟨t, ht⟩ := Dvor_tight i r hr hS
  refine ⟨t, ?_⟩
  rw [foldGen, ← ht, foldWalls]
  exact (sideType_sidePerm (toG (foldKr i r)) (foldWallAt i t)).symm

/-- **The union of the Voronoi pieces is invariant under the wall group.**  An element of `foldH i`
is a subset sum of the wall generators (`mem_closure_image_iff`), and `actX (wallSum i Δ)` carries
`Dvor i r` onto `Dvor i (flipSet r Δ)` (`actX_image_Dvor`). -/
theorem actX_foldH_image_subset_dvor (i : Fin 98) (γ : Gg) (hγ : γ ∈ foldH i)
    (r : Fin (foldCodim i) → Bool) :
    actX γ '' Dvor i r ⊆ ⋃ r' : Fin (foldCodim i) → Bool, Dvor i r' := by
  classical
  have hγ' : γ ∈ AddSubgroup.closure (foldGen i '' (Set.univ : Set (Fin (foldCodim i)))) := by
    simpa [foldH, Set.image_univ] using hγ
  have h2 : γ ∈ AddSubgroup.closure
      (foldGen i '' ((Finset.univ : Finset (Fin (foldCodim i))) : Set (Fin (foldCodim i)))) := by
    simpa using hγ'
  obtain ⟨Δ, -, rfl⟩ := (mem_closure_image_iff (foldGen i) Finset.univ γ).mp h2
  change actX (wallSum i Δ) '' Dvor i r ⊆ ⋃ r' : Fin (foldCodim i) → Bool, Dvor i r'
  rw [actX_image_Dvor i r Δ]
  exact Set.subset_iUnion _ (flipSet r Δ)

/-- The union of the Voronoi pieces is saturated for the identification relation `~₁`. -/
theorem mem_foldC_of_rel_dvor (i : Fin 98) {z x : Xbar}
    (hz : z ∈ ⋃ r : Fin (foldCodim i) → Bool, Dvor i r) (h : rel z x) :
    x ∈ ⋃ r : Fin (foldCodim i) → Bool, Dvor i r := by
  obtain ⟨γ, hγ, rfl⟩ := h
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hz
  exact actX_foldH_image_subset_dvor i γ (Ksub_le_foldH_dvor i hz hγ) r ⟨z, hr, rfl⟩

theorem fold_source_open_dvor (i : Fin 98) :
    IsOpen (⋃ r : Fin (foldCodim i) → Bool, mk '' Dvor i r) ∧
      (mk ⁻¹' (⋃ r : Fin (foldCodim i) → Bool, mk '' Dvor i r)
        = ⋃ r : Fin (foldCodim i) → Bool, Dvor i r) := by
  have hpre : mk ⁻¹' (⋃ r : Fin (foldCodim i) → Bool, mk '' Dvor i r)
      = (⋃ r : Fin (foldCodim i) → Bool, Dvor i r) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨r, z, hz, hzx⟩
      exact Set.mem_iUnion.mp
        (mem_foldC_of_rel_dvor i (Set.mem_iUnion.mpr ⟨r, hz⟩) (Quotient.eq.mp hzx))
    · rintro ⟨r, hr⟩
      exact ⟨r, x, hr, rfl⟩
  refine ⟨?_, hpre⟩
  refine isOpen_quotient_iff_preimage.mpr ?_
  rw [hpre]
  exact isOpen_iUnion (fun r => isOpen_Dvor i r)

end Work.FoldInst
