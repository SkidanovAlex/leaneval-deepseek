import Mathlib
import Submission.Work.Motivic.mem_trans_source
import Submission.Work.Motivic.trans_hom_aux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/-- `(V.ι ⁻¹ᵁ U).ι ∘ (isoOfLE h).inv` is `X.homOfLE h`, at the level of points. -/
lemma isoOfLE_inv_iota_apply {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (x : U.toScheme) :
    (V.ι ⁻¹ᵁ U).ι ((Scheme.Opens.isoOfLE h).inv x) = X.homOfLE h x := by
  rw [← Scheme.Hom.comp_apply, isoOfLE_inv_comp_iota]

/-- The underlying map of a composite partial isomorphism is the composite of the underlying
maps, at the level of points. -/
theorem trans_hom_apply {X Y Z : Scheme.{0}} (i : X.PartialIso Y) (j : Y.PartialIso Z)
    {x : X} (hx : x ∈ i.source) (hy : i.toPartialMap.hom ⟨x, hx⟩ ∈ j.source) :
    (i.trans j).toPartialMap.hom ⟨x, (mem_trans_source i j hx).mpr hy⟩
      = j.toPartialMap.hom ⟨i.toPartialMap.hom ⟨x, hx⟩, hy⟩ := by
  have hT : Dense (↑(i.target ⊓ j.source) : Set Y) :=
    Dense.inter_of_isOpen_right i.dense_target j.dense_source j.source.is_open'
  -- Give the point of the source of `i.trans j` its explicit type, so that the subsequent
  -- definitional unfoldings are type correct at low transparency.
  change (i.trans j).toPartialMap.hom
      (⟨x, (mem_trans_source i j hx).mpr hy⟩ :
        (i.symm.target.ι ''ᵁ (i.symm.iso.hom ''ᵁ (i.symm.source.ι ⁻¹ᵁ (i.target ⊓ j.source)))).toScheme)
    = j.toPartialMap.hom ⟨i.toPartialMap.hom ⟨x, hx⟩, hy⟩
  -- `i.trans j` unfolds to `i'.trans' j' e`; recording it with a *well-typed* `rfl` avoids the
  -- `isoOfEq` term coming from the definition of `trans`, which is not type correct at
  -- `implicit` transparency.
  have hsplit : (i.trans j).toPartialMap.hom
      = (i.restrictTarget (i.target ⊓ j.source) hT inf_le_left).iso.hom
        ≫ (Y.isoOfEq (rfl : (i.target ⊓ j.source) = (i.target ⊓ j.source))).hom
        ≫ (j.restrictSource (i.target ⊓ j.source) hT inf_le_right).toPartialMap.hom := rfl
  rw [hsplit]
  rw [Scheme.PartialIso.toPartialMap_hom]
  -- Make every open subscheme appearing in the goal explicit.
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
    simp only [Scheme.PartialIso.restrictSource_target]
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
    simp only [Scheme.PartialIso.restrictSource_iso, Iso.trans_hom]
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
    simp only [Scheme.PartialIso.restrictTarget_iso, Scheme.PartialIso.restrictSource_iso,
      Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
  set_option backward.isDefEq.respectTransparency false in
    simp only [Scheme.Hom.comp_apply]
  -- The middle isomorphism `Y.isoOfEq (rfl : T = T)` is the identity.
  rw [Scheme.isoOfEq_rfl, Iso.refl_hom]
  -- The goal is now fully explicit; this makes the point applications type correct.
  show (j.target.ι ''ᵁ (j.iso.hom ''ᵁ (j.source.ι ⁻¹ᵁ (i.target ⊓ j.source)))).ι
      ((Hom.isoImage j.target.ι (j.iso.hom ''ᵁ (j.source.ι ⁻¹ᵁ (i.target ⊓ j.source)))).hom
        ((Hom.isoImage j.iso.hom (j.source.ι ⁻¹ᵁ (i.target ⊓ j.source))).hom
          ((Opens.isoOfLE inf_le_right).inv
            ((Opens.isoOfLE inf_le_left).hom
              ((Hom.isoImage i.symm.iso.hom (i.symm.source.ι ⁻¹ᵁ (i.target ⊓ j.source))).inv
                ((Hom.isoImage i.symm.target.ι (i.symm.iso.hom ''ᵁ i.symm.source.ι ⁻¹ᵁ (i.target ⊓ j.source))).inv
                  ⟨x, (mem_trans_source i j hx).mpr hy⟩))))))
    = j.toPartialMap.hom ⟨i.toPartialMap.hom ⟨x, hx⟩, hy⟩
  -- Push the outer inclusions inwards.
  rw [isoImage_hom_apply, isoImage_hom_apply]
  rw [isoOfLE_inv_iota_apply]
  show j.target.ι
      (j.iso.hom (Y.homOfLE inf_le_right
        ((i.restrictTarget (i.target ⊓ j.source) hT inf_le_left).iso.hom
          ⟨x, (mem_trans_source i j hx).mpr hy⟩)))
    = j.toPartialMap.hom ⟨i.toPartialMap.hom ⟨x, hx⟩, hy⟩
  -- The image of the point lies in `j.source` and its value is `i.toPartialMap.hom ⟨x, hx⟩`.
  have hpt : Y.homOfLE inf_le_right
      ((i.restrictTarget (i.target ⊓ j.source) hT inf_le_left).iso.hom
        ⟨x, (mem_trans_source i j hx).mpr hy⟩)
      = ⟨i.toPartialMap.hom ⟨x, hx⟩, hy⟩ := by
    apply Subtype.ext
    change (Y.homOfLE inf_le_right
      ((i.restrictTarget (i.target ⊓ j.source) hT inf_le_left).iso.hom
        ⟨x, (mem_trans_source i j hx).mpr hy⟩)).val
      = (⟨i.toPartialMap.hom ⟨x, hx⟩, hy⟩ : ↥(j.source : Set Y)).val
    set_option backward.isDefEq.respectTransparency false in
      simp only [Scheme.homOfLE_apply]
    set_option backward.isDefEq.respectTransparency false in
      simp only [iso_hom_val]
    exact restrictTarget_apply' i (i.target ⊓ j.source) hT inf_le_left hx
      ((mem_trans_source i j hx).mpr hy)
  change j.target.ι
      (j.iso.hom (Y.homOfLE inf_le_right
        ((i.restrictTarget (i.target ⊓ j.source) hT inf_le_left).iso.hom
          ⟨x, (mem_trans_source i j hx).mpr hy⟩)))
    = j.target.ι (j.iso.hom ⟨i.toPartialMap.hom ⟨x, hx⟩, hy⟩)
  exact congrArg (fun q => j.target.ι (j.iso.hom q)) hpt

end Work.Motivic
