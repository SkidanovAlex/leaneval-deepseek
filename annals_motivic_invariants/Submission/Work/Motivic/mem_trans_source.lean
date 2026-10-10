import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- The source of a composite of partial isomorphisms is the preimage under the first one of
the source of the second. -/
theorem trans_source_eq {X Y Z : Scheme.{0}} (i : X.PartialIso Y) (j : Y.PartialIso Z) :
    (i.trans j).source = i.source.ι ''ᵁ (i.toPartialMap.hom ⁻¹ᵁ j.source) := by
  rw [Scheme.PartialIso.trans_source]
  simp only [Scheme.PartialIso.restrictSource, Scheme.PartialIso.symm, Iso.symm_hom,
    Scheme.Hom.inv_image]
  congr 1
  rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq,
    Scheme.PartialIso.toPartialMap_hom, Scheme.Hom.comp_preimage]

/-- A point `x` of the source of `i` lies in the source of the composite partial isomorphism
`i.trans j` exactly when its image under `i` lies in the source of `j`. -/
theorem mem_trans_source {X Y Z : Scheme.{0}} (i : X.PartialIso Y) (j : Y.PartialIso Z)
    {x : X} (hx : x ∈ i.source) :
    (x ∈ (i.trans j).source ↔ i.toPartialMap.hom ⟨x, hx⟩ ∈ j.source) := by
  rw [trans_source_eq]
  rw [show ∀ (V : Opens i.source.toScheme),
      (x ∈ i.source.ι ''ᵁ V ↔ (⟨x, hx⟩ : i.source.toScheme) ∈ V) from
    fun V => Scheme.Opens.mem_ι_image_iff (U := i.source) (V := V)
      (x := (⟨x, hx⟩ : i.source.toScheme))]
  exact Scheme.Hom.mem_preimage i.toPartialMap.hom

end Work.Motivic
