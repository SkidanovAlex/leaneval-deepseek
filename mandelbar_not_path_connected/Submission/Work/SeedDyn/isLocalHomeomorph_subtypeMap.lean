import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn

/-- **Auxiliary lemma.** If `f : X → Y` is a local homeomorphism on an open set `U ⊆ X`
(in the sense of `IsLocalHomeomorphOn`), then the restriction of `f` to the subtype `↥U`
is a local homeomorphism into `Y`.

This is proved here so that the file is self-contained: it is the domain-only half of
`isLocalHomeomorph_subtypeMap` below. -/
theorem isLocalHomeomorph_domRestrict_of_localHomeomorphOn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {U : Set X} {f : X → Y} (hU : IsOpen U)
    (hf : IsLocalHomeomorphOn f U) : IsLocalHomeomorph (Set.domRestrict U f) := by
  rcases isEmpty_or_nonempty U with hUe | hUne
  · -- `U` is empty, so there is nothing to check.
    intro x
    exact (hUe.false x).elim
  · refine IsLocalHomeomorph.mk (Set.domRestrict U f) fun p => ?_
    -- At `p : ↥U` we may use a local model `e : OpenPartialHomeomorph X Y` with `f = e`.
    obtain ⟨e, hpe, hfe⟩ := hf p.1 p.2
    -- Restricting this model to the open subtype `U` gives a local model on `↥U`.
    refine ⟨e.subtypeRestr (s := ⟨U, hU⟩) hUne, ?_, ?_⟩
    · simpa [OpenPartialHomeomorph.subtypeRestr_source] using hpe
    · intro q _
      have hcoe := OpenPartialHomeomorph.subtypeRestr_coe (e := e) (s := ⟨U, hU⟩) hUne
      rw [hcoe]
      simp only [Set.domRestrict]
      rw [hfe]

/-- If `f : X → Y` is a local homeomorphism on an open set `U ⊆ X`, if `V ⊆ Y` is open and
`f` maps `U` into `V`, then the induced map `↥U → ↥V` between the subtypes is a local
homeomorphism as well. -/
theorem isLocalHomeomorph_subtypeMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} {V : Set Y} {f : X → Y} (hU : IsOpen U) (hV : IsOpen V)
    (hm : ∀ z ∈ U, f z ∈ V) (hf : IsLocalHomeomorphOn f U) :
    IsLocalHomeomorph (Subtype.map f (fun z hz => hm z hz)) := by
  have h1 := isLocalHomeomorph_domRestrict_of_localHomeomorphOn hU hf
  -- The composite with the inclusion `↥V ↪ Y` is the domain restriction of `f` to `U`.
  have hcomp : IsLocalHomeomorph (Subtype.val ∘ Subtype.map f (fun z hz => hm z hz)) := by
    rw [show (Subtype.val ∘ Subtype.map f (fun z hz => hm z hz)) = Set.domRestrict U f from rfl]
    exact h1
  -- The inclusion of the open set `V` is a local homeomorphism, so we may cancel it.
  refine IsLocalHomeomorph.of_comp (g := (Subtype.val : V → Y)) hcomp ?_ ?_
  · exact hV.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  · exact (Topology.IsInducing.subtypeVal (t := V)).continuous_iff.mpr (by
      rw [show (Subtype.val ∘ Subtype.map f (fun z hz => hm z hz)) = Set.domRestrict U f from rfl]
      exact continuousOn_iff_continuous_domRestrict.mp hf.continuousOn)

end Work.SeedDyn
