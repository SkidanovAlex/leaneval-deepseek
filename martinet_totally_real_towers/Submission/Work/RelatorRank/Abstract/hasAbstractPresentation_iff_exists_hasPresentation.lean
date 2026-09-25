import Mathlib
import Submission.Work.RelatorRank.API
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.hasPresentation_of_isPresentation

namespace Work.RelatorRank.Abstract

/-- **The abstract `∃`-form and the `Work.ProPDeficiency` `∃`-form agree.**

`HasAbstractPresentation G d r` says that `G` has a presentation on the generators `Fin d` whose
relator set has at most `r` elements, while `Work.ProPDeficiency.HasPresentation G d r'` says that
`G` is isomorphic to the quotient of the free group on *some* finite `α` with
`Fintype.card α = d` by the normal closure of a relator set of exactly `r'` elements.  The two
differ only in that the second records the relator count exactly and allows an arbitrary finite
index set, while the first bounds it and fixes the index set to `Fin d`; hence
`HasAbstractPresentation G d r` holds exactly when `HasPresentation G d r'` holds for some `r' ≤ r`. -/
theorem hasAbstractPresentation_iff_exists_hasPresentation {G : Type*} [Group G] {d r : ℕ} :
    HasAbstractPresentation G d r ↔
      ∃ r' : ℕ, r' ≤ r ∧ Work.ProPDeficiency.HasPresentation G d r' := by
  constructor
  · -- `→`: the datum itself is a presentation with exactly `rel.card` relators.
    rintro ⟨P⟩
    refine ⟨P.rel.card, P.card_le, Fin d, inferInstance, P.rel, Fintype.card_fin d, rfl, ?_⟩
    -- the presentation map `FreeGroup (Fin d) →* G` is onto and has kernel `normalClosure P.rel`
    have hsurj : Function.Surjective ⇑(FreeGroup.lift P.gen) :=
      MonoidHom.range_eq_top.mp (by
        rw [FreeGroup.range_lift_eq_closure]
        exact P.generating)
    exact ⟨(QuotientGroup.quotientKerEquivOfSurjective (FreeGroup.lift P.gen) hsurj).symm.trans
      (QuotientGroup.quotientMulEquivOfEq P.ker_eq)⟩
  · -- `←`: reindex the given presentation along a bijection with `Fin d` and name the generators
    -- by the classes of the standard free generators in the quotient.
    rintro ⟨r', hr', α, hαfin, rel, hcardα, hcardrel, hpres⟩
    obtain ⟨φ⟩ := hpres
    set e : α ≃ Fin d := @Fintype.equivFinOfCardEq α hαfin d hcardα with he
    set ψ : FreeGroup α ≃* FreeGroup (Fin d) := FreeGroup.freeGroupCongr e with hψ
    set rel' : Finset (FreeGroup (Fin d)) := rel.image ψ with hrel'
    set N' : Subgroup (FreeGroup (Fin d)) :=
      Subgroup.normalClosure (rel' : Set (FreeGroup (Fin d))) with hN'
    -- reindexing the relator set reindexes its normal closure
    have hmap : Subgroup.map (ψ : FreeGroup α →* FreeGroup (Fin d))
        (Subgroup.normalClosure (rel : Set (FreeGroup α))) = N' := by
      rw [hN', hrel', Subgroup.map_normalClosure (rel : Set (FreeGroup α))
        (ψ : FreeGroup α →* FreeGroup (Fin d)) ψ.surjective]
      congr 1
      exact Finset.coe_image.symm
    set iso : G ≃* (FreeGroup (Fin d) ⧸ N') :=
      φ.trans (QuotientGroup.congr _ _ ψ hmap) with hiso
    set gen : Fin d → G :=
      fun i => iso.symm ((QuotientGroup.mk' N') (FreeGroup.of i)) with hgen
    -- the presentation map is `iso.symm` composed with the quotient map
    have hcomp : FreeGroup.lift gen = iso.symm.toMonoidHom.comp (QuotientGroup.mk' N') := by
      refine FreeGroup.ext_hom _ _ (fun i => ?_)
      have h1 : gen i = iso.symm ((QuotientGroup.mk' N') (FreeGroup.of i)) := by rw [hgen]
      rw [FreeGroup.lift_apply_of, h1, MonoidHom.comp_apply]
      rfl
    refine ⟨gen, rel', ?_, ?_, ?_⟩
    · -- the named generators generate: the presentation map is onto
      have hsurj : Function.Surjective ⇑(FreeGroup.lift gen) := by
        rw [hcomp]
        exact iso.symm.surjective.comp (QuotientGroup.mk'_surjective N')
      show Subgroup.closure (Set.range gen) = ⊤
      rw [← FreeGroup.range_lift_eq_closure]
      exact MonoidHom.range_eq_top.mpr hsurj
    · -- the relator count is unchanged by reindexing, and `rel.card = r' ≤ r`
      calc rel'.card = rel.card := Finset.card_image_of_injective _ ψ.injective
        _ = r' := hcardrel
        _ ≤ r := hr'
    · -- the kernel of the presentation map is exactly the (reindexed) normal closure
      rw [hcomp, MonoidHom.ker_comp_of_injective _ _ iso.symm.injective]
      exact QuotientGroup.ker_mk' N'

end Work.RelatorRank.Abstract
