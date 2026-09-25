import Mathlib
import Submission.Work.RelatorRank.API
import Submission.Work.ProPDeficiency.Basic

/-!
# `GenRank = dGens`: the two generator-rank conventions agree

**Namespace** `Work.RelatorRank.Abstract`; module
`Submission.Work.RelatorRank.Abstract.genRank_eq_dGens`.

There are two formalisations of "the minimal number of generators" in this workspace:

* `Work.RelatorRank.GenRank G`, the `sInf` of the sizes of the *generating families*
  `gen : Fin d → G` (`Generating gen` means `Subgroup.closure (Set.range gen) = ⊤`);
* `Work.ProPDeficiency.dGens G`, the `sInf` of the cardinalities of the finite *generating sets*
  `S : Finset G` (`IsGeneratingSet S` means `Subgroup.closure (S : Set G) = ⊤`).

The two languages are interchangeable: a generating finset of cardinality `n` re-indexes as a
generating family on `Fin n` (via `Finset.equivFin`), and conversely the image of a finite
generating family is a generating finset of no larger cardinality.  Hence the two `sInf`s coincide
for every finitely generated group.

The two conversion lemmas are `hasGeneratingFamily_card_of_isGeneratingSet` and
`exists_isGeneratingSet_card_le_of_hasGeneratingFamily`; the equality is the target
`genRank_eq_dGens`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.RelatorRank.Abstract

open Work.ProPDeficiency

/-- **Re-indexing a generating finset as a generating family.**  A finset `S` whose closure is `⊤`
gives, via `Finset.equivFin S : ↥S ≃ Fin S.card`, a generating family `Fin S.card → G`. -/
theorem hasGeneratingFamily_card_of_isGeneratingSet {G : Type*} [Group G] {S : Finset G}
    (hS : IsGeneratingSet S) : HasGeneratingFamily G S.card := by
  refine ⟨fun i : Fin S.card => ((Finset.equivFin S).symm i : G), ?_⟩
  have hrange : Set.range (fun i : Fin S.card => ((Finset.equivFin S).symm i : G))
      = (S : Set G) := by
    rw [show (fun i : Fin S.card => ((Finset.equivFin S).symm i : G))
        = Subtype.val ∘ (Finset.equivFin S).symm from rfl]
    rw [Set.range_comp, (Finset.equivFin S).symm.surjective.range_eq, Subtype.coe_image_univ]
  rw [generating_iff, hrange]
  exact hS

/-- **The image of a finite generating family is a generating finset**, of no larger cardinality. -/
theorem exists_isGeneratingSet_card_le_of_hasGeneratingFamily {G : Type*} [Group G] {d : ℕ}
    (h : HasGeneratingFamily G d) : ∃ S : Finset G, IsGeneratingSet S ∧ S.card ≤ d := by
  classical
  obtain ⟨gen, hgen⟩ := h
  refine ⟨Finset.univ.image gen, ?_, ?_⟩
  · rw [isGeneratingSet_iff]
    have hcoe : ((Finset.univ.image gen : Finset G) : Set G) = Set.range gen := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [hcoe]
    exact hgen
  · calc (Finset.univ.image gen).card ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_image_le
      _ = d := by simp

/-- **`GenRank` and `dGens` agree.**  The minimal size of a generating family (`GenRank`) equals
the minimal cardinality of a finite generating set (`dGens`), for a finitely generated group.

The hypothesis `Group.FG G` is what makes both `sInf`s attained: it supplies an actual generating
finset, hence a generating family, in each direction. -/
theorem genRank_eq_dGens {G : Type*} [Group G] (hG : Group.FG G) :
    GenRank G = Work.ProPDeficiency.dGens G := by
  obtain ⟨n, S, _hn, hSgen⟩ := Group.fg_iff'.mp hG
  refine le_antisymm ?_ ?_
  · -- `GenRank G ≤ dGens G`, from a minimal generating finset of cardinality `dGens G`
    obtain ⟨T, hTmin, hTcard⟩ := exists_minimalGeneratingSet hG
    have h1 := hasGeneratingFamily_card_of_isGeneratingSet hTmin.1
    rw [hTcard] at h1
    exact genRank_le_of_hasGeneratingFamily h1
  · -- `dGens G ≤ GenRank G`, from a generating family of size `GenRank G`
    have hfam : HasGeneratingFamily G (GenRank G) :=
      hasGeneratingFamily_genRank ⟨S.card, hasGeneratingFamily_card_of_isGeneratingSet hSgen⟩
    obtain ⟨U, hUgen, hUcard⟩ := exists_isGeneratingSet_card_le_of_hasGeneratingFamily hfam
    exact le_trans (dGens_le_card hUgen) hUcard

end Work.RelatorRank.Abstract
