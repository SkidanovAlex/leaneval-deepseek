import Mathlib
import Submission.Work.RelatorRank.All
import Submission.Work.ShafarevichKoch.RelationBound
import Submission.Work.ShafarevichKoch.Crux
import Submission.Work.ShafarevichKoch.Kc
import Submission.Work.ShafarevichKoch.exists_generatingSet_card_five_Kc

/-!
# `Work.ShafarevichKoch.KcCohomology` -- the crux in the project's cohomological normalisation

The chapter's crux (`Crux.lean`) is the statement that `G_∅ = Gal(Kc_∅/Kc)` admits a presentation
on `5 = rank₂ Cl(Kc)` generators with at most `6 = 5 + d₂(O_{Kc}^×)` relators.  The literature
states it in **continuous cohomology**:

`dim_{𝔽₂} H²_cont(G_∅, 𝔽₂) ≤ 6 = dim_{𝔽₂} V_∅/Kc^{×2}`

(Koch, *Galois theory of `p`-extensions*, Ch. 11 Thm. 11.3: `Sha_∅ ↪ C_∅ = (V_∅/K^{×p})^∨`; with
the count `#(V_∅/Kc^{×2}) = 2^6` of §9.4 of the README this is exactly the bound; equivalently
Wingberg's duality, NSW Ch. VIII §8 Thm. 8.8.1, in the deficiency form
`df(G_∅) = d₂(O_{Kc}^×/N_{Kc_∅/Kc} O_{Kc_∅}^×) ≤ d₂(O_{Kc}^×) = 1`).

This module makes that identification in the workspace, so that the chapter's crux becomes the
conjunction of the **two named classical inputs the rest of the project already uses**:

* the arithmetic bound, stated with the genuine continuous cohomology group
  `Work.RelatorRank.contH2 (galoisGroup M) = H²(G_∅, 𝔽₂)` built in the parallel chapter
  `Submission.Work.ConCohomology` -- this is the content of the deliverable's item (2), i.e. the
  classical Shafarevich--Koch/Wingberg relation bound;
* the group-theoretic value theorem `Work.RelatorRank.GaschutzCohomologicalValue Γ`
  (`r(Γ) = dim_{𝔽₂} H²(Γ,𝔽₂)` for finitely generated pro-`2` groups, Gaschütz 1953 / Koch Ch. 11),
  which is *shared* with the benchmark's own group-theory wall
  (`Submission.gaschutzCohomologicalValue` of `Submission.lean`).

Nothing new is assumed beyond those two; the rest of this file is the transport between the
chapter's presentation interface (`HasProTwoPresentation`, `KcProTwoPresentationInput`) and the
sibling chapters' vocabulary (`Work.RelatorRank.HasProP2Presentation`, `RelatorRankLe`,
`GeneratorRank`, `ContH2DimLe`), together with the generator-rank identification
`GeneratorRank (G_∅) = 5` (item (1) of the deliverable, restated in the sibling's vocabulary).

## Main declarations

* `Work.ShafarevichKoch.generatorRank_galoisGroup_Kc` : `GeneratorRank (G_∅) = 5`;
* `Work.ShafarevichKoch.hasProTwoPresentation_of_hasProP2Presentation` : the sibling's presentation
  datum is the chapter's;
* `Work.ShafarevichKoch.relatorRankLe_six_galoisGroup_iff` :
  `RelatorRankLe (G_∅) 6 ↔ HasProTwoPresentation Kc 5 6`;
* `Work.ShafarevichKoch.KcKochCohomologyBound` : the classical cohomological form
  `∃ M, dim_{𝔽₂} H²_cont(G_∅,𝔽₂) ≤ 6`, i.e. `ContH2DimLe (G_∅) 6`;
* `Work.ShafarevichKoch.kcProTwoPresentationInput_of_contH2DimLe` and its `∀ M` form: the crux from
  the cohomological bound + Gaschütz;
* `Work.ShafarevichKoch.infiniteProTwoExtension_Kc_of_contH2DimLe`,
  `Work.ShafarevichKoch.unramifiedPro2TowerWall_of_contH2DimLe`,
  `Work.ShafarevichKoch.boundedRdTowerWall_of_contH2DimLe`,
  `Work.ShafarevichKoch.exists_unramifiedLevel_rootDiscr_of_contH2DimLe`: the walls, from the two
  classical inputs.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-! ## The generator rank, in the sibling chapter's vocabulary -/

/-- **A `Finset` generating set gives a `Finset.card`-indexed dense generating family.**

`Work.RelatorRank.HasDenseGeneratingFamily Γ d` is `∃ gen : Fin d → Γ, DenseGenerating gen`, i.e.
`(Subgroup.closure (Set.range gen)).topologicalClosure = ⊤`.  Enumerating a `Finset` `S` with
`S.equivFin` turns a generating set `S` into such a family. -/
theorem hasDenseGeneratingFamily_of_finset {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {S : Finset Γ}
    (h : (Subgroup.closure (S : Set Γ)).topologicalClosure = ⊤) :
    Work.RelatorRank.HasDenseGeneratingFamily Γ S.card := by
  refine ⟨fun i => (S.equivFin.symm i : Γ), ?_⟩
  show (Subgroup.closure (Set.range fun i : Fin S.card => (S.equivFin.symm i : Γ))).topologicalClosure
    = ⊤
  have hrange : Set.range (fun i : Fin S.card => (S.equivFin.symm i : Γ)) = (S : Set Γ) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).2
    · intro hx
      refine ⟨S.equivFin ⟨x, hx⟩, ?_⟩
      simp
  rw [hrange]
  exact h

/-- **The generator rank of `G_∅ = Gal(Kc_∅/Kc)` is `5`.**

This is item (1) of the deliverable (`d(G_∅) = rank₂ Cl(Kc) = 5`,
`exists_generatingSet_card_five_Kc`) restated with the sibling chapter's definition
`Work.RelatorRank.GeneratorRank Γ = sInf {d | HasDenseGeneratingFamily Γ d}`. -/
theorem generatorRank_galoisGroup_Kc (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2) :
    Work.RelatorRank.GeneratorRank (galoisGroup M) = 5 := by
  obtain ⟨hgen, hmin⟩ := exists_generatingSet_card_five_Kc M
  obtain ⟨S, hcard, htop⟩ := hgen
  have hmem : Work.RelatorRank.HasDenseGeneratingFamily (galoisGroup M) 5 :=
    hcard ▸ hasDenseGeneratingFamily_of_finset htop
  have hlow : ∀ d ∈ {d : ℕ | Work.RelatorRank.HasDenseGeneratingFamily (galoisGroup M) d}, 5 ≤ d := by
    rintro d ⟨g, hg⟩
    have hclosure : (Subgroup.closure (Set.range g)).topologicalClosure = ⊤ := hg
    set S : Finset (galoisGroup M) := Finset.univ.image g with hSdef
    have hScard : S.card ≤ d := by
      rw [hSdef]
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin d))) (f := g)
    have hSrange : (Subgroup.closure (S : Set (galoisGroup M))).topologicalClosure = ⊤ := by
      have hcoe : (S : Set (galoisGroup M)) = Set.range g := by
        rw [hSdef, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      rw [hcoe, hclosure]
    exact le_trans (hmin S hSrange) hScard
  refine le_antisymm (Nat.sInf_le hmem) ?_
  have hne : ({d : ℕ | Work.RelatorRank.HasDenseGeneratingFamily (galoisGroup M) d} : Set ℕ).Nonempty :=
    ⟨5, hmem⟩
  exact hlow _ (Nat.sInf_mem hne)

/-! ## Transport between the two presentation interfaces -/

/-- **A relator family for `Γ` gives a presentation datum in the sibling chapter's sense.**

The direction `Fin r → FreeGroup (Fin d)` (this chapter) to `Finset (FreeGroup (Fin d))`
(`Work.RelatorRank`) is `Set.range` versus `Finset.univ.image`: the normal closure of the range of
a family and of the finite set of its values agree. -/
theorem hasProP2Presentation_of_relators
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2) {d r : ℕ}
    (g : Fin d → galoisGroup M) (w : Fin r → FreeGroup (Fin d))
    (hker : MonoidHom.ker (FreeGroup.lift g) = Subgroup.normalClosure (Set.range w))
    (hdense : (Subgroup.closure (Set.range g)).topologicalClosure = ⊤) :
    Work.RelatorRank.HasProP2Presentation (galoisGroup M) d r :=
  ⟨{ gen := g
     rel := Finset.univ.image w
     dense := hdense
     card_le := by
       simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin r))) (f := w)
     ker_eq := by
       rw [hker]
       congr 1
       exact Set.ext fun x => by simp }⟩

/-- **The sibling chapter's presentation datum is this chapter's `HasProTwoPresentation`.**

`Work.RelatorRank.HasProP2Presentation Γ d r` is a dense generating `d`-family `gen` together with
a *finite set* of relators `rel` presenting `Γ` on `gen`; the chapter's `HasProTwoPresentation F d r`
is the same datum with the relators enumerated as a `Fin r`-family `w`, for some maximal unramified
pro-`2` extension `M` of `F`.  The enumeration is obtained by listing `rel` along
`Finset.equivFin` (and padding by `hasProTwoPresentation_mono`, since `rel.card ≤ r`). -/
theorem hasProTwoPresentation_of_hasProP2Presentation
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2) {d r : ℕ}
    (h : Work.RelatorRank.HasProP2Presentation (galoisGroup M) d r) :
    HasProTwoPresentation Kc d r := by
  obtain ⟨P⟩ := h
  have hsmall : HasProTwoPresentation Kc d P.rel.card := by
    refine ⟨M, P.gen, fun i => (P.rel.equivFin.symm i : FreeGroup (Fin d)), ?_, P.dense⟩
    have hrange : Set.range (fun i : Fin P.rel.card => (P.rel.equivFin.symm i : FreeGroup (Fin d)))
        = (P.rel : Set (FreeGroup (Fin d))) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (P.rel.equivFin.symm i).2
      · intro hx
        exact ⟨P.rel.equivFin ⟨x, hx⟩, by simp⟩
    rw [P.ker_eq, hrange]
  exact hasProTwoPresentation_mono hsmall P.card_le

/-- **`RelatorRankLe (G_∅) 6` gives the chapter's crux `HasProTwoPresentation Kc 5 6`.**

`Work.RelatorRank.RelatorRankLe Γ 6` is `HasProP2Presentation Γ (GeneratorRank Γ) 6`, so
`generatorRank_galoisGroup_Kc` converts it, after which `hasProTwoPresentation_of_hasProP2Presentation`
applies. -/
theorem hasProTwoPresentation_of_relatorRankLe_six
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (h : Work.RelatorRank.RelatorRankLe (galoisGroup M) 6) :
    HasProTwoPresentation Kc 5 6 := by
  have hgr := generatorRank_galoisGroup_Kc M
  have h' : Work.RelatorRank.HasProP2Presentation (galoisGroup M) 5 6 := hgr ▸ h
  exact hasProTwoPresentation_of_hasProP2Presentation M h'

/-! ## The classical cohomological form of the crux -/

/-- **The classical Shafarevich--Koch relation bound for `Kc`, in cohomological form.**

`dim_{𝔽₂} H²_cont(G_∅, 𝔽₂) ≤ 6` for the maximal unramified pro-`2` group of `Kc = ℚ(√-30030)`,
stated with the genuine continuous cohomology group `Work.RelatorRank.contH2 (galoisGroup M)` of
the parallel chapter `Submission.Work.ConCohomology` (`ContH2DimLe Γ r` is
`∃ k ≤ r, Nat.card (H²(Γ,𝔽₂)) = 2 ^ k`, so it is false when `H²` is infinite).

This is the deliverable's item (2) in its classical normalisation: Koch Ch. 11 Thm. 11.3
(`Sha_∅ ↪ (V_∅/K^{×2})^∨`, with `#(V_∅/Kc^{×2}) = 2^6`, README §9.4) or Wingberg's duality
(NSW Ch. VIII §8 Thm. 8.8.1).  The `6` is `d + d₂(O_{Kc}^×) = 5 + 1`. -/
def KcKochCohomologyBound : Prop :=
  ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
    Work.RelatorRank.ContH2DimLe (galoisGroup M) 6

/-- **The crux from the two classical inputs.**

Given Gaschütz's value theorem `r(Γ) = dim_{𝔽₂} H²(Γ,𝔽₂)` for `Γ = G_∅` and the arithmetic bound
`dim_{𝔽₂} H²_cont(G_∅,𝔽₂) ≤ 6`, the chapter obtains its presentation interface
`KcProTwoPresentationInput`.  Nothing else is used. -/
theorem kcProTwoPresentationInput_of_contH2DimLe
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hdict : Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) : KcProTwoPresentationInput :=
  kcProTwoPresentationInput_of_five_six
    (hasProTwoPresentation_of_relatorRankLe_six M
      (Work.RelatorRank.relatorRankLe_of_contH2DimLe hdict h))

/-- **The crux from the two classical inputs, both stated in their `∃ M`/`∀ M` forms.** -/
theorem kcProTwoPresentationInput_of_kochCohomologyBound
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : KcKochCohomologyBound) : KcProTwoPresentationInput := by
  obtain ⟨M, hM⟩ := h
  exact kcProTwoPresentationInput_of_contH2DimLe M (hdict M) hM

/-- **Conversely, the crux forces the cohomological bound**, so `KcKochCohomologyBound` is
*exactly* the arithmetic content of the chapter's crux and not a weakening of it. -/
theorem kochCohomologyBound_of_kcProTwoPresentationInput
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : KcProTwoPresentationInput) : KcKochCohomologyBound := by
  obtain ⟨M, g, w, hker, hdense⟩ := hasProTwoPresentation_six_of_input h
  have hrr : Work.RelatorRank.RelatorRankLe (galoisGroup M) 6 := by
    show Work.RelatorRank.HasProP2Presentation (galoisGroup M)
      (Work.RelatorRank.GeneratorRank (galoisGroup M)) 6
    rw [generatorRank_galoisGroup_Kc M]
    exact hasProP2Presentation_of_relators M g w hker hdense
  exact ⟨M, Work.RelatorRank.contH2DimLe_of_relatorRankLe (hdict M) hrr⟩

/-- **The crux *is* the cohomological relation bound** (given the shared value theorem): the two
named inputs -- Gaschütz's dictionary for `G_∅` and the classical bound
`dim_{𝔽₂} H²_cont(G_∅, 𝔽₂) ≤ 6` -- are equivalent to `KcProTwoPresentationInput`. -/
theorem kcProTwoPresentationInput_iff_kochCohomologyBound
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M)) :
    KcProTwoPresentationInput ↔ KcKochCohomologyBound :=
  ⟨kochCohomologyBound_of_kcProTwoPresentationInput hdict,
    kcProTwoPresentationInput_of_kochCohomologyBound hdict⟩

/-! ## The walls, from the two classical inputs -/

/-- **The concrete conclusion from the cohomological form of the relation bound.** -/
theorem infiniteProTwoExtension_Kc_of_contH2DimLe
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hdict : Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) :
    Work.ClassFieldTower.InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_Kc_of_input (kcProTwoPresentationInput_of_contH2DimLe M hdict h)

/-- **The caller's wall `Submission.NumberField.UnramifiedPro2TowerWall`, from the two classical
inputs.** -/
theorem unramifiedPro2TowerWall_of_contH2DimLe
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hdict : Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) :
    Submission.NumberField.UnramifiedPro2TowerWall :=
  unramifiedPro2TowerWall_of_input (kcProTwoPresentationInput_of_contH2DimLe M hdict h)

/-- **The caller's wall `Submission.NumberField.BoundedRdTowerWall`, from the two classical
inputs.** -/
theorem boundedRdTowerWall_of_contH2DimLe
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hdict : Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) :
    Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_input (kcProTwoPresentationInput_of_contH2DimLe M hdict h)

/-- **Unramified levels of every prescribed degree with constant root discriminant, from the two
classical inputs.** -/
theorem exists_unramifiedLevel_rootDiscr_of_contH2DimLe
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2)
    (hdict : Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M))
    (h : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc :=
  exists_unramifiedLevel_rootDiscr_of_hasProTwoPresentation
    (hasProTwoPresentation_six_of_input (kcProTwoPresentationInput_of_contH2DimLe M hdict h))
    le_rfl N

end Work.ShafarevichKoch
