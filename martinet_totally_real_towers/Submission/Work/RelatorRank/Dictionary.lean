import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.RelatorRank.Discrete
import Submission.Work.HopfGaschutz.All

/-!
# `Work.RelatorRank` -- the relation-rank dictionary, and where the open problem is

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.Dictionary`.

This module connects the two chapters that share the relation-rank dictionary:

* this one, which owns the presentation language `HasProP2Presentation` / `RelatorRankLe` /
  `RelatorHalfOf` / `RelationRankInvariant` and the *continuous* cohomology `contH2 Γ = H²(Γ,𝔽₂)`
  (`CohomologyH2.lean`);
* `Submission.Work.HopfGaschutz`, which owns the Hopf/transgression content: for a finite group `Q`
  with a minimal generating family, the transgression is a *bijection*
  `Z¹(K,𝔽₂)^Q ≃ H²(Q,𝔽₂)` (`Work.HopfGaschutz.h2DimOf_eq_log_card_contH2`), the *easy* direction of
  the dictionary is proved (`Work.HopfGaschutz.log_card_contH2_le_card_of_presentation`), and the
  *hard* direction is isolated as the named `Prop` `Work.HopfGaschutz.GaschutzDictionary`.

## What this module proves

* `contH2_log_card_le_of_hasProP2Presentation`: **one half of `GaschutzCohomologicalValue`, in this
  chapter's vocabulary and unconditionally**: a presentation of a finite `2`-group on a minimal
  generating family by `r` relators forces `dim_{𝔽₂} H²(Γ,𝔽₂) ≤ r`.  So in the finite case the
  implication "presentation `⟹` cohomological bound" is a theorem.
* `hasProP2Presentation_of_gaschutzDictionary`: the converse, from the neighbouring chapter's named
  input.

## What is *not* provable here (important)

The remaining direction -- "`dim_{𝔽₂} H² ≤ r` `⟹` a presentation with `≤ r` relators" -- is, for
finite `p`-groups, *exactly* the statement that a minimal presentation of a finite `p`-group has
`dim H²` relators, i.e. that `G` is **efficient**; `Work.HopfGaschutz.Dictionary.
gaschutzDictionary_iff_minimalRelatorSet` proves this equivalence, and it is an **open problem**
(Mann, *Some questions about `p`-groups*, Question 18; Gardam, arXiv:1705.02040: "there is no known
example of a non-efficient finite `p`-group").  Consequently

* `GaschutzCohomologicalValue` (this chapter) and `GaschutzDictionary` (the neighbouring chapter) are
  *not* theorems of the discrete theory: the discrete formulation of the bridge is at least as hard
  as that open problem;
* the pro-`p` (closed normal closure) formulation of Gaschütz's invariance *is* a theorem of the
  classical theory -- it needs the free pro-`p` group and Nakayama over `𝔽_p[[Γ]]`, neither of which
  is in this workspace (see `README.md` §3.2);
* and the correct engineering fix for a consumer who needs the `∀ gen` form is to state the wall in
  the pro-`p`/closed category, or to supply the efficiency statement for the finite quotients.
-/

set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace Work.RelatorRank

/-- **The easy direction of the cohomological dictionary, in this chapter's vocabulary.**  If a
finite `2`-group `Γ` (discrete topology) admits a presentation on a *minimal* generating `d`-family
with at most `r` relators, then `dim_{𝔽₂} H²(Γ, 𝔽₂) ≤ r` for the continuous cohomology `contH2 Γ`.

This is `HasProP2Presentation Γ d r → (cohomological bound)`: the half of
`GaschutzCohomologicalValue` that does not need the open efficiency statement. -/
theorem contH2_log_card_le_of_hasProP2Presentation {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [DiscreteTopology Γ] [Fintype Γ] (hΓ : IsPGroup 2 Γ) {d r : ℕ}
    (hd : ∀ S : Finset Γ, Subgroup.closure (S : Set Γ) = ⊤ → d ≤ S.card)
    (h : HasProP2Presentation Γ d r) :
    Nat.log 2 (Nat.card (contH2 Γ)) ≤ r := by
  obtain ⟨P⟩ := h
  letI : TopologicalSpace (FreeGroup (Fin d)) := ⊥
  haveI : DiscreteTopology (FreeGroup (Fin d)) := ⟨rfl⟩
  have hgen : Subgroup.closure (Set.range P.gen) = ⊤ :=
    (denseGenerating_iff_generating_of_discrete P.gen).mp P.dense
  have hmin : Work.HopfGaschutz.presKernel P.gen ≤ Work.HopfGaschutz.relFrattini 2 ⊤ :=
    Work.HopfGaschutz.le_relFrattini_of_minimal_generating hΓ P.gen hgen
      (fun S hS => by simpa using hd S hS)
  exact le_trans
    (Work.HopfGaschutz.log_card_contH2_le_card_of_presentation (α := Fin d) (Q := Γ)
      P.gen hgen hmin P.rel P.ker_eq) P.card_le

/-- **The converse, from the neighbouring chapter's named input.**  If
`Work.HopfGaschutz.GaschutzDictionary 2` -- the (open) efficiency statement for finite `2`-groups --
is available, then a cohomological bound `dim_{𝔽₂} H²(Γ,𝔽₂) ≤ r` produces a presentation of a finite
`2`-group `Γ` on a given minimal generating `d`-family with at most `r` relators, i.e. the `∃`-form
`HasProP2Presentation Γ d r`. -/
theorem hasProP2Presentation_of_gaschutzDictionary {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [DiscreteTopology Γ] [Fintype Γ] (hΓ : IsPGroup 2 Γ)
    (hdict : Work.HopfGaschutz.GaschutzDictionary 2) {d r : ℕ}
    (hex : HasDenseGeneratingFamily Γ d)
    (hd : ∀ S : Finset Γ, Subgroup.closure (S : Set Γ) = ⊤ → d ≤ S.card)
    (h : Nat.log 2 (Nat.card (contH2 Γ)) ≤ r) : HasProP2Presentation Γ d r := by
  obtain ⟨gen, hgen'⟩ := hex
  letI : TopologicalSpace (FreeGroup (Fin d)) := ⊥
  haveI : DiscreteTopology (FreeGroup (Fin d)) := ⟨rfl⟩
  have hgen : Subgroup.closure (Set.range gen) = ⊤ :=
    (denseGenerating_iff_generating_of_discrete gen).mp hgen'
  have hmin : Work.HopfGaschutz.presKernel gen ≤ Work.HopfGaschutz.relFrattini 2 ⊤ :=
    Work.HopfGaschutz.le_relFrattini_of_minimal_generating hΓ gen hgen
      (fun S hS => by simpa using hd S hS)
  have hval : Work.HopfGaschutz.h2DimOf 2 (Fin d) Γ gen = Nat.log 2 (Nat.card (contH2 Γ)) :=
    Work.HopfGaschutz.h2DimOf_eq_log_card_contH2 gen hgen hmin
  have hmin' : ∀ S : Finset Γ, Subgroup.closure (S : Set Γ) = ⊤ → Fintype.card (Fin d) ≤ S.card :=
    fun S hS => by simpa using hd S hS
  have hval' : Work.HopfGaschutz.h2DimOf 2 (Fin d) Γ gen ≤ r := by rw [hval]; exact h
  obtain ⟨rel, hcard, hker⟩ :=
    Work.HopfGaschutz.exists_relatorSet_of_le_h2DimOf (p := 2) (α := Fin d) (G := Γ)
      hdict hΓ gen hgen hmin' hval'
  exact ⟨gen, rel, hgen', hcard, hker⟩

end Work.RelatorRank
