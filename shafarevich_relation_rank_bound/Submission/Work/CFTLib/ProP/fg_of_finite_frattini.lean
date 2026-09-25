import Mathlib
import Submission.Work.CFT.MaxProP.ContCohomology.Frattini
import Submission.Work.CFT.MaxProP.ContCohomology.Burnside.topGeneratorRank_eq_finrank_H1FpCont

namespace Work.CFTLib.ProP

open Work.CFT.MaxProP

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **A pro-`p` group with finite Frattini quotient is topologically finitely generated.**

Let `G` be a profinite (= compact, Hausdorff, totally disconnected, topological) group all of whose
finite continuous quotients `G ⧸ U` (for `U : OpenNormal G`) are `p`-groups, and let
`N = proPFrattini p G = closure(G^p · [G,G])` be its Frattini subgroup (the library's
`Work.CFT.MaxProP.proPFrattini`).  If the Frattini quotient `G ⧸ N` is finite, then `G` has a
finite topological generating set.

This is the structural half of Burnside's basis result used by
`Work.CFT.MaxProP.ContCohomology.Burnside.topGeneratorRank_eq_finrank_H1FpCont`, whose proof
needs `∃ d, ∃ f : FreeGroup (Fin d) →* G, closure (Set.range f) = Set.univ` as a hypothesis; here
that hypothesis is deduced from finiteness of the Frattini quotient.

Proof sketch.  Since `G ⧸ N` is finite, choose a finite set `g` of preimages of a generating set
of `G ⧸ N` (a finite elementary abelian `p`-group).  Then `G = closure(g) · N`.  To show
`closure(g)` is dense it suffices (by the library's
`Work.CFT.MaxProP.ContCohomology.Burnside.exists_openNormalSubgroup_sup_ne_top`, which says that a
closed proper subgroup of a pro-`p` group misses an open normal subgroup) to show
`closure(g) ⊔ U = ⊤` for every open normal subgroup `U`.  In the finite `p`-group `G ⧸ U`, the
image of `N = Φ(G)` lies in the Frattini subgroup
(`Work.CFT.MaxProP.ContCohomology.Burnside.map_proPFrattini_le_frattini`), and `closure(g)` maps
onto a subgroup generating modulo the Frattini subgroup, hence onto everything
(`frattini_nongenerating`), so `closure(g) ⊔ U = ⊤`. -/
theorem fg_of_finite_frattini
    (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ∀ U : Work.CFT.MaxProP.OpenNormal G, IsPGroup p (G ⧸ U.carrier))
    (N : Subgroup G) [N.Normal] (hN : N = Work.CFT.MaxProP.proPFrattini p G)
    (hfin : Finite (G ⧸ N)) :
    ∃ S : Finset G, (Subgroup.closure (S : Set G)).topologicalClosure = ⊤ := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  haveI : Finite (G ⧸ N) := hfin
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  -- A section of the projection `G → G ⧸ N`.
  let g : (G ⧸ N) → G := fun q => Classical.choose (QuotientGroup.mk'_surjective N q)
  have hg : ∀ q : G ⧸ N, QuotientGroup.mk' N (g q) = q :=
    fun q => Classical.choose_spec (QuotientGroup.mk'_surjective N q)
  let S : Finset G := Finset.univ.image g
  have hSrange : (S : Set G) = Set.range g := by
    simp [S, Finset.coe_image, Set.image_univ]
  refine ⟨S, ?_⟩
  -- `S` generates `G` modulo `N`.
  have hsup : Subgroup.closure (S : Set G) ⊔ N = ⊤ := by
    have hmap : Subgroup.map (QuotientGroup.mk' N) (Subgroup.closure (S : Set G)) = ⊤ := by
      rw [hSrange, MonoidHom.map_closure]
      have himg : (QuotientGroup.mk' N) '' Set.range g = Set.univ := by
        rw [← Set.range_comp]
        have hcomp : (QuotientGroup.mk' N) ∘ g = id :=
          funext fun q => by simp [Function.comp, hg q]
        rw [hcomp, Set.range_id]
      rw [himg, Subgroup.closure_univ]
    have h := Subgroup.comap_map_eq (QuotientGroup.mk' N) (Subgroup.closure (S : Set G))
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  set K : Subgroup G := (Subgroup.closure (S : Set G)).topologicalClosure with hKdef
  have hKN : K ⊔ N = ⊤ := by
    rw [eq_top_iff, ← hsup]
    have h1 : Subgroup.closure (S : Set G) ≤ K := by
      rw [hKdef]
      exact Subgroup.le_topologicalClosure _
    exact sup_le_sup h1 le_rfl
  have hKclosed : IsClosed (K : Set G) := by
    rw [hKdef]
    exact Subgroup.isClosed_topologicalClosure _
  by_contra hne
  obtain ⟨x, -, hxK⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  obtain ⟨U, hU⟩ :=
    Work.CFT.MaxProP.ContCohomology.Burnside.exists_openNormalSubgroup_sup_ne_top hKclosed hxK
  have hUsub : IsOpen (U.toSubgroup : Set G) := U.isOpen'
  have hUp : IsPGroup p (G ⧸ U.toSubgroup) := hG ⟨U.toSubgroup, U.isNormal', hUsub⟩
  have hfratt : N.map (QuotientGroup.mk' U.toSubgroup) ≤ frattini (G ⧸ U.toSubgroup) := by
    rw [hN]
    exact Work.CFT.MaxProP.ContCohomology.Burnside.map_proPFrattini_le_frattini
      U.toSubgroup hUsub hUp
  haveI : Finite (G ⧸ U.toSubgroup) := U.toSubgroup.quotient_finite_of_isOpen hUsub
  haveI : IsCoatomic (Subgroup (G ⧸ U.toSubgroup)) := Finite.to_isCoatomic
  have hstep : K.map (QuotientGroup.mk' U.toSubgroup) ⊔ frattini (G ⧸ U.toSubgroup) = ⊤ := by
    have h1 : K.map (QuotientGroup.mk' U.toSubgroup) ⊔
        N.map (QuotientGroup.mk' U.toSubgroup) ≤
        K.map (QuotientGroup.mk' U.toSubgroup) ⊔ frattini (G ⧸ U.toSubgroup) :=
      sup_le_sup le_rfl hfratt
    rw [← Subgroup.map_sup, hKN,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective U.toSubgroup)] at h1
    exact le_antisymm le_top h1
  have hKmap : K.map (QuotientGroup.mk' U.toSubgroup) = ⊤ := frattini_nongenerating hstep
  have hKU : K ⊔ U.toSubgroup = ⊤ := by
    rw [← QuotientGroup.ker_mk' U.toSubgroup,
      ← Subgroup.comap_map_eq (QuotientGroup.mk' U.toSubgroup) K, hKmap, Subgroup.comap_top]
  exact hU (hKU ▸ Subgroup.mem_top x)

end

end Work.CFTLib.ProP
