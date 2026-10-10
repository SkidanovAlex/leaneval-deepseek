import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped Classical

namespace NK.TameStructure.ProCyclic

theorem exists_topologicallyCyclic_of_isProCyclic {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [CompactSpace H] [TotallyDisconnectedSpace H]
    (h : NK.LocalTame.IsProCyclic H) :
    ∃ g : H, ∀ N : OpenNormalSubgroup H,
      Subgroup.zpowers (QuotientGroup.mk' N.toSubgroup g) = ⊤ := by
  classical
  -- the projection `H → H ⧸ N` is continuous
  have hcont : ∀ N : OpenNormalSubgroup H,
      Continuous (QuotientGroup.mk' N.toSubgroup : H → H ⧸ N.toSubgroup) := by
    intro N
    rw [QuotientGroup.coe_mk']
    exact continuous_coinduced_rng
  -- `T N` is closed: it is the preimage of the (finite, hence closed) set of generators of the
  -- finite quotient `H ⧸ N`
  have hclosed : ∀ N : OpenNormalSubgroup H,
      IsClosed {x : H | Subgroup.zpowers (QuotientGroup.mk' N.toSubgroup x) = ⊤} := by
    intro N
    haveI : T1Space (H ⧸ N.toSubgroup) := inferInstance
    have hfin : ({y : H ⧸ N.toSubgroup | Subgroup.zpowers y = ⊤} : Set (H ⧸ N.toSubgroup)).Finite :=
      (Set.toFinite _).subset (Set.subset_univ _)
    have hh := (hfin.isClosed).preimage (hcont N)
    simpa [Set.preimage_ofPred_eq] using hh
  -- finite intersection property
  have hfip : ∀ u : Finset (OpenNormalSubgroup H),
      (⋂ N ∈ u, {x : H | Subgroup.zpowers (QuotientGroup.mk' N.toSubgroup x) = ⊤}).Nonempty := by
    intro u
    rcases u.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, by simp⟩
    · -- the infimum of the (finitely many) quotients by which we must generate
      set M : OpenNormalSubgroup H := u.inf' hne id with hMdef
      have hMle : ∀ N ∈ u, M ≤ N := fun N hN => by
        rw [hMdef]; exact Finset.inf'_le id hN
      haveI : Finite (H ⧸ M.toSubgroup) := inferInstance
      haveI hfi : M.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      haveI hcyc : IsCyclic (H ⧸ M.toSubgroup) := h M.toSubgroup hfi
      obtain ⟨x0, hx0⟩ := IsCyclic.exists_generator (α := H ⧸ M.toSubgroup)
      have hgen0 : Subgroup.zpowers x0 = ⊤ := (Subgroup.eq_top_iff' _).mpr hx0
      obtain ⟨g, hgm⟩ := QuotientGroup.mk'_surjective M.toSubgroup x0
      refine ⟨g, ?_⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro N hN
      have hle : M.toSubgroup ≤ N.toSubgroup := hMle N hN
      let f : H ⧸ M.toSubgroup →* H ⧸ N.toSubgroup :=
        QuotientGroup.map M.toSubgroup N.toSubgroup (MonoidHom.id H) hle
      have key : f (QuotientGroup.mk' M.toSubgroup g) = QuotientGroup.mk' N.toSubgroup g := by
        show (QuotientGroup.map M.toSubgroup N.toSubgroup (MonoidHom.id H) hle)
          (QuotientGroup.mk' M.toSubgroup g) = QuotientGroup.mk' N.toSubgroup g
        exact QuotientGroup.map_mk' M.toSubgroup N.toSubgroup (MonoidHom.id H) hle g
      have hfsurj : Function.Surjective f := by
        intro z
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N.toSubgroup z
        refine ⟨QuotientGroup.mk' M.toSubgroup x, ?_⟩
        show (QuotientGroup.map M.toSubgroup N.toSubgroup (MonoidHom.id H) hle)
          (QuotientGroup.mk' M.toSubgroup x) = QuotientGroup.mk' N.toSubgroup x
        exact QuotientGroup.map_mk' M.toSubgroup N.toSubgroup (MonoidHom.id H) hle x
      have h1 : Subgroup.zpowers (QuotientGroup.mk' M.toSubgroup g) = ⊤ := by
        rw [hgm, hgen0]
      -- a surjection between cyclic groups sends generators to generators
      calc Subgroup.zpowers (QuotientGroup.mk' N.toSubgroup g)
          = Subgroup.zpowers (f (QuotientGroup.mk' M.toSubgroup g)) := by rw [key]
        _ = ⊤ := by rw [← MonoidHom.map_zpowers, h1, Subgroup.map_top_of_surjective f hfsurj]
  -- compactness of `H` produces a common element
  have hfin : (⋂ N : OpenNormalSubgroup H,
      {x : H | Subgroup.zpowers (QuotientGroup.mk' N.toSubgroup x) = ⊤}).Nonempty := by
    have hh := isCompact_univ.inter_iInter_nonempty
      (fun N : OpenNormalSubgroup H => {x : H | Subgroup.zpowers (QuotientGroup.mk' N.toSubgroup x) = ⊤})
      hclosed (fun u => by simpa using hfip u)
    simpa using hh
  obtain ⟨g, hg⟩ := hfin
  exact ⟨g, fun N => Set.mem_iInter.mp hg N⟩

end NK.TameStructure.ProCyclic
