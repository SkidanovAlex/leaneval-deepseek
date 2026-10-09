import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Descending the procyclic-growth hypotheses to a quotient

Let `Γ` be a topological group and `V ⊴ Γ` a normal subgroup.  If every finite-index normal
subgroup `K ≥ V` has cyclic quotient `Γ ⧸ K` (`hcyc`) and every open normal `K ≥ V` admits an
open normal `V ≤ L ≤ K` with `p ∣ [K : L]` (`hbig`), then the same two properties hold for the
quotient group `Γ ⧸ V`:

* `Work.SSGRoute.PT.quotient_proCyclicGrowth`.

This is the interface that allows
`Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth` to be applied to `Γ ⧸ V` with coefficients
`N^V`.
-/

namespace Work.SSGRoute.PT

open scoped Pointwise

/-- Cyclicity is preserved by group isomorphisms. -/
lemma isCyclic_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : IsCyclic G) :
    IsCyclic H := by
  obtain ⟨g, hg⟩ := h
  refine ⟨e g, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective y
  obtain ⟨n, hn⟩ := hg x
  exact ⟨n, by rw [show x = g ^ n from hn.symm]; exact (map_zpow e g n).symm⟩

theorem quotient_proCyclicGrowth
    (p : ℕ) [Fact p.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (V : Subgroup Γ) [V.Normal]
    (hcyc : ∀ (K : Subgroup Γ) [K.Normal], V ≤ K → K.FiniteIndex → IsCyclic (Γ ⧸ K))
    (hbig : ∀ (K : Subgroup Γ) [K.Normal], V ≤ K → IsOpen (K : Set Γ) →
      ∃ (L : Subgroup Γ) (hL : L.Normal), V ≤ L ∧ L ≤ K ∧ IsOpen (L : Set Γ) ∧
        p ∣ (L.subgroupOf K).index) :
    (∀ (U : Subgroup (Γ ⧸ V)) [U.Normal], U.FiniteIndex → IsCyclic ((Γ ⧸ V) ⧸ U)) ∧
    (∀ (U : Subgroup (Γ ⧸ V)), IsOpen (U : Set (Γ ⧸ V)) → U.Normal →
      ∃ (U' : Subgroup (Γ ⧸ V)), U' ≤ U ∧ IsOpen (U' : Set (Γ ⧸ V)) ∧ U'.Normal ∧
        p ∣ (U'.subgroupOf U).index) := by
  classical
  have hmk : (QuotientGroup.mk' V : Γ → Γ ⧸ V) = QuotientGroup.mk :=
    funext (QuotientGroup.mk'_apply V)
  have hcont : Continuous (QuotientGroup.mk' V) := by
    rw [hmk]
    exact QuotientGroup.isOpenQuotientMap_mk.continuous
  constructor
  · intro U hUn hUfi
    set K : Subgroup Γ := U.comap (QuotientGroup.mk' V) with hK
    have hVK : V ≤ K := by
      intro v hv
      rw [hK, Subgroup.mem_comap,
        show QuotientGroup.mk' V v = 1 from (QuotientGroup.eq_one_iff v).mpr hv]
      exact U.one_mem
    haveI hKn : K.Normal := hUn.comap _
    have hKfi : K.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff, hK,
        Subgroup.index_comap_of_surjective U (QuotientGroup.mk'_surjective V)]
      exact (Subgroup.finiteIndex_iff).mp hUfi
    haveI hKfiI : K.FiniteIndex := hKfi
    have hcycK : IsCyclic (Γ ⧸ K) := hcyc K hVK hKfi
    have hmap : Subgroup.map (QuotientGroup.mk' V) K = U := by
      rw [hK]; exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) U
    have h1 : IsCyclic ((Γ ⧸ V) ⧸ Subgroup.map (QuotientGroup.mk' V) K) :=
      isCyclic_of_mulEquiv (G := Γ ⧸ K)
        (H := (Γ ⧸ V) ⧸ Subgroup.map (QuotientGroup.mk' V) K)
        (QuotientGroup.quotientQuotientEquivQuotient V K hVK).symm hcycK
    haveI : (Subgroup.map (QuotientGroup.mk' V) K).Normal := hKn.map _ (QuotientGroup.mk'_surjective V)
    exact isCyclic_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hmap) h1
  · intro U hUopen hUn
    set K : Subgroup Γ := U.comap (QuotientGroup.mk' V) with hK
    have hVK : V ≤ K := by
      intro v hv
      rw [hK, Subgroup.mem_comap,
        show QuotientGroup.mk' V v = 1 from (QuotientGroup.eq_one_iff v).mpr hv]
      exact U.one_mem
    haveI hKn : K.Normal := hUn.comap _
    have hKopen : IsOpen (K : Set Γ) := by
      have hset : (K : Set Γ) = (QuotientGroup.mk' V) ⁻¹' (U : Set (Γ ⧸ V)) := rfl
      rw [hset]
      exact hUopen.preimage hcont
    obtain ⟨L, hLn, hVL, hLK, hLopen, hpdvd⟩ := hbig K hVK hKopen
    haveI hLnI : L.Normal := hLn
    have hker : (QuotientGroup.mk' V).ker = V := QuotientGroup.ker_mk' V
    have hmap : Subgroup.map (QuotientGroup.mk' V) K = U := by
      rw [hK]; exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) U
    refine ⟨Subgroup.map (QuotientGroup.mk' V) L, ?_, ?_, ?_, ?_⟩
    · rw [hK] at hLK
      calc Subgroup.map (QuotientGroup.mk' V) L
          ≤ Subgroup.map (QuotientGroup.mk' V) (Subgroup.comap (QuotientGroup.mk' V) U) :=
            Subgroup.map_mono hLK
        _ = U := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) U
    · exact QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ hLopen
    · exact hLn.map _ (QuotientGroup.mk'_surjective V)
    · have hrel : (Subgroup.map (QuotientGroup.mk' V) L).relIndex
          (Subgroup.map (QuotientGroup.mk' V) K) = L.relIndex K := by
        rw [Subgroup.relIndex_map_map, hker, sup_eq_left.mpr hVL, sup_eq_left.mpr hVK]
      show p ∣ (Subgroup.map (QuotientGroup.mk' V) L).relIndex U
      rw [show U = Subgroup.map (QuotientGroup.mk' V) K from hmap.symm, hrel]
      exact hpdvd

end Work.SSGRoute.PT
