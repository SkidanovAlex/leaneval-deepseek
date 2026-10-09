import Mathlib
import Submission.Work.SSGRoute.PTW.CompactAbelianExponentP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTW

/-- **The Frattini/`p`-power criterion for compact abelian groups.**  For a compact Hausdorff
abelian topological group `G` and a prime `p`, an element lies in every open subgroup of index `p`
if and only if it lies in the closure of the set of `p`-th powers (equivalently, of the subgroup
they generate). -/
theorem mem_all_open_index_p_iff_mem_closure_pthPowers (G : Type*) [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (p : ℕ) [Fact p.Prime] (x : G) :
    (∀ V : Subgroup G, V.FiniteIndex → IsOpen (V : Set G) → V.index = p → x ∈ V) ↔
      x ∈ closure {y : G | ∃ z : G, z ^ p = y} := by
  constructor
  · -- The hard direction: pass to the compact abelian quotient by the closed subgroup generated
    -- by the `p`-th powers, which is compact Hausdorff abelian of exponent `p`, so that open
    -- index-`p` subgroups separate its points.
    intro hx
    let P : Subgroup G :=
      { carrier := Set.range (fun z : G => z ^ p)
        one_mem' := ⟨1, by simp⟩
        mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, by simp only [mul_pow]⟩
        inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, by simp only [inv_pow]⟩ }
    have hPcoe : (P : Set G) = {y : G | ∃ z : G, z ^ p = y} := rfl
    set K : Subgroup G := P.topologicalClosure with hK
    haveI : K.Normal := inferInstance
    haveI : IsClosed (K : Set G) := Subgroup.isClosed_topologicalClosure P
    have hKcoe : (K : Set G) = closure {y : G | ∃ z : G, z ^ p = y} := by
      rw [hK, Subgroup.topologicalClosure_coe, hPcoe]
    have hexp : ∀ q : G ⧸ K, q ^ p = 1 := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K q
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.le_topologicalClosure P ⟨g, rfl⟩
    have hxQ : ∀ U : Subgroup (G ⧸ K), U.FiniteIndex → IsOpen (U : Set (G ⧸ K)) →
        U.index = p → (QuotientGroup.mk x : G ⧸ K) ∈ U := by
      intro U _ hUopen hUidx
      have hcont : Continuous (QuotientGroup.mk' K : G →* G ⧸ K) := QuotientGroup.continuous_mk
      have hidx : (Subgroup.comap (QuotientGroup.mk' K) U).index = p := by
        rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K), hUidx]
      have hfin : (Subgroup.comap (QuotientGroup.mk' K) U).FiniteIndex :=
        Subgroup.finiteIndex_iff.mpr (by rw [hidx]; exact (Fact.out : p.Prime).ne_zero)
      have hmem := hx _ hfin (hUopen.preimage hcont) hidx
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply] at hmem
      exact hmem
    by_contra hxc
    have hne : (QuotientGroup.mk x : G ⧸ K) ≠ 1 := by
      intro h
      exact hxc (by rw [← hKcoe]; exact QuotientGroup.eq_one_iff x |>.mp h)
    obtain ⟨U, hUo, hUi, hUq⟩ :=
      exists_open_index_p_notMem_of_compact_abelian_exponent_p (G ⧸ K) p hexp
        (QuotientGroup.mk x) hne
    have hfinU : U.FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by rw [hUi]; exact (Fact.out : p.Prime).ne_zero)
    exact hUq (hxQ U hfinU hUo hUi)
  · -- The easy direction: the `p`-th powers lie in every open index-`p` subgroup, which is closed.
    intro hx V _ hVopen hVidx
    have hSclosed : IsClosed {y : G | ∃ z : G, z ^ p = y} := by
      have hh : {y : G | ∃ z : G, z ^ p = y} = Set.range (fun z : G => z ^ p) := rfl
      rw [hh]; exact IsCompact.isClosed (isCompact_range (continuous_id.pow p))
    rw [hSclosed.closure_eq] at hx
    obtain ⟨z, rfl⟩ := hx
    have hcard : Nat.card (G ⧸ V) = p := by rw [← Subgroup.index_eq_card]; exact hVidx
    have h1 : ((QuotientGroup.mk z : G ⧸ V)) ^ p = 1 := by
      have := pow_card_eq_one' (x := (QuotientGroup.mk z : G ⧸ V))
      rwa [hcard] at this
    rw [← QuotientGroup.eq_one_iff (z ^ p), QuotientGroup.mk_pow]
    exact h1

end Work.SSGRoute.PTW
