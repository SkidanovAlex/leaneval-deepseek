import Mathlib
import Submission.Work.SSGRoute.PTW.Prelude
import Submission.Work.SSGRoute.PTW.exists_open_index_p_notMem_of_totallyDisconnected_exponent
import Submission.Work.SSGRoute.PTW.connectedComponentOfOne_le_of_isOpen_subgroup
import Submission.Work.SSGRoute.PTW.logSectionDefs
import Submission.Work.SSGRoute.PTW.abs_ideleClassGroup_pow_surjective
import Submission.Work.SSGRoute.PTW.connectedComponent_pow_surjective
import Submission.Work.SSGRoute.PTW.ideleClassGroup_quotient_instances
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace «ℕ»

/-- The name `ℕ.Prime` used in the specification of the main theorem: it is `Nat.Prime`. -/
abbrev Prime : ℕ → Prop := Nat.Prime

end «ℕ»

namespace Work.SSGRoute.PTW

open NK.GlobalCFT

/-- Auxiliary: the specification writes the primality hypothesis as `[Fact ℕ.Prime p]`, which
Lean parses as `(Fact ℕ.Prime) p`; this abbreviation makes that parse the intended
`Fact (Nat.Prime p)`. -/
abbrev Fact (P : ℕ → Prop) (n : ℕ) : Prop := _root_.Fact (P n)

set_option checkBinderAnnotations false

/-!
# The `p`-power criterion in the idèle class group

Main result: an element of `C_K = 𝕀 K ⧸ Kˣ` lying in every open subgroup of index `p` is a
`p`-th power.  The proof reduces, via `connectedComponentOfOne_le_of_isOpen_subgroup`, to the
compact totally disconnected quotient `C_K ⧸ C_K^0`, on which the open index-`p` subgroups separate
points (`exists_open_index_p_notMem_of_totallyDisconnected_exponent`), and uses the divisibility of
the identity component `C_K^0`.
-/

/-- The identity component of a totally disconnected topological group is trivial. -/
theorem connectedComponentOfOne_eq_bot_of_totallyDisconnected (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [TotallyDisconnectedSpace G] :
    Subgroup.connectedComponentOfOne G = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h : connectedComponent (1 : G) = {1} :=
    totallyDisconnectedSpace_iff_connectedComponent_one.mp inferInstance
  have hx' : x ∈ connectedComponent (1 : G) := hx
  rw [h] at hx'
  simpa using hx'

/-- **The Frattini/`p`-power criterion for compact totally disconnected abelian groups.**

If `G` is a compact Hausdorff totally disconnected abelian topological group and `x ∈ G` lies in
every open subgroup of index `p`, then `x` is a `p`-th power.  (Needed: the quotient
`C_K ⧸ C_K^0` of the idèle class group by its identity component is of this form.) -/
theorem exists_pow_eq_of_forall_open_index_p {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (p : ℕ) [_root_.Fact (Nat.Prime p)] (x : G)
    (hx : ∀ V : Subgroup G, V.FiniteIndex → IsOpen (V : Set G) → V.index = p → x ∈ V) :
    ∃ y : G, y ^ p = x := by
  classical
  have hpc : Continuous (⇑(powMonoidHom p) : G → G) := by
    have hfun : (⇑(powMonoidHom p) : G → G) = fun g : G => g ^ p := by
      funext g; exact powMonoidHom_apply p g
    rw [hfun]; exact continuous_id.pow p
  set N : Subgroup G := (powMonoidHom p).range with hN
  have hNclosed : IsClosed (N : Set G) := by
    rw [hN, MonoidHom.coe_range]
    exact (isCompact_range hpc).isClosed
  haveI : IsClosed (N : Set G) := hNclosed
  haveI : T2Space (G ⧸ N) := inferInstance
  haveI htd : TotallyDisconnectedSpace (G ⧸ N) := by
    rw [hN]
    exact totallyDisconnectedSpace_quotient_of_connectedComponentOfOne_le hNclosed
      ((connectedComponentOfOne_eq_bot_of_totallyDisconnected G).le.trans bot_le)
  have hexp : ∀ q : G ⧸ N, q ^ p = 1 := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨g, (powMonoidHom_apply p g).symm⟩
  by_contra hcon
  push_neg at hcon
  have hxN : (QuotientGroup.mk' N x) ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN] at h
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp h
    exact hcon g (by rw [← hg, powMonoidHom_apply])
  obtain ⟨U, hUopen, hUindex, hUx⟩ :=
    exists_open_index_p_notMem_of_totallyDisconnected_exponent (G ⧸ N) p hexp
      (QuotientGroup.mk' N x) hxN
  have hsurj := QuotientGroup.mk'_surjective N
  refine hUx ?_
  have hmem : x ∈ Subgroup.comap (QuotientGroup.mk' N) U := by
    refine hx _ ?_ ?_ ?_
    · rw [Subgroup.finiteIndex_iff, Subgroup.index_comap_of_surjective _ hsurj, hUindex]
      exact (_root_.Fact.out : Nat.Prime p).ne_zero
    · exact hUopen.preimage QuotientGroup.continuous_mk
    · rw [Subgroup.index_comap_of_surjective _ hsurj, hUindex]
  rwa [Subgroup.mem_comap] at hmem

/-- **Reduction step.**  If the quotient `C_K ⧸ C_K^0` is compact and totally disconnected and the
identity component `C_K^0` is `p`-divisible, then an element of `C_K` lying in every open subgroup
of index `p` is a `p`-th power.  (The hypothesis passes to `C_K ⧸ C_K^0` because every open index-`p`
subgroup of `C_K` contains `C_K^0`; the Frattini criterion
`exists_pow_eq_of_forall_open_index_p` applies to the profinite quotient, and the resulting
`p`-th power disagrees with `x` by an element of `C_K^0`.) -/
theorem exists_pow_eq_of_mem_all_open_index_p_of_quotient (K : Type) [Field K] [NumberField K]
    (p : ℕ) [_root_.Fact (Nat.Prime p)] (x : NK.GlobalCFT.IdeleClassGroup K)
    [CompactSpace (NK.GlobalCFT.IdeleClassGroup K ⧸
      Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K))]
    [TotallyDisconnectedSpace (NK.GlobalCFT.IdeleClassGroup K ⧸
      Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K))]
    (hA : ∀ g : NK.GlobalCFT.IdeleClassGroup K,
      g ∈ Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K) →
        ∃ z : NK.GlobalCFT.IdeleClassGroup K, z ^ p = g)
    (hx : ∀ V : Subgroup (NK.GlobalCFT.IdeleClassGroup K), V.FiniteIndex →
        IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K)) → V.index = p → x ∈ V) :
    ∃ y : NK.GlobalCFT.IdeleClassGroup K, y ^ p = x := by
  classical
  set N : Subgroup (NK.GlobalCFT.IdeleClassGroup K) :=
    Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K) with hN
  haveI hNcl : IsClosed (N : Set (NK.GlobalCFT.IdeleClassGroup K)) := isClosed_connectedComponent
  have hxq : ∀ U : Subgroup (NK.GlobalCFT.IdeleClassGroup K ⧸ N), U.FiniteIndex →
      IsOpen (U : Set (NK.GlobalCFT.IdeleClassGroup K ⧸ N)) → U.index = p →
      (QuotientGroup.mk' N x) ∈ U := by
    intro U _ hUopen hUindex
    have hsurj := QuotientGroup.mk'_surjective N
    have hmem : x ∈ Subgroup.comap (QuotientGroup.mk' N) U := by
      refine hx _ ?_ ?_ ?_
      · rw [Subgroup.finiteIndex_iff, Subgroup.index_comap_of_surjective _ hsurj, hUindex]
        exact (_root_.Fact.out : Nat.Prime p).ne_zero
      · exact hUopen.preimage QuotientGroup.continuous_mk
      · rw [Subgroup.index_comap_of_surjective _ hsurj, hUindex]
    rwa [Subgroup.mem_comap] at hmem
  obtain ⟨yq, hyq⟩ :=
    exists_pow_eq_of_forall_open_index_p (G := NK.GlobalCFT.IdeleClassGroup K ⧸ N) p
      (QuotientGroup.mk' N x) hxq
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N yq
  have hg : x * (y⁻¹) ^ p ∈ N := by
    have h1 : (QuotientGroup.mk' N) (y ^ p) = (QuotientGroup.mk' N) x := by
      rw [map_pow, hyq]
    have h2 : (QuotientGroup.mk' N) (y ^ p * x⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h3 : (y ^ p * x⁻¹)⁻¹ ∈ N := N.inv_mem h2
    simpa [inv_pow, mul_inv_rev] using h3
  obtain ⟨z, hz⟩ := hA (x * (y⁻¹) ^ p) hg
  exact ⟨z * y, by rw [mul_pow, hz]; group⟩


/-- **The `p`-power criterion in the idèle class group.**  An element of `C_K = 𝕀 K ⧸ Kˣ` lying in
every open subgroup of index `p` is a `p`-th power. -/
theorem mem_pthPower_in (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact ℕ.Prime p]
    (x : NK.GlobalCFT.IdeleClassGroup K)
    (hx : ∀ (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)), V.FiniteIndex →
        IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K)) → V.index = p → x ∈ V) :
    ∃ y : NK.GlobalCFT.IdeleClassGroup K, y ^ p = x := by
  obtain ⟨hcomp, htd⟩ := ideleClassGroup_quotient_instances K
  haveI : CompactSpace (NK.GlobalCFT.IdeleClassGroup K ⧸
      Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K)) := hcomp
  haveI : TotallyDisconnectedSpace (NK.GlobalCFT.IdeleClassGroup K ⧸
      Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K)) := htd
  exact exists_pow_eq_of_mem_all_open_index_p_of_quotient K p x
    (fun g _ => connectedComponent_pow_surjective K p g ‹_›) hx


end Work.SSGRoute.PTW
