import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.Reductions.Defs
import Submission.Work.ThreePoints.map_oddCore_le_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O^{2'}(G)` in the `Reductions` chapter

`Submission.Blueprint.oddResidual G = sInf {N : Subgroup G | N.Normal ∧ Odd N.index}` is the
smallest normal subgroup of odd index.  This file collects the API used by the reduction of
Theorem B (`ReductionsProp`):

* `oddResidual_basic` — `O^{2'}(G)` is normal, has odd index, is minimal with that property,
  and contains every involution (`x * x = 1 → x ∈ O^{2'}(G)`);
* `oddResidual_self_eq_top` — `O^{2'}(O^{2'}(G)) = O^{2'}(G)` (idempotency);
* `oddCore_oddResidual_basic` — if `O(G) = 1` then `O(O^{2'}(G)) = 1` and
  `O^{2'}(O^{2'}(G)) = O^{2'}(G)`.

The key point for the involution statement (and for the oddness of the index) is that the image
of `x` in `G ⧸ N` has order dividing both `2` (if `x * x ∈ N`) and the odd number `N.index`,
hence is trivial.  Idempotency uses that `O^{2'}(G)` is invariant under every automorphism of
`G` (the defining family of normal subgroups of odd index is automorphism-invariant), hence
characteristic, so its image in `G` is normal.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.Reductions

/-- If `N ◁ G` has odd index and `x * x ∈ N`, then `x ∈ N`. -/
theorem mem_of_mul_self_mem_of_odd_index {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (hNn : N.Normal) (hodd : Odd N.index) {x : G} (hx : x * x ∈ N) : x ∈ N := by
  haveI := hNn
  have hmul : ((x * x : G) : G ⧸ N) = (x : G ⧸ N) * (x : G ⧸ N) := by
    simpa only [QuotientGroup.mk'_apply] using map_mul (QuotientGroup.mk' N) x x
  have hmk : (x : G ⧸ N) * (x : G ⧸ N) = 1 := by
    rw [← hmul]
    exact (QuotientGroup.eq_one_iff (x * x)).mpr hx
  have hdvd2 : orderOf (x : G ⧸ N) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hmk
  have hdvdi : orderOf (x : G ⧸ N) ∣ N.index := by
    have h := orderOf_dvd_natCard (x : G ⧸ N)
    rwa [← Subgroup.index_eq_card] at h
  have hone : orderOf (x : G ⧸ N) = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd2 with h | h
    · exact h
    · exfalso
      obtain ⟨m, hm⟩ := h ▸ hdvdi
      rcases hodd with ⟨k, hk⟩
      omega
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hone)

/-- The elements of `G` whose square lies in `O^{2'}(G)` lie in `O^{2'}(G)`: the square root
relation holds already modulo each normal subgroup of odd index, hence in their intersection. -/
theorem mem_oddResidual_of_mul_self_mem {G : Type} [Group G] [Finite G] {x : G}
    (hx : x * x ∈ oddResidual G) : x ∈ oddResidual G := by
  classical
  have hx' : x * x ∈ sInf {N : Subgroup G | N.Normal ∧ Odd N.index} := by
    simpa only [oddResidual] using hx
  rw [Subgroup.mem_sInf] at hx'
  rw [oddResidual, Subgroup.mem_sInf]
  intro N hN
  exact mem_of_mul_self_mem_of_odd_index hN.1 hN.2 (hx' N hN)

/-- `O^{2'}(G)`: normality, odd index, minimality, and containment of the involutions. -/
theorem oddResidual_basic {G : Type} [Group G] [Finite G] :
    (oddResidual G).Normal ∧ Odd (oddResidual G).index ∧
      (∀ N : Subgroup G, N.Normal → Odd N.index → oddResidual G ≤ N) ∧
      (∀ x : G, x * x = 1 → x ∈ oddResidual G) := by
  classical
  have hcomap : ∀ (e : G ≃* G) (N : Subgroup G), N ∈ {N : Subgroup G | N.Normal ∧ Odd N.index} →
      N.comap e.toMonoidHom ∈ {N : Subgroup G | N.Normal ∧ Odd N.index} := by
    intro e N hN
    refine ⟨hN.1.comap _, ?_⟩
    rw [Subgroup.index_comap_of_surjective N e.surjective]
    exact hN.2
  -- normality: every automorphism permutes the defining family
  have hnorm : (oddResidual G).Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [oddResidual] at hy ⊢
      rw [Subgroup.mem_sInf] at hy
      rw [Subgroup.mem_sInf]
      intro N hN
      exact Subgroup.mem_comap.mp (hy (N.comap (MulAut.conj g).toMonoidHom)
        (hcomap (MulAut.conj g) N hN))
    · have hle : (oddResidual G).map (MulAut.conj g⁻¹).toMonoidHom ≤ oddResidual G := by
        intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [oddResidual] at hy ⊢
        rw [Subgroup.mem_sInf] at hy
        rw [Subgroup.mem_sInf]
        intro N hN
        exact Subgroup.mem_comap.mp (hy (N.comap (MulAut.conj g⁻¹).toMonoidHom)
          (hcomap (MulAut.conj g⁻¹) N hN))
      intro x hx
      refine ⟨(MulAut.conj g⁻¹) x, hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), ?_⟩
      show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
      group
  -- odd index: the quotient has no involution
  have hodd : Odd (oddResidual G).index := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have h2 : 2 ∣ Nat.card (G ⧸ oddResidual G) := by
      rw [← Subgroup.index_eq_card]
      exact even_iff_two_dvd.mp heven
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (G := G ⧸ oddResidual G) h2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (oddResidual G) y
    have hpow : ((QuotientGroup.mk' (oddResidual G)) x) ^ 2 = 1 := by
      rw [← hy]
      exact pow_orderOf_eq_one _
    have hmm : (QuotientGroup.mk' (oddResidual G)) (x * x)
        = ((QuotientGroup.mk' (oddResidual G)) x) ^ 2 := by
      rw [map_mul, pow_two]
    have hx2 : x * x ∈ oddResidual G := by
      refine (QuotientGroup.eq_one_iff (x * x)).mp ?_
      rw [← QuotientGroup.mk'_apply, hmm, hpow]
    have hxL : x ∈ oddResidual G := mem_oddResidual_of_mul_self_mem hx2
    have hone : (QuotientGroup.mk' (oddResidual G)) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hxL
    rw [hone] at hy
    exact absurd hy (by norm_num)
  refine ⟨hnorm, hodd, ?_, ?_⟩
  · intro N hN hNo
    rw [oddResidual]
    exact sInf_le ⟨hN, hNo⟩
  · intro x hx
    exact mem_oddResidual_of_mul_self_mem (by rw [hx]; exact one_mem _)

/-- `O^{2'}(G)` is invariant under every automorphism of `G`: the defining family of normal
subgroups of odd index is permuted by automorphisms. -/
theorem map_mulEquiv_oddResidual {G : Type} [Group G] [Finite G] (e : G ≃* G) :
    (oddResidual G).map (e : G →* G) = oddResidual G := by
  have hcomap : ∀ (f : G ≃* G) (N : Subgroup G), N ∈ {N : Subgroup G | N.Normal ∧ Odd N.index} →
      N.comap f.toMonoidHom ∈ {N : Subgroup G | N.Normal ∧ Odd N.index} := by
    intro f N hN
    refine ⟨hN.1.comap _, ?_⟩
    rw [Subgroup.index_comap_of_surjective N f.surjective]
    exact hN.2
  have hle : (oddResidual G).map (e : G →* G) ≤ oddResidual G := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [oddResidual] at hy ⊢
    rw [Subgroup.mem_sInf] at hy
    rw [Subgroup.mem_sInf]
    intro N hN
    exact Subgroup.mem_comap.mp (hy (N.comap (e : G →* G)) (hcomap e N hN))
  have hle2 : (oddResidual G).map (e.symm : G →* G) ≤ oddResidual G := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [oddResidual] at hy ⊢
    rw [Subgroup.mem_sInf] at hy
    rw [Subgroup.mem_sInf]
    intro N hN
    exact Subgroup.mem_comap.mp (hy (N.comap (e.symm : G →* G)) (hcomap e.symm N hN))
  refine le_antisymm hle ?_
  intro x hx
  exact Subgroup.mem_map.mpr ⟨e.symm x, hle2 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), by simp⟩

/-- `O^{2'}(O^{2'}(G)) = O^{2'}(G)`: idempotency of `O^{2'}`. -/
theorem oddResidual_self_eq_top {G : Type} [Group G] [Finite G] :
    oddResidual ↥(oddResidual G) = ⊤ := by
  classical
  haveI hL : (oddResidual G).Normal := oddResidual_basic.1
  have hLodd : Odd (oddResidual G).index := oddResidual_basic.2.1
  -- `K = O^{2'}(↥O^{2'}(G))` is invariant under every automorphism of `↥O^{2'}(G)`, hence its
  -- image in `G` is normal in `G`
  have himg : ((oddResidual ↥(oddResidual G)).map (oddResidual G).subtype).Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    rw [Subgroup.map_map]
    have hcomp : ((MulAut.conj g : MulAut G) : G →* G).comp (oddResidual G).subtype
        = (oddResidual G).subtype.comp (MulAut.conjNormal (H := oddResidual G) g) := by
      ext x
      simp [MulAut.conjNormal_apply]
    rw [hcomp, ← Subgroup.map_map,
      map_mulEquiv_oddResidual (MulAut.conjNormal (H := oddResidual G) g)]
  have hle : (oddResidual ↥(oddResidual G)).map (oddResidual G).subtype ≤ oddResidual G := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hrel : ((oddResidual ↥(oddResidual G)).map (oddResidual G).subtype).relIndex
        (oddResidual G) = (oddResidual ↥(oddResidual G)).index := by
    show (((oddResidual ↥(oddResidual G)).map (oddResidual G).subtype).subgroupOf
        (oddResidual G)).index = _
    congr 1
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      rw [hyx'] at hy
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hodd' : Odd ((oddResidual ↥(oddResidual G)).map (oddResidual G).subtype).index := by
    have h1 := Subgroup.relIndex_mul_index hle
    rw [hrel] at h1
    rw [← h1]
    exact ((oddResidual_basic (G := ↥(oddResidual G))).2.1).mul hLodd
  have hle' : oddResidual G ≤ (oddResidual ↥(oddResidual G)).map (oddResidual G).subtype :=
    oddResidual_basic.2.2.1 _ himg hodd'
  refine le_antisymm le_top ?_
  intro x _
  have hx : (x : G) ∈ (oddResidual ↥(oddResidual G)).map (oddResidual G).subtype := hle' x.2
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  rw [hyx'] at hy
  exact hy

/-- If `O(G) = 1` then `O(O^{2'}(G)) = 1` and `O^{2'}(O^{2'}(G)) = O^{2'}(G)`. -/
theorem oddCore_oddResidual_basic {G : Type} [Group G] [Finite G]
    (h : oddCore G = ⊥) :
    oddCore ↥(oddResidual G) = ⊥ ∧ oddResidual ↥(oddResidual G) = ⊤ := by
  haveI : (oddResidual G).Normal := oddResidual_basic.1
  refine ⟨?_, oddResidual_self_eq_top⟩
  have h1 := Work.ThreePoints.map_oddCore_le_oddCore (G := G) (oddResidual G)
  rw [h] at h1
  have h2 : (oddCore ↥(oddResidual G)).map (oddResidual G).subtype = ⊥ := le_bot_iff.mp h1
  have h3 : oddCore ↥(oddResidual G) ≤ (oddResidual G).subtype.ker :=
    (Subgroup.map_eq_bot_iff _).mp h2
  rwa [Subgroup.ker_subtype, le_bot_iff] at h3

end Work.Reductions
