/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Comparison of the number of index-`ℓ` subgroups with a finite index subgroup

For additive commutative groups `V ≤ G` with `V` of finite index in `G` and a prime `ℓ`, the
number of index-`ℓ` subgroups of `V` is at most the number of index-`ℓ` subgroups of `G`.

The proof is a strong induction on the index `[G : V]`, reducing to the "prime step"
`NK.LocalCFT.Units.EllRank.natCard_projectivization_ellDual_le_of_relIndex_prime`.
-/
import Submission.NK.LocalCFT.Units.EllRank.Defs
import Submission.NK.LocalCFT.Units.EllRank.natCard_projectivization_ellDual_le_of_relIndex_prime
import Submission.NK.LocalCFT.Units.EllRank.nIdx_eq_natCard_projectivization
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped LinearAlgebra.Projectivization

set_option linter.style.haveILetI false

namespace NK.LocalCFT.Units.EllRank

noncomputable section

/-- **Invariance of the index count under additive isomorphisms.** -/
theorem nIdx_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (n : ℕ) :
    nIdx n A = nIdx n B := by
  refine Nat.card_congr (Equiv.subtypeEquiv ?_ ?_)
  · refine ⟨fun H => H.map e.toAddMonoidHom, fun K => K.comap e.toAddMonoidHom, ?_, ?_⟩
    · intro H
      ext x
      simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [e.injective hyx] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    · intro K
      ext x
      simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [← hyx]
      · intro hx
        exact ⟨e.symm x, by simpa using hx, by simp⟩
  · intro H
    show H.index = n ↔ (H.map (e : A →+ B)).index = n
    rw [AddSubgroup.index_map_equiv H e]

section Prime

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Invariance of the projective count under additive isomorphisms of the ambient group.** -/
theorem projCard_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    Nat.card (ℙ (ZMod ℓ) (ellDual ℓ A)) = Nat.card (ℙ (ZMod ℓ) (ellDual ℓ B)) := by
  rw [← nIdx_eq_natCard_projectivization (ℓ := ℓ) A,
    nIdx_congr e ℓ, nIdx_eq_natCard_projectivization (ℓ := ℓ) B]

/-- Passing from `V` to `V.addSubgroupOf W` for `V ≤ W` does not change the projective count. -/
theorem projCard_addSubgroupOf_eq {G : Type*} [AddCommGroup G] {V W : AddSubgroup G}
    (hVW : V ≤ W) :
    Nat.card (ℙ (ZMod ℓ) (ellDual ℓ ↥(V.addSubgroupOf W))) =
      Nat.card (ℙ (ZMod ℓ) (ellDual ℓ ↥V)) :=
  projCard_congr (AddSubgroup.addSubgroupOfEquivOfLe hVW)

/-- The prime step, restated so that it can be used inside the induction below. -/
theorem prime_step {G : Type*} [AddCommGroup G] (V W : AddSubgroup G) (hVW : V ≤ W)
    {p : ℕ} [Fact p.Prime] (h : V.relIndex W = p) :
    Nat.card (ℙ (ZMod ℓ) (ellDual ℓ ↥V)) ≤ Nat.card (ℙ (ZMod ℓ) (ellDual ℓ ↥W)) :=
  natCard_projectivization_ellDual_le_of_relIndex_prime V W hVW h

/-- If `V ≤ W` and `[W : V] = 1` then `V = W`. -/
theorem eq_of_relIndex_eq_one {G : Type*} [AddGroup G] {V W : AddSubgroup G} (hVW : V ≤ W)
    (h : V.relIndex W = 1) : V = W := by
  have h1 : V.addSubgroupOf W = ⊤ := by
    rw [show V.relIndex W = (V.addSubgroupOf W).index from rfl] at h
    exact AddSubgroup.index_eq_one.mp h
  have h2 : W ≤ V := AddSubgroup.addSubgroupOf_eq_top.mp h1
  exact le_antisymm hVW h2

/-- **The comparison, relative form.**  For `V ≤ W` additive subgroups of an abelian group with
`[W : V] ≠ 0`, the number of index-`ℓ` subgroups of `V` is at most that of `W`. -/
theorem natCard_projectivization_ellDual_le_of_relIndex_ne_zero :
    ∀ (n : ℕ), n ≠ 0 → ∀ {G : Type*} [AddCommGroup G] (V W : AddSubgroup G),
      V ≤ W → V.relIndex W = n →
      Nat.card (ℙ (ZMod ℓ) (ellDual ℓ ↥V)) ≤ Nat.card (ℙ (ZMod ℓ) (ellDual ℓ ↥W)) := by
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro hn G _ V W hVW hrel
  by_cases hVW' : V = W
  · subst hVW'
    exact le_rfl
  · by_cases hpr : n.Prime
    · haveI : Fact n.Prime := ⟨hpr⟩
      exact prime_step V W hVW hrel
    · -- composite index: find a proper intermediate subgroup
      have hn1 : n ≠ 1 := fun h1 => hVW' (eq_of_relIndex_eq_one hVW (h1 ▸ hrel))
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
      haveI : Fact p.Prime := ⟨hp⟩
      have hpn : p ≠ n := fun h1 => hpr (h1 ▸ hp)
      have hp_lt_n : p < n :=
        lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpdvd) hpn
      have hfker : (QuotientAddGroup.mk' V).ker = V := QuotientAddGroup.ker_mk' V
      -- the image of `W` in `G ⧸ V`
      have hQcard : Nat.card ↥(W.map (QuotientAddGroup.mk' V)) = n := by
        have h := AddSubgroup.relIndex_ker W (QuotientAddGroup.mk' V)
        rw [hfker, hrel] at h
        exact h.symm
      haveI : Finite ↥(W.map (QuotientAddGroup.mk' V)) :=
        Nat.finite_of_card_ne_zero (by rw [hQcard]; exact hn)
      haveI : Fintype ↥(W.map (QuotientAddGroup.mk' V)) := Fintype.ofFinite _
      obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card (G := ↥(W.map (QuotientAddGroup.mk' V))) p
        (by rw [← Nat.card_eq_fintype_card, hQcard]; exact hpdvd)
      -- the cyclic subgroup generated by `x`
      set Q₁ : AddSubgroup (G ⧸ V) := AddSubgroup.zmultiples (x : G ⧸ V) with hQ₁
      have hQ₁card : Nat.card ↥Q₁ = p := by
        rw [hQ₁, Nat.card_zmultiples, AddSubgroup.addOrderOf_coe x, hx]
      have hQ₁le : Q₁ ≤ W.map (QuotientAddGroup.mk' V) := by
        rw [hQ₁]
        exact AddSubgroup.zmultiples_le.mpr x.2
      -- the intermediate subgroup
      set V₁ : AddSubgroup G := AddSubgroup.comap (QuotientAddGroup.mk' V) Q₁ with hV₁
      have hV_V₁ : V ≤ V₁ := by
        intro v hv
        rw [hV₁, AddSubgroup.mem_comap]
        have : (QuotientAddGroup.mk' V) v = 0 := (QuotientAddGroup.eq_zero_iff v).mpr hv
        rw [show ⇑(QuotientAddGroup.mk' V) v = QuotientAddGroup.mk' V v from rfl, this]
        exact Q₁.zero_mem
      have hV₁_W : V₁ ≤ W := by
        intro v hv
        rw [hV₁, AddSubgroup.mem_comap] at hv
        have h2 : v ∈ AddSubgroup.comap (QuotientAddGroup.mk' V)
            (W.map (QuotientAddGroup.mk' V)) := hQ₁le hv
        rw [AddSubgroup.comap_map_eq, hfker] at h2
        rw [sup_eq_left.mpr hVW] at h2
        exact h2
      have hrel_V : V.relIndex V₁ = p := by
        have h := AddSubgroup.relIndex_ker V₁ (QuotientAddGroup.mk' V)
        rw [← hfker, h]
        rw [hV₁, AddSubgroup.map_comap_eq_self (f := QuotientAddGroup.mk' V) (H := Q₁) (by
          rw [AddMonoidHom.range_eq_top.mpr (QuotientAddGroup.mk'_surjective V)]
          exact le_top)]
        exact hQ₁card
      have hrel_V₁ : V₁.relIndex W = n / p := by
        have h := AddSubgroup.relIndex_mul_relIndex V V₁ W hV_V₁ hV₁_W
        rw [hrel_V, hrel] at h
        exact Nat.eq_div_of_mul_eq_right hp.ne_zero h
      have ih1 := ih p hp_lt_n hp.ne_zero V V₁ hV_V₁ hrel_V
      have ih2 := ih (n / p) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt)
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpdvd) hp.pos).ne' V₁ W hV₁_W hrel_V₁
      exact le_trans ih1 ih2

/-- **The comparison, absolute form.**  For a finite index additive subgroup `V` of an abelian
group `G` and a prime `ℓ`, the number of index-`ℓ` subgroups of `V` is at most the number of
index-`ℓ` subgroups of `G`. -/
theorem natCard_projectivization_ellDual_le_of_finiteIndex {G : Type*} [AddCommGroup G]
    (V : AddSubgroup G) (hV : V.FiniteIndex) :
    Nat.card (ℙ (ZMod ℓ) (ellDual ℓ ↥V)) ≤ Nat.card (ℙ (ZMod ℓ) (ellDual ℓ G)) := by
  have hmain := natCard_projectivization_ellDual_le_of_relIndex_ne_zero (ℓ := ℓ) V.index
    hV.index_ne_zero V ⊤ le_top (by rw [AddSubgroup.relIndex_top_right])
  -- `↥(⊤ : AddSubgroup G)` may be replaced by `G`
  have htop : Nat.card (ℙ (ZMod ℓ) (ellDual ℓ ↥(⊤ : AddSubgroup G))) =
      Nat.card (ℙ (ZMod ℓ) (ellDual ℓ G)) := by
    have e : ↥(⊤ : AddSubgroup G) ≃+ G := AddSubgroup.topEquiv
    rw [← nIdx_eq_natCard_projectivization (ℓ := ℓ) ↥(⊤ : AddSubgroup G),
      nIdx_congr e ℓ, nIdx_eq_natCard_projectivization (ℓ := ℓ) G]
  rwa [htop] at hmain

end Prime

end

end NK.LocalCFT.Units.EllRank
