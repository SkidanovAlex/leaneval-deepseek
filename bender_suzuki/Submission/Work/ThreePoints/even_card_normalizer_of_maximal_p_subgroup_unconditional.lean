import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.three_involutions_even

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end
open LeanEval.GroupTheory.Defs

open scoped Pointwise

namespace Work.ThreePoints

open Submission.Blueprint

/-! ### The Brauer–Suzuki-free form of Ch. I §3 Prop. 1 -/

/-- **Peterfalvi I Ch. I §3 Prop. 1** (transitivity form), Brauer–Suzuki-free: if `Q` is maximal
among the `p`-subgroups of `G` with at least three fixed points of `Ω = G ⧸ K` and `N_G(Q)` is
transitive on `Ω_Q`, then some point stabiliser `N_H(Q)` (`H ∈ Ω_Q`) has even order.

This is `Work.ThreePoints.sec3_prop1_transitive` with its single use of the Brauer–Suzuki black box
(Case B, `¬ HasFourGroup M`) replaced by `Work.ThreePoints.three_involutions_even`. -/
theorem sec3_prop1_transitive_unconditional {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G} (hQp : IsPGroup p Q)
    (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup G, Q ≤ R → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q)
    (htrans : Work.DoubleTransitivity.IsTransitiveOnSub (Subgroup.normalizer (Q : Set G))
      (Submission.Blueprint.fixedPts K Q)) :
    ∃ ω ∈ Submission.Blueprint.fixedPts K Q,
      Even (Nat.card (MulAction.stabilizer G ω ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set M : Subgroup G := Subgroup.normalizer (Q : Set G) with hMdef
  have hMdef' : M = Subgroup.normalizer (Q : Set G) := hMdef
  have hQodd : Odd (Nat.card Q) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    haveI : Fintype ↥Q := Fintype.ofFinite ↥Q
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥Q) 2
      (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hev)
    obtain ⟨n, hn⟩ := hQp x
    have hxG : orderOf ((x : Q) : G) = 2 := (Subgroup.orderOf_coe x).trans hx
    have h2dvd : 2 ∣ p ^ n := by
      rw [← hxG]
      exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg (fun y : Q => (y : G)) hn)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  by_cases hA4 : Submission.Blueprint.HasFourGroup M
  · -- Case A: `N_G(Q)` has `2`-rank `≥ 2`
    obtain ⟨t, ht2⟩ : ∃ t : M, orderOf t = 2 := by
      obtain ⟨t, -, ht2, -, -, -⟩ := hA4
      exact ⟨t, ht2⟩
    have htG : orderOf ((t : G)) = 2 := (Subgroup.orderOf_coe t).trans ht2
    obtain ⟨ω, hωfix, -⟩ := existsUnique_fixedPts_of_orderOf_eq_two hK htG
    have hle : Q ≤ MulAction.stabilizer G ω :=
      le_stabilizer_of_involution_mem_normalizer hK hQodd hA4 ⟨t.2, htG⟩ hωfix
    refine ⟨ω, mem_fixedPts_iff_le_stabilizer.mpr hle, ?_⟩
    have hmem : (t : G) ∈ (MulAction.stabilizer G ω ⊓ M : Subgroup G) :=
      ⟨MulAction.mem_stabilizer_iff.mpr hωfix, t.2⟩
    refine even_iff_two_dvd.mpr ?_
    have hord : orderOf (⟨(t : G), hmem⟩ :
        ↥(MulAction.stabilizer G ω ⊓ M : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact htG
    have h2dvd : 2 ∣ orderOf (⟨(t : G), hmem⟩ :
        ↥(MulAction.stabilizer G ω ⊓ M : Subgroup G)) := by
      rw [hord]
    exact dvd_trans h2dvd (orderOf_dvd_natCard
      (⟨(t : G), hmem⟩ : ↥(MulAction.stabilizer G ω ⊓ M : Subgroup G)))
  · -- Case B: `N_G(Q)` has `2`-rank `1`
    have hB : ¬ Submission.Blueprint.HasFourGroup M := hA4
    have hne : (Submission.Blueprint.fixedPts K Q).Nonempty := by
      rw [← Set.ncard_pos]; omega
    obtain ⟨ω₀, hω₀⟩ := hne
    obtain ⟨ω₁, hω₁, hω₁ne⟩ :=
      Set.exists_ne_of_one_lt_ncard (by omega : 1 < (Submission.Blueprint.fixedPts K Q).ncard) ω₀
    have h2s : 2 ≤ ((Submission.Blueprint.fixedPts K Q) \ {ω₀}).ncard := by
      have h1 := Set.ncard_sdiff_singleton_add_one hω₀
      omega
    obtain ⟨ω₂, hω₂, hω₂ne⟩ := Set.exists_ne_of_one_lt_ncard
      (by omega : 1 < ((Submission.Blueprint.fixedPts K Q) \ {ω₀}).ncard) ω₁
    have hω₂mem : ω₂ ∈ Submission.Blueprint.fixedPts K Q := hω₂.1
    have hω₂ne₀ : ω₂ ≠ ω₀ := hω₂.2
    -- the three involutions
    obtain ⟨t₁, ht₁M, ht₁2, ht₁⟩ :=
      sec3_lemma3 hK hp hQp hQmax hω₀ hω₁ hω₁ne.symm (htrans ω₀ hω₀ ω₁ hω₁)
    obtain ⟨t₂, ht₂M, ht₂2, ht₂⟩ :=
      sec3_lemma3 hK hp hQp hQmax hω₀ hω₂mem hω₂ne₀.symm (htrans ω₀ hω₀ ω₂ hω₂mem)
    have ht₁M' : t₁ ∈ M := by rw [hMdef']; exact ht₁M
    have ht₂M' : t₂ ∈ M := by rw [hMdef']; exact ht₂M
    have hprodM : t₁ * t₂ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).mul_mem ht₁M ht₂M
    have hω' : (t₁ * t₂) • ω₀ ∈ Submission.Blueprint.fixedPts K Q :=
      Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hprodM hω₀
    have ht₁sq : t₁ * t₁ = 1 := mul_self_eq_one_of_orderOf_eq_two ht₁2
    have ht₂sq : t₂ * t₂ = 1 := mul_self_eq_one_of_orderOf_eq_two ht₂2
    have hne' : ω₀ ≠ (t₁ * t₂) • ω₀ := by
      intro hcon
      have h1 : t₁ • ((t₁ * t₂) • ω₀) = ω₂ := by
        rw [mul_smul, ← mul_smul, ht₁sq, one_smul, ht₂]
      have h2 : t₁ • ω₀ = t₁ • ((t₁ * t₂) • ω₀) := congrArg (fun y => t₁ • y) hcon
      exact hω₂ne (ht₁.symm.trans (h2.trans h1)).symm
    obtain ⟨t, htM, ht2, ht⟩ := sec3_lemma3 hK hp hQp hQmax hω₀ hω'
      hne' ⟨t₁ * t₂, hprodM, rfl⟩
    have htM' : t ∈ M := by rw [hMdef']; exact htM
    have hxmem : t₂ * t₁ * t ∈ M := M.mul_mem (M.mul_mem ht₂M' ht₁M') htM'
    have htsq : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht2
    have hxfix : (t₂ * t₁ * t) • ω₀ = ω₀ := by
      rw [mul_smul, mul_smul, ht, mul_smul]
      have h1 : t₁ • (t₁ • (t₂ • ω₀)) = t₂ • ω₀ := by
        rw [← mul_smul, ht₁sq, one_smul]
      rw [h1, ← mul_smul, ht₂sq, one_smul]
    refine ⟨ω₀, hω₀, ?_⟩
    refine even_iff_two_dvd.mpr ?_
    have hmem : (t₂ * t₁ * t) ∈ (MulAction.stabilizer G ω₀ ⊓ M : Subgroup G) :=
      ⟨MulAction.mem_stabilizer_iff.mpr hxfix, hxmem⟩
    -- work inside `M`
    set t₁' : M := ⟨t₁, ht₁M'⟩
    set t₂' : M := ⟨t₂, ht₂M'⟩
    set t' : M := ⟨t, htM'⟩
    have ht₁2' : orderOf t₁' = 2 := by rw [← Subgroup.orderOf_coe t₁']; exact ht₁2
    have ht₂2' : orderOf t₂' = 2 := by rw [← Subgroup.orderOf_coe t₂']; exact ht₂2
    have ht2' : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe t']; exact ht2
    have htsq' : t' * t' = 1 := mul_self_eq_one_of_orderOf_eq_two ht2'
    have hne₂₁ : t₂' ≠ t₁' := by
      intro heq
      refine hne' ?_
      have hw : (t₁' * t₂' : M) = 1 := by rw [heq, mul_self_eq_one_of_orderOf_eq_two ht₁2']
      have hcoe : ((t₁' * t₂' : M) : G) = t₁ * t₂ := rfl
      rw [hw] at hcoe
      rw [← hcoe]
      simp
    have hxeven : Even (orderOf (t₂' * t₁' * t')) :=
      three_involutions_even hB ht₂2' ht₁2' ht2' hne₂₁
    have hxevenG : Even (orderOf (t₂ * t₁ * t)) := by
      have hcoee : (((t₂' * t₁' * t') : M) : G) = t₂ * t₁ * t := rfl
      rw [← hcoee, Subgroup.orderOf_coe]
      exact hxeven
    refine dvd_trans (even_iff_two_dvd.mp hxevenG) ?_
    have hord : orderOf (⟨t₂ * t₁ * t, hmem⟩ :
        ↥(MulAction.stabilizer G ω₀ ⊓ M : Subgroup G)) = orderOf (t₂ * t₁ * t) :=
      Subgroup.orderOf_mk _ _
    rw [← hord]
    exact orderOf_dvd_natCard _

/-- **Peterfalvi I Ch. I §4 Prop. 2** (p. 156), unconditional form: `F` is a finite group of
`2`-rank `≥ 2` (`HasFourGroup F`), `K ≤ F` is a strongly embedded subgroup (so `F` acts on
`Ω = F ⧸ K`), `p ≠ 2` is a prime, and `Q ≤ K` is a `p`-subgroup maximal among the `p`-subgroups of
`K` with at least three fixed points of `Ω`.  Then `|N_K(Q)|` is even.

This is the input consumed by Ch. II §4 Prop. 1(a) (p. 168) inside `F₁ = C_G(O^p(X))·P`, where
`K = F₁ ⊓ M`, `F = F₁` and `Ω` is the class `Ξ` of proper Bender groups of `F₁`.

**This is `Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup` with the Brauer–Suzuki
hypothesis removed.**  The helper lemma `Work.ThreePoints.sec3_prop1_transitive_unconditional`
above is the same adapted form of `Work.ThreePoints.sec3_prop1_transitive`. -/
theorem even_card_normalizer_of_maximal_p_subgroup_unconditional {F : Type} [Group F] [Finite F]
    (hA : Submission.Blueprint.ThmAProp)
    (hfour : Submission.Blueprint.HasFourGroup F) {K : Subgroup F}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F} (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) :
    Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  classical
  haveI : Fintype (F ⧸ K) := Fintype.ofFinite _
  set M : Subgroup F := Subgroup.normalizer (Q : Set F) with hMdef
  have hstab : MulAction.stabilizer F (((1 : F)) : F ⧸ K) = K := by
    rw [Work.ThreePoints.stabilizer_mk K 1, conj_one]
  have h2tr : MulAction.IsMultiplyPretransitive F (F ⧸ K) 2 := hA F hfour K hK
  -- App. II (6): maximality in `F` and transitivity of `N_F(Q)` on `Ω_Q`
  obtain ⟨hQmaxF, htransF⟩ := app2_6_general (X := F) (E := F ⧸ K) (p := p) hp h2tr
    (P := Q) hQp (by rw [hstab]; exact hQK) hQ3
    (fun R hRg hRa hR3 hQR => by
      have hRK : R ≤ K := by rw [← hstab]; exact hRa
      rw [hQmax R hQR hRK hRg hR3])
  -- Ch. I §3 Prop. 1
  obtain ⟨ω, hω, heven⟩ := sec3_prop1_transitive_unconditional hK hp hp2 hQp hQ3
    (fun R hQR hRg hR3 => hQmaxF R hQR hRg hR3) htransF
  have hωK : (((1 : F)) : F ⧸ K) ∈ Submission.Blueprint.fixedPts K Q := by
    rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, hstab]
    exact hQK
  obtain ⟨n, hnM, hn⟩ := htransF (((1 : F)) : F ⧸ K) hωK ω hω
  -- all point stabilisers of `N_F(Q)` on `Ω_Q` have the same order
  have hcard_eq : Nat.card (MulAction.stabilizer F ω ⊓ M : Subgroup F) =
      Nat.card (MulAction.stabilizer F (((1 : F)) : F ⧸ K) ⊓ M : Subgroup F) := by
    have hnM' : n ∈ M := hnM
    have hMconj : conj n M = M := by
      have hstep : ∀ u ∈ M, conj u M ≤ M := by
        intro u hu m hm
        rw [mem_conj_iff] at hm
        have h := M.mul_mem (M.mul_mem hu hm) (M.inv_mem hu)
        rwa [show u * (u⁻¹ * m * u) * u⁻¹ = m from by group] at h
      refine le_antisymm (hstep n hnM') ?_
      calc M = conj n (conj n⁻¹ M) := by rw [← conj_mul, mul_inv_cancel, conj_one]
        _ ≤ conj n M := Subgroup.map_mono (hstep n⁻¹ (M.inv_mem hnM'))
    have h1 : MulAction.stabilizer F ω =
        conj n (MulAction.stabilizer F (((1 : F)) : F ⧸ K)) := by
      rw [← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj n (((1 : F)) : F ⧸ K), hn]
    have key2 : MulAction.stabilizer F ω ⊓ M =
        conj n (MulAction.stabilizer F (((1 : F)) : F ⧸ K) ⊓ M) := by
      rw [conj_inf, ← h1, hMconj]
    rw [key2]
    exact Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hevenK : Even (Nat.card (K ⊓ M : Subgroup F)) := by
    rw [← hstab, ← hcard_eq]
    exact heven
  -- `N_K(Q)` is isomorphic to its image in `F`, which is `K ⊓ N_F(Q)`
  have hmap : (Subgroup.normalizer (Q.subgroupOf K : Set K)).map K.subtype = K ⊓ M := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [hMdef, Subgroup.mem_normalizer_iff_map_conj_eq]
      have hy' : (Q.subgroupOf K).map (MulAut.conj y).toMonoidHom = Q.subgroupOf K :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
      calc Q.map (MulAut.conj (y : F)).toMonoidHom
          = ((Q.subgroupOf K).map K.subtype).map (MulAut.conj (y : F)).toMonoidHom := by
            conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hQK]
        _ = (Q.subgroupOf K).map ((MulAut.conj (y : F)).toMonoidHom.comp K.subtype) := by
            rw [Subgroup.map_map]
        _ = (Q.subgroupOf K).map (K.subtype.comp (MulAut.conj y).toMonoidHom) := by
            rw [show (MulAut.conj (y : F)).toMonoidHom.comp K.subtype =
              K.subtype.comp (MulAut.conj y).toMonoidHom from by
                ext z
                simp [MulAut.conj_apply]]
        _ = ((Q.subgroupOf K).map (MulAut.conj y).toMonoidHom).map K.subtype := by
            rw [Subgroup.map_map]
        _ = (Q.subgroupOf K).map K.subtype := by rw [hy']
        _ = Q := Subgroup.map_subgroupOf_eq_of_le hQK
    · rintro ⟨hxK, hxN⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyQ : (y : F) ∈ Q := Subgroup.mem_subgroupOf.mp hy
        have h1 : x * (y : F) * x⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hxN) (y : F) |>.mp hyQ
        rw [Subgroup.mem_subgroupOf]
        simpa using h1
      · intro hy
        have hyQ : x * (y : F) * x⁻¹ ∈ Q := by
          have h := Subgroup.mem_subgroupOf.mp hy
          simpa using h
        have hxi : x⁻¹ ∈ Subgroup.normalizer (Q : Set F) :=
          (Subgroup.normalizer (Q : Set F)).inv_mem hxN
        have h1 : x⁻¹ * (x * (y : F) * x⁻¹) * x⁻¹⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hxi) (x * (y : F) * x⁻¹) |>.mp hyQ
        have h2 : x⁻¹ * (x * (y : F) * x⁻¹) * x⁻¹⁻¹ = (y : F) := by group
        rw [h2] at h1
        exact Subgroup.mem_subgroupOf.mpr h1
  have hcardfin : Nat.card ↥(Subgroup.normalizer (Q.subgroupOf K : Set K)) =
      Nat.card ↥(K ⊓ M : Subgroup F) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (f := K.subtype) Subtype.coe_injective).symm
  rw [hcardfin]
  exact hevenK

end Work.ThreePoints
