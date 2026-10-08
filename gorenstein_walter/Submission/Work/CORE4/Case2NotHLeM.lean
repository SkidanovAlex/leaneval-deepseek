import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.DihOrCycSub
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# CORE4 — Bender §4: `H ⊄ M` for the maximal subgroup `M` of Theorem 2.10 (2)

Bender 1981, §4 (p. 224) begins: *"In this final section we study a maximal subgroup `M` as
described in Theorem 2.10, and show that it is `too big`. By Theorem 2.6, `H ⊄ M`."*

Theorem 2.6 (`Work.GW2.Thm26Prop`) is stated for an arbitrary `B : BenderSetup G`, i.e. for an
arbitrary maximal subgroup `Hhat` containing `H = C_G(t)`.  Applying it to the maximal subgroup
`M` of the second case of Theorem 2.10 (a coatom with `t ∈ E(M)` and `N_G(X) ≤ M` for some
`1 ≠ X ≤ F(U)`), it says that either

* `M = H` (the first alternative of Theorem 2.6), or
* `O₂(M)` is a four-group, `U = O(M)` and `|M : O₂(M)O(M)| = 6` (the second alternative).

In the first case `M = C_G(t)`, so `E(M) ≤ M` centralizes `t`, and `t ∈ E(M)` — but the centre of a
quasisimple group has odd order (`LayerProp`), so this is impossible.  In the second case `M` is an
extension of the solvable group `O₂(M)O(M)` by a group of order `6`, hence solvable, so `E(M) = 1`
— contradicting `t ∈ E(M) ≠ 1`.  So `H ⊄ M` in both cases.
-/

namespace Work.CORE4

open Subgroup

set_option maxHeartbeats 1000000

/-! ## Auxiliary general facts -/

/-- A finite subgroup has odd order if and only if it is a `{2}ᶜ`-subgroup. -/
private theorem odd_iff_isPiSubgroup_ne_two {G : Type*} [Group G] [Finite G] (N : Subgroup G) :
    Odd (Nat.card N) ↔ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N := by
  unfold Subgroup.IsPiSubgroup
  have hne : Nat.card ↥N ≠ 0 := (Nat.card_pos (α := ↥N)).ne'
  constructor
  · intro hodd q hq hq2
    rw [hq2] at hq
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (Nat.mem_primeFactors.mp hq).2.1)
  · intro h
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact h 2 (Nat.mem_primeFactors.mpr
      ⟨by norm_num, even_iff_two_dvd.mp heven, hne⟩) rfl

/-- `O(G) = O_{2'}(G)` has odd order (compared with the odd-order library's `O_{2'}(G)`). -/
private theorem odd_oddCore (H : Type) [Group H] [Finite H] :
    Odd (Nat.card (Work.GW2.oddCore H)) := by
  have hle : Work.GW2.oddCore H ≤ OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) H := by
    rw [Work.GW2.oddCore]
    refine le_trans (Subgroup.normalCore_le _) (sSup_le ?_)
    intro N hN
    exact @OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore H _ ({q : ℕ | q ≠ 2}) N hN.1
      ((odd_iff_isPiSubgroup_ne_two N).mp hN.2)
  exact Odd.of_dvd_nat
    ((odd_iff_isPiSubgroup_ne_two _).mpr
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup ({q : ℕ | q ≠ 2})))
    (Subgroup.card_dvd_of_le hle)

/-- The relative odd core `O(K)` carried into `G` has odd order. -/
private theorem oddCoreIn_odd' {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    Odd (Nat.card ↥(Work.GW2.oddCoreIn K)) := by
  have h : Nat.card ↥(Work.GW2.oddCoreIn K) = Nat.card ↥(Work.GW2.oddCore ↥K) := by
    rw [Work.GW2.oddCoreIn]
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective K)
  rw [h]
  exact odd_oddCore ↥K

/-- The layer of a solvable group is trivial. -/
private theorem layer_eq_bot_of_solvable {X : Type} [Group X] (h : Group.IsSolvable X) :
    Work.GW2.layer X = ⊥ := by
  haveI := h
  rw [Work.GW2.layer, sSup_eq_bot]
  intro E hE
  by_contra hne
  have hlt : ⁅E, E⁆ < E := Group.IsSolvable.commutator_lt_of_ne_bot hne
  rw [hE.2.1] at hlt
  exact absurd hlt (lt_irrefl E)

/-- If `↥K` is solvable then `E(K) = 1`. -/
private theorem layerIn_eq_bot_of_solvable {G : Type} [Group G] {K : Subgroup G}
    (h : Group.IsSolvable ↥K) : Work.GW2.layerIn K = ⊥ := by
  rw [Work.GW2.layerIn, layer_eq_bot_of_solvable h, Subgroup.map_bot]

/-- Every finite group of order `6` is solvable. -/
private theorem solvable_of_card_six {X : Type} [Group X] [Finite X] (h : Nat.card X = 6) :
    Group.IsSolvable X := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : 3 ∣ Nat.card X := by rw [h]; norm_num
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hPcard : Nat.card ↥(Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb]
  have hPindex : (Subgroup.zpowers b).index = 2 := by
    have hh := Subgroup.index_mul_card (Subgroup.zpowers b)
    rw [hPcard, h] at hh
    omega
  haveI : (Subgroup.zpowers b).Normal := Subgroup.normal_of_index_eq_two hPindex
  haveI hP3 : IsPGroup 3 ↥(Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  haveI : Group.IsNilpotent ↥(Subgroup.zpowers b) := hP3.isNilpotent
  haveI hQ2 : IsPGroup 2 (X ⧸ Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [← Subgroup.index_eq_card, hPindex]; norm_num)
  haveI : Group.IsNilpotent (X ⧸ Subgroup.zpowers b) := hQ2.isNilpotent
  exact Group.isSolvable_of_subgroup_quotient (Subgroup.zpowers b)

/-- **Quasisimple centre crüx.**  An involution lying in the centre of a quasisimple group is
impossible, because that centre has odd order. -/
private theorem false_of_quasisimple_involution {X : Type} [Group X] (E : Subgroup X)
    (hE : Work.GW2.IsQuasisimple E) (hodd : Odd (Nat.card ↥(Subgroup.center ↥E)))
    {t : X} (htE : t ∈ E) (ht2 : orderOf t = 2) (hcen : ∀ x ∈ E, x * t = t * x) : False := by
  have hcenter : (⟨t, htE⟩ : ↥E) ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hcen (y : X) y.2
  have hdvd : orderOf (⟨t, htE⟩ : ↥E) ∣ Nat.card ↥(Subgroup.center ↥E) :=
    Subgroup.orderOf_dvd_natCard _ hcenter
  have hord : orderOf (⟨t, htE⟩ : ↥E) = 2 := by
    have h1 : orderOf ((⟨t, htE⟩ : ↥E) : X) = orderOf (⟨t, htE⟩ : ↥E) :=
      Subgroup.orderOf_coe _
    rw [show ((⟨t, htE⟩ : ↥E) : X) = t from rfl, ht2] at h1
    exact h1.symm
  rw [hord] at hdvd
  exact Odd.not_two_dvd_nat hodd hdvd

/-! ## The layer of `M` -/

/-- **§4, p. 224.**  If `t ∈ E(M)` for a coatom `M` of a minimal counterexample, then `E(M)` is
the (unique) quasisimple normal subgroup of `M`, its centre has odd order, and `t` lifts into it. -/
private theorem layer_facts (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} {M : Subgroup G}
    (hcoat : IsCoatom M) (ht : B.t ∈ Work.GW2.layerIn M) :
    Work.GW2.IsQuasisimple (Work.GW2.layer ↥M) ∧ (Work.GW2.layer ↥M).Normal ∧
      Odd (Nat.card ↥(Subgroup.center ↥(Work.GW2.layer ↥M))) ∧
      ∃ e ∈ Work.GW2.layer ↥M, ((e : ↥M) : G) = B.t := by
  have ht1 : B.t ≠ 1 := by
    intro h1
    have ht2 := B.t_order
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  -- the layer of `M` is nontrivial
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    have hbot' : Work.GW2.layerIn M = ⊥ := by
      rw [Work.GW2.layerIn, hbot, Subgroup.map_bot]
    exact ht1 (Subgroup.mem_bot.mp (hbot' ▸ ht))
  -- so `M` has a normal quasisimple subgroup
  obtain ⟨E', hE'norm, hE'q⟩ : ∃ E' : Subgroup ↥M, E'.Normal ∧ Work.GW2.IsQuasisimple E' := by
    by_contra hcon
    apply hlayer_ne
    rw [Work.GW2.layer, sSup_eq_bot]
    intro F hF
    by_contra hFne
    exact hcon ⟨F, hF.1, hF.2⟩
  -- `M` is a proper subgroup of `G`, hence a D-group
  have hD : Work.GW2.DihOrCycSylow ↥M := DihOrCycSub hbc.sylow M
  have hcard : Nat.card ↥M < Nat.card G := by
    have hlt : M < ⊤ := hcoat.lt_top
    have hh := Subgroup.card_lt_of_lt hlt
    rwa [Subgroup.card_top] at hh
  have hIsD : Work.GW2.IsDGroup ↥M := hbc.ih ↥M hcard hD
  -- Bender 1.6 / `LayerProp`
  obtain ⟨hlayerEq, hodd, -⟩ := I.toolkit.lay ↥M I.toolkit.ft hD hIsD E' hE'norm hE'q
  refine ⟨hlayerEq.symm ▸ hE'q, hlayerEq.symm ▸ hE'norm, ?_, ?_⟩
  · rw [hlayerEq]; exact hodd
  · have ht' : B.t ∈ (Work.GW2.layer ↥M).map (Subgroup.subtype M) := ht
    obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp ht'
    exact ⟨e, he, heq⟩

/-! ## The second alternative of Theorem 2.6 for `M`: `M` is solvable -/

/-- **Theorem 2.6, second alternative.**  If `O₂(M)` is a four-group, `O(M) = U` and
`|M : O₂(M)·O(M)| = 6`, then `M` is solvable: it is the extension of the solvable group
`O₂(M)·O(M)` (a four-group times an odd-order group) by the group `M/O₂(M)O(M)` of order `6`. -/
private theorem solvable_of_case2 {G : Type} [Group G] [Finite G] (I : Work.GW2.C4Inputs)
    (B : Work.GW2.BenderSetup G) {M : Subgroup G}
    (hU : Work.GW2.oddCoreIn M = B.U)
    (hfour : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 M))
    (hrel : (Work.GW2.pCoreIn 2 M ⊔ B.U).relIndex M = 6) :
    Group.IsSolvable ↥M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the two pieces `P' = O₂(M)`, `Q' = O(M)` and their join, all inside `↥M`
  set P' : Subgroup ↥M := Work.GW2.pCore 2 ↥M with hP'def
  set Q' : Subgroup ↥M := Work.GW2.oddCore ↥M with hQ'def
  have hP'card : Nat.card ↥P' = 4 := by
    have h : Nat.card ↥(P'.map (Subgroup.subtype M)) = Nat.card ↥P' :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective M)
    rw [← h, hP'def]
    exact hfour.1
  have hQ'odd : Odd (Nat.card ↥Q') := by
    have h : Nat.card ↥(Work.GW2.oddCoreIn M) = Nat.card ↥Q' := by
      rw [Work.GW2.oddCoreIn, hQ'def]
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective M)
    rw [← h]
    exact oddCoreIn_odd' M
  -- the index of `P' ⊔ Q'` in `↥M` is `6`
  have hPleM : Work.GW2.pCoreIn 2 M ≤ M := by
    rw [show Work.GW2.pCoreIn 2 M = P'.map (Subgroup.subtype M) from rfl]
    exact Subgroup.map_subtype_le _
  have hQleM : B.U ≤ M := by
    rw [← hU, Work.GW2.oddCoreIn]
    exact Subgroup.map_subtype_le _
  have hImg : (P' ⊔ Q').map (Subgroup.subtype M) = Work.GW2.pCoreIn 2 M ⊔ B.U := by
    have e1 : P'.map (Subgroup.subtype M) = Work.GW2.pCoreIn 2 M := rfl
    have e2 : Q'.map (Subgroup.subtype M) = B.U := by
      show (Work.GW2.oddCore ↥M).map (Subgroup.subtype M) = B.U
      exact hU
    rw [Subgroup.map_sup, e1, e2]
  have hKsub : (Work.GW2.pCoreIn 2 M ⊔ B.U).subgroupOf M = P' ⊔ Q' := by
    have h2 : ((Work.GW2.pCoreIn 2 M ⊔ B.U).subgroupOf M).map (Subgroup.subtype M)
        = Work.GW2.pCoreIn 2 M ⊔ B.U := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (sup_le hPleM hQleM)]
    have hcomap : Subgroup.comap (Subgroup.subtype M)
          (((Work.GW2.pCoreIn 2 M ⊔ B.U).subgroupOf M).map (Subgroup.subtype M))
        = Subgroup.comap (Subgroup.subtype M) ((P' ⊔ Q').map (Subgroup.subtype M)) := by
      rw [h2, hImg]
    rwa [Subgroup.comap_map_eq_self (by rw [Subgroup.ker_subtype]; exact bot_le),
      Subgroup.comap_map_eq_self (by rw [Subgroup.ker_subtype]; exact bot_le)] at hcomap
  have hK'index : (P' ⊔ Q').index = 6 := by
    rw [← hKsub]
    exact hrel
  have hK'card : Nat.card (↥M ⧸ (P' ⊔ Q')) = 6 := by
    rw [← Subgroup.index_eq_card]
    exact hK'index
  -- solvability of the three groups involved
  haveI : Group.IsSolvable ↥P' := by
    haveI h2 : IsPGroup 2 ↥P' := IsPGroup.of_card (n := 2) (by rw [hP'card]; norm_num)
    haveI h3 : Group.IsNilpotent ↥P' := h2.isNilpotent
    exact inferInstance
  haveI : Group.IsSolvable ↥Q' := I.toolkit.ft ↥Q' hQ'odd
  haveI : Group.IsSolvable (↥M ⧸ (P' ⊔ Q')) := solvable_of_card_six hK'card
  haveI : (P' : Subgroup ↥M).Normal := by rw [hP'def]; infer_instance
  haveI : (Q' : Subgroup ↥M).Normal := by rw [hQ'def]; infer_instance
  -- `(P' ⊔ Q')/P'` is a quotient of `Q'`
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (P'.subgroupOf (P' ⊔ Q'))).comp (Subgroup.inclusion le_sup_right)) := by
    intro y
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (P'.subgroupOf (P' ⊔ Q')) y
    obtain ⟨p, hp, q, hq, hpq⟩ := Subgroup.mem_sup_of_normal_left.mp z.2
    refine ⟨⟨q, hq⟩, ?_⟩
    rw [← hz]
    have hzprod : z = (⟨p, Subgroup.mem_sup_left hp⟩ : ↥(P' ⊔ Q')) *
        (⟨q, Subgroup.mem_sup_right hq⟩ : ↥(P' ⊔ Q')) := by
      apply Subtype.ext
      show (z : ↥M) = p * q
      rw [hpq]
    have hone : (QuotientGroup.mk' (P'.subgroupOf (P' ⊔ Q')))
        (⟨p, Subgroup.mem_sup_left hp⟩ : ↥(P' ⊔ Q')) = 1 :=
      (QuotientGroup.eq_one_iff (⟨p, Subgroup.mem_sup_left hp⟩ : ↥(P' ⊔ Q'))).mpr (by
        rw [Subgroup.mem_subgroupOf]
        exact hp)
    rw [hzprod, map_mul, hone, one_mul]
    refine congrArg (QuotientGroup.mk' (P'.subgroupOf (P' ⊔ Q'))) (Subtype.ext ?_)
    rfl
  have hK'solv : Group.IsSolvable ↥(P' ⊔ Q') := by
    haveI : Group.IsSolvable ((↥(P' ⊔ Q')) ⧸ (P'.subgroupOf (P' ⊔ Q'))) :=
      Group.isSolvable_of_surjective hsurj
    haveI : Group.IsSolvable ↥(P'.subgroupOf (P' ⊔ Q')) :=
      Group.isSolvable_of_surjective
        (f := ((Subgroup.subgroupOfEquivOfLe (le_sup_left : P' ≤ P' ⊔ Q')).symm).toMonoidHom)
        ((Subgroup.subgroupOfEquivOfLe (le_sup_left : P' ≤ P' ⊔ Q')).symm).surjective
    exact Group.isSolvable_of_subgroup_quotient (P'.subgroupOf (P' ⊔ Q'))
  exact Group.isSolvable_of_subgroup_quotient (P' ⊔ Q')

/-! ## The main lemma -/

theorem Case2NotHLeM (I : Work.GW2.C4Inputs) : ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G, ∀ M : Subgroup G, IsCoatom M → B.t ∈ Work.GW2.layerIn M → (∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ Work.GW2.fittingIn B.U ∧ Subgroup.normalizer (X : Set G) ≤ M) → ¬ B.H ≤ M := by
  intro G _ _ hbc B M hcoat ht _hX hHM
  -- Bender's Theorem 2.6 for the maximal subgroup `M ⊇ H = C(t)`
  let B' : Work.GW2.BenderSetup G :=
    { S := B.S, S0 := B.S0, t := B.t, Hhat := M, S0_le := B.S0_le, S0_cyclic := B.S0_cyclic,
      S0_index := B.S0_index, t_mem := B.t_mem, t_order := B.t_order, Hhat_coatom := hcoat,
      H_le_Hhat := hHM }
  have h26 := I.thm26 G I.toolkit.ft hbc B'
  have hU : Work.GW2.oddCoreIn M = B.U := h26.1
  rcases h26.2.2 with ⟨-, hMH⟩ | ⟨hfour, hrel, -⟩
  · -- first alternative: `M = H = C_G(t)`, so `E(M)` centralizes `t`
    obtain ⟨hqs, -, hoddZ, e, he, heq⟩ := layer_facts I hbc hcoat ht
    have he2 : orderOf e = 2 := by
      have h1 : orderOf ((e : ↥M) : G) = orderOf e := Subgroup.orderOf_coe e
      rw [heq, B.t_order] at h1
      exact h1.symm
    have hcen : ∀ x ∈ Work.GW2.layer ↥M, x * e = e * x := by
      intro x _
      apply Subtype.ext
      have hxM : ((x : ↥M) : G) ∈ B.H := hMH ▸ (x : ↥M).2
      rw [Subgroup.mem_centralizer_singleton_iff] at hxM
      show ((x : ↥M) : G) * ((e : ↥M) : G) = ((e : ↥M) : G) * ((x : ↥M) : G)
      rw [heq]
      exact hxM
    exact false_of_quasisimple_involution (Work.GW2.layer ↥M) hqs hoddZ he he2 hcen
  · -- second alternative: `M` is solvable
    have hsolv : Group.IsSolvable ↥M := solvable_of_case2 I B hU hfour hrel
    have hbot : Work.GW2.layerIn M = ⊥ := layerIn_eq_bot_of_solvable hsolv
    refine absurd (Subgroup.mem_bot.mp (hbot ▸ ht)) ?_
    intro h1
    have ht2 := B.t_order
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)

end Work.CORE4
