import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aFrattini
import Submission.Work.CORE3.Case1aAbelian
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.A7V18.le_of_inverts_of_odd
import Submission.Work.CORE3.A7V18.card_map_of_inf_ker_eq_bot
import Submission.Work.AUTA7.A7.CentralizerInvolution

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# `CORE3` / `A7V18` / `P0Card`: `|O_p(U) ∩ M| = 3`

Bender 1981, §3, p. 222–223.  In the subcase `Ĥ = H`, `P := O_p(U)` is centralized by `t₁` and
inverted by `t₂`, and for a maximal `M ⊇ N_G(P₂)` the paper claims `|P₀| = 3`, where
`P₀ := P ∩ M ≠ 1`.

The formal proof below uses the two facts that the paper's `M`-analysis provides *before*
this claim, and which are hypotheses of this leaf (`A7V18/V2InLayer`, `A7V18/P0ne`,
`A7V18/SylowEight`):

* `V₂ = ⟨t, t₂⟩ ≤ E(M) = layerIn M`, and
* `E(M)/Z(E(M)) ≅ A₇`.

The argument:

1. `P₀ ≤ E(M)`: since `t₂ ∈ E(M) ≤ M`, `L := E(M) ◁ M` and `t₂` inverts `P₀`, the element
   `x² = (x t₂ x⁻¹) t₂` lies in `L` for every `x ∈ P₀`, and `x` has odd order, so
   `x = (x²)^k ∈ L`.
2. `P₀ ∩ Z(L) = 1`, because a central element of `L` is centralized by the inverting `t₂`.
3. Hence `P₀` embeds in `L/Z(L) ≅ A₇`, and its image lies in the centralizer of the image of
   the involution `t ∈ L` (every element of `P₀ ≤ O(H)` commutes with `t`).
4. In `A₇` the centralizer of an involution has order `24`, so `|P₀| ∣ 24`.  As `P₀` is a
   `p`-group of odd order (`P₀ ≤ O(H)`), `|P₀| = p^k` is an odd prime power dividing `24`, i.e.
   `|P₀| ∈ {1, 3}`; and `P₀ ≠ 1` by hypothesis, so `|P₀| = 3`.
-/

namespace Work.CORE3.A7V18

open Subgroup

/-! ## The leaf -/

theorem P0Card (I : Work.CORE3.Case1Inputs) (hFr : Work.GW2.Case1aFrattiniProp)
    (hAb : Work.GW2.Case1aAbelianProp) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case1 B → B.Hhat = B.H → ∀ D : Work.GW2.Case1aData B, ∀ P2 M : Subgroup G,
        P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
        ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
        IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
        (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) ≠ ⊥ →
        (Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2 : Subgroup G) ≤ Work.GW2.layerIn M →
        Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
          alternatingGroup (Fin 7)) →
        Nat.card (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) = 3 := by
  intro G _instG _finG _hFT hCtx B _hCase _hHhat D P2 M _hP2le _hP2grp _hP2ndvd hMcoat _hNM
    hP0ne hV2 hIso
  classical
  set P0 : Subgroup G := (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) with hP0def
  set L : Subgroup G := Work.GW2.layerIn M with hLdef
  -- ## 1. `P0 ≤ O(H)` has odd order, and `t₂` inverts it
  have hP0_le_U : P0 ≤ B.U := inf_le_left.trans (Work.CORE3.c1aPcoreIn_le_self D.p B.U)
  have hU_odd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hP0_odd : Odd (Nat.card P0) :=
    Odd.of_dvd_nat hU_odd (Subgroup.card_dvd_of_le hP0_le_U)
  have hP0_inv : ∀ x ∈ P0, D.t2 * x * D.t2⁻¹ = x⁻¹ := fun x hx => D.inv x hx.1
  -- ## 2. `L = E(M)` is normal in `M`, and `t, t₂ ∈ L`
  have hLnorm : M ≤ Subgroup.normalizer (L : Set G) := by
    rw [hLdef]
    exact Work.CORE3.c1aLe_normalizer_map_subtype (K := M) (N := Work.GW2.layer ↥M)
      (Work.CORE3.mdata_layer_normal M)
  have ht2L : D.t2 ∈ L := hV2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t2))
  have htL : B.t ∈ L := hV2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
  -- ## 3. `P0 ≤ L`
  have hP0_le_L : P0 ≤ L := le_of_inverts_of_odd hLnorm inf_le_right ht2L hP0_inv hP0_odd
  have hLne : L ≠ ⊥ := fun h => hP0ne (le_bot_iff.mp (h ▸ hP0_le_L))
  -- ## 4. `Z(L)` has odd order (Bender 1.6 for the `D`-group `M`)
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro h
    exact hLne (by rw [hLdef, Work.GW2.layerIn, h, Subgroup.map_bot])
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    have hZlayer : Odd (Nat.card (Subgroup.center ↥(Work.GW2.layer ↥M))) :=
      (Work.CORE3.mdata_layer_quasisimple I hCtx B hMcoat hlayer_ne).2
    have hiso : ↥L ≃* ↥(Work.GW2.layer ↥M) := by
      rw [hLdef]
      exact (Subgroup.equivMapOfInjective (Work.GW2.layer ↥M) M.subtype
        (Subgroup.subtype_injective M)).symm
    rw [Nat.card_congr (Subgroup.centerCongr hiso).toEquiv]
    exact hZlayer
  -- ## 5. the reduction to `A₇`
  obtain ⟨e⟩ := hIso
  let f : ↥L →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have htL_ord : orderOf (⟨B.t, htL⟩ : ↥L) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨B.t, htL⟩ : ↥L)]
    exact B.t_order
  have hft_ne : f ⟨B.t, htL⟩ ≠ 1 := by
    intro hf1
    have hmk : (QuotientGroup.mk' (Subgroup.center ↥L)) (⟨B.t, htL⟩ : ↥L) = 1 :=
      e.injective (by simpa [f] using hf1)
    have hmem : (⟨B.t, htL⟩ : ↥L) ∈ Subgroup.center ↥L :=
      (QuotientGroup.eq_one_iff (⟨B.t, htL⟩ : ↥L)).mp (by simpa [QuotientGroup.mk'_apply] using hmk)
    have hdvd : 2 ∣ Nat.card (Subgroup.center ↥L) := by
      rw [← htL_ord]
      exact Subgroup.orderOf_dvd_natCard _ hmem
    exact Nat.not_even_iff_odd.mpr hZodd (even_iff_two_dvd.mpr hdvd)
  have hft_ord : orderOf (f ⟨B.t, htL⟩) = 2 := by
    have h2 : f ⟨B.t, htL⟩ * f ⟨B.t, htL⟩ = 1 := by
      rw [← map_mul]
      have hh : (⟨B.t, htL⟩ : ↥L) * ⟨B.t, htL⟩ = 1 := by
        rw [← pow_two, ← htL_ord, pow_orderOf_eq_one]
      rw [hh, map_one]
    have hdvd : orderOf (f ⟨B.t, htL⟩) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hft_ne
    · exact h
  have hcardC : Nat.card (Subgroup.centralizer ({f ⟨B.t, htL⟩} : Set (alternatingGroup (Fin 7)))) = 24 :=
    Work.AUTA7.A7.CentralizerInvolution
      (by rw [← pow_two, ← hft_ord, pow_orderOf_eq_one]) hft_ne
  -- ## 6. `P₀` embeds into `C_{A₇}(t)`; hence `|P₀| ∣ 24`
  set P0L : Subgroup ↥L := P0.subgroupOf L with hP0Ldef
  have hle : P0L.map f ≤ Subgroup.centralizer ({f ⟨B.t, htL⟩} : Set (alternatingGroup (Fin 7))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hxP0 : (x : G) ∈ P0 := by
      rw [hP0Ldef] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    have hcomm : (x : G) * B.t = B.t * (x : G) :=
      ((Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_U_le_H B (hP0_le_U hxP0))) B.t
        (by simp)).symm
    have hxt : x * ⟨B.t, htL⟩ = ⟨B.t, htL⟩ * x := by
      apply Subtype.ext
      simpa using hcomm
    rw [← map_mul, ← map_mul, hxt]
  have hcard_P0L : Nat.card P0L = Nat.card P0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0_le_L).toEquiv
  have hdisj : P0 ⊓ (Subgroup.center ↥L).map L.subtype = ⊥ := by
    have hcen_le : (Subgroup.center ↥L).map L.subtype ≤ Subgroup.centralizer ({D.t2} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have hc := Subgroup.mem_center_iff.mp hy (⟨D.t2, ht2L⟩ : ↥L)
      have hc' : (y : G) * D.t2 = D.t2 * (y : G) := by
        have := congrArg (fun w : ↥L => (w : G)) hc
        simpa using this.symm
      exact hc'.symm
    have hsub : P0 ⊓ (Subgroup.center ↥L).map L.subtype ≤
        P0 ⊓ Subgroup.centralizer ({D.t2} : Set G) :=
      le_inf inf_le_left (le_trans inf_le_right hcen_le)
    have h2 : P0 ⊓ Subgroup.centralizer ({D.t2} : Set G) = ⊥ :=
      Work.CORE2A.inverts_inf_centralizer_eq_bot_of_odd hP0_inv hP0_odd
    exact le_bot_iff.mp (h2 ▸ hsub)
  have hker : P0L ⊓ f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxP0L, hxker⟩
    have hxP0 : (x : G) ∈ P0 := by
      rw [hP0Ldef] at hxP0L
      exact Subgroup.mem_subgroupOf.mp hxP0L
    have hx1 : f x = 1 := MonoidHom.mem_ker.mp hxker
    have hmk : (QuotientGroup.mk' (Subgroup.center ↥L)) x = 1 :=
      e.injective (by simpa [f] using hx1)
    have hxZ : (x : G) ∈ (Subgroup.center ↥L).map L.subtype :=
      Subgroup.mem_map.mpr ⟨x, (QuotientGroup.eq_one_iff x).mp
        (by simpa [QuotientGroup.mk'_apply] using hmk), rfl⟩
    have hboth : (x : G) ∈ P0 ⊓ (Subgroup.center ↥L).map L.subtype := ⟨hxP0, hxZ⟩
    rw [hdisj, Subgroup.mem_bot] at hboth
    exact Subtype.ext hboth
  have hcard_map : Nat.card (P0L.map f) = Nat.card P0L := card_map_of_inf_ker_eq_bot f P0L hker
  have hcard1 : Nat.card P0 = Nat.card (P0L.map f) := by
    rw [hcard_map, hcard_P0L]
  have hdvd24 : Nat.card (P0L.map f) ∣ 24 := hcardC ▸ Subgroup.card_dvd_of_le hle
  -- ## 7. `|P₀|` is a prime power dividing `24`, hence `|P₀| = 3`
  have hp_odd : Odd D.p := by
    have hmem : D.p ∈ (Nat.card (Work.GW2.fittingIn B.U)).primeFactors := D.p_mem
    obtain ⟨-, hdvd, -⟩ := Nat.mem_primeFactors.mp hmem
    exact Odd.of_dvd_nat hU_odd
      (hdvd.trans (Subgroup.card_dvd_of_le (Work.CORE3.c1aFittingIn_le B.U)))
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  have hpgrp : IsPGroup D.p P0 := (Work.CORE3.c1aIsPGroup_pCoreIn D.p B.U).to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpgrp
  have hk24 : D.p ^ k ∣ 24 := by
    rw [← hk, hcard1]
    exact hdvd24
  have hkne : k ≠ 0 := by
    intro h
    exact hP0ne ((Subgroup.card_eq_one).mp (by rw [hk, h, pow_zero]))
  have hpdvd : D.p ∣ 24 := dvd_trans (dvd_pow_self D.p hkne) hk24
  have hp3 : D.p = 3 := by
    have h' : D.p ∣ 2 ^ 3 * 3 := by
      rw [show (2 : ℕ) ^ 3 * 3 = 24 by norm_num]
      exact hpdvd
    rcases (D.hp.dvd_mul).mp h' with h2 | h3
    · exfalso
      obtain ⟨j, hj⟩ := hp_odd
      rcases (Nat.dvd_prime Nat.prime_two).mp (D.hp.dvd_of_dvd_pow h2) with h1 | h1
      · exact D.hp.ne_one h1
      · rw [h1] at hj
        omega
    · rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
      · exact absurd h1 D.hp.ne_one
      · exact h1
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have h9 : D.p ^ 2 ∣ 24 := dvd_trans (Nat.pow_dvd_pow D.p h2) hk24
    rw [hp3] at h9
    norm_num at h9
  have hk_eq : k = 1 := by omega
  rw [hk, hp3, hk_eq, pow_one]

end Work.CORE3.A7V18
