import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.DSTR.quasisimpleSylow
import Submission.Work.Dihedral.Defs
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.DSTR.DihHelp.dih_decomp_reflection
import Submission.Work.DSTR.DihHelp.dih_sr_conj_rot
import Submission.Work.DSTR.DihHelp.cyclicSqOne
import Submission.Work.CORE2A.isFourGroup_closure_pair
import Submission.Work.CORE2A.center_card_le_two_of_le_dihedral

namespace Work.CORE2A

open Subgroup

/-! ## Auxiliary statements -/

/-- The index of `S ⊓ E` in `E` is odd when `E ◁ Y` and `S` is a Sylow `2`-subgroup of `Y`:
with `E` normal, `E ⊔ S` is a subgroup of `Y`, and `[E : E ⊓ S] = [E ⊔ S : S]` divides
`[Y : S]`, which is odd.  (Normalty of `E` is essential: for `Y = S₄`, `S` a Sylow
`2`-subgroup and `E` a non-normal Klein four subgroup, the index is `2`.) -/
theorem odd_index_inf_sylow_subgroupOf_aux {Y : Type} [Group Y] [Finite Y] (S : Sylow 2 Y)
    (E : Subgroup Y) (hE : E.Normal) :
    IsPGroup 2 (((S : Subgroup Y) ⊓ E).subgroupOf E) ∧
      Odd (((S : Subgroup Y) ⊓ E).subgroupOf E).index := by
  haveI hF2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hE
  constructor
  · exact ((S.isPGroup').to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : ((S : Subgroup Y) ⊓ E) ≤ E)).symm
  · -- `[(S ⊓ E) : E ⊓ S] = [E ⊔ S : S]`, and the latter divides `[Y : S]`
    have hrel : (S : Subgroup Y).relIndex E
        = (S : Subgroup Y).relIndex (E ⊔ (S : Subgroup Y)) := by
      have h1 := Subgroup.relIndex_mul_relIndex (H := (S : Subgroup Y) ⊓ E) (K := E)
        (L := E ⊔ (S : Subgroup Y)) inf_le_right le_sup_left
      have h2 := Subgroup.relIndex_mul_relIndex (H := (S : Subgroup Y) ⊓ E)
        (K := (S : Subgroup Y)) (L := E ⊔ (S : Subgroup Y)) inf_le_left le_sup_right
      have h3 : ((S : Subgroup Y) ⊓ E).relIndex E = (S : Subgroup Y).relIndex E :=
        Subgroup.inf_relIndex_right (S : Subgroup Y) E
      have h4 : ((S : Subgroup Y) ⊓ E).relIndex (S : Subgroup Y)
          = E.relIndex (S : Subgroup Y) :=
        Subgroup.inf_relIndex_left (S : Subgroup Y) E
      have h5 : E.relIndex (E ⊔ (S : Subgroup Y)) = E.relIndex (S : Subgroup Y) :=
        Subgroup.relIndex_sup_left (S : Subgroup Y) E
      rw [h3] at h1
      rw [h5] at h1
      rw [h4] at h2
      have hne : E.relIndex (S : Subgroup Y) ≠ 0 := by
        rw [← h4]
        exact Subgroup.index_ne_zero_of_finite
      have h6 : E.relIndex (S : Subgroup Y) * (S : Subgroup Y).relIndex E
          = E.relIndex (S : Subgroup Y) * (S : Subgroup Y).relIndex (E ⊔ (S : Subgroup Y)) := by
        rw [mul_comm (E.relIndex (S : Subgroup Y)), h1, ← h2]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h6
    have hdvd : (S : Subgroup Y).relIndex (E ⊔ (S : Subgroup Y)) ∣ (S : Subgroup Y).index := by
      have h := Subgroup.relIndex_mul_relIndex (H := (S : Subgroup Y))
        (K := E ⊔ (S : Subgroup Y)) (L := ⊤) le_sup_right le_top
      rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h
      exact ⟨_, h.symm⟩
    have hSodd : ¬ 2 ∣ (S : Subgroup Y).index := S.not_dvd_index
    have hodd : Odd ((S : Subgroup Y).relIndex (E ⊔ (S : Subgroup Y))) :=
      Nat.not_even_iff_odd.mp fun h => hSodd (Nat.dvd_trans (even_iff_two_dvd.mp h) hdvd)
    change Odd (((S : Subgroup Y) ⊓ E).relIndex E)
    rw [Subgroup.inf_relIndex_right (S : Subgroup Y) E, hrel]
    exact hodd

/-! ## The general statement

Let `Y` be a finite group whose Sylow `2`-subgroups are cyclic or dihedral, `E ◁ Y` quasisimple
with non-cyclic Sylow `2`-subgroups, and `S` a Sylow `2`-subgroup of `Y`.  If `z ∈ Z(S)` is an
involution, then `z ∈ E`.

The proof is a local argument, no classification of `D`-groups is used.  Suppose `z ∉ E`, put
`P = S ⊓ E` (a Sylow `2`-subgroup of `E`, hence non-cyclic, hence of order `≥ 4`), and
`H = P ⊔ ⟨z⟩ ≤ S`.  Then `P` has index `2` in `H`, `z` is central in `H` and `z ∉ P`, so
`H = P × ⟨z⟩` and the centre of `H` contains `Z(P) × ⟨z⟩`.  As `P` is a non-trivial `2`-group,
`Z(P) ≠ 1`, and every non-cyclic subgroup of a dihedral group of order `≥ 5` has centre of order
`≤ 2`; since `H` is non-cyclic of order `≥ 5`, this is the required contradiction. -/
theorem involution_mem_of_mem_center_sylow {Y : Type} [Group Y] [Finite Y]
    (hsyl : Work.GW2.DihOrCycSylow Y) (E : Subgroup Y) (hEn : E.Normal)
    (hEq : Work.GW2.IsQuasisimple E)
    (h2p : ∀ P : Sylow 2 E, ¬ IsCyclic P)
    (S : Sylow 2 Y) (z : Y) (hzS : z ∈ (S : Subgroup Y)) (hz2 : orderOf z = 2)
    (hzc : ∀ x ∈ (S : Subgroup Y), x * z = z * x) : z ∈ E := by
  classical
  by_contra hzE
  haveI hF2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `P = S ⊓ E` and `H = P ⊔ ⟨z⟩`
  set P : Subgroup Y := (S : Subgroup Y) ⊓ E with hPdef
  have hPleE : P ≤ E := by rw [hPdef]; exact inf_le_right
  have hPleS : P ≤ (S : Subgroup Y) := by rw [hPdef]; exact inf_le_left
  have hzP : z ∉ P := by rw [hPdef]; exact fun h => hzE h.2
  -- `P` is a Sylow `2`-subgroup of `E`, hence non-cyclic and of order `≥ 4`
  have hPE : IsPGroup 2 ↥(P.subgroupOf E) := (odd_index_inf_sylow_subgroupOf_aux S E hEn).1
  have hPEodd : Odd (P.subgroupOf E).index := (odd_index_inf_sylow_subgroupOf_aux S E hEn).2
  have hPEidx : ¬ 2 ∣ (P.subgroupOf E).index := fun h =>
    (Nat.not_even_iff_odd.mpr hPEodd) (even_iff_two_dvd.mpr h)
  have hncPE : ¬ IsCyclic ↥(P.subgroupOf E) := h2p (hPE.toSylow hPEidx)
  have hcardPE : 4 ≤ Nat.card ↥(P.subgroupOf E) := by
    obtain ⟨k, hk⟩ := hPE.exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra hcon
      rcases (show k = 0 ∨ k = 1 by omega) with h0 | h1
      · haveI : Subsingleton ↥(P.subgroupOf E) := by
          rw [← Finite.card_le_one_iff_subsingleton, hk, h0]
          norm_num
        exact hncPE isCyclic_of_subsingleton
      · exact hncPE (isCyclic_of_prime_card (p := 2) (by rw [hk, h1]; norm_num))
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      _ = Nat.card ↥(P.subgroupOf E) := hk.symm
  have hcardP : 4 ≤ Nat.card ↥P := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleE).toEquiv]
    exact hcardPE
  set H : Subgroup Y := P ⊔ Subgroup.zpowers z with hHdef
  have hPH : P ≤ H := by rw [hHdef]; exact le_sup_left
  have hzH : z ∈ H := by
    rw [hHdef]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hHS : H ≤ (S : Subgroup Y) := by
    rw [hHdef]
    exact sup_le hPleS (Subgroup.zpowers_le.mpr hzS)
  have hnePH : P ≠ H := fun h => hzP (h ▸ hzH)
  have hcardH : 5 ≤ Nat.card ↥H := by
    have hlt := Subgroup.card_lt_of_lt (H := P) (K := H) (lt_of_le_of_ne hPH hnePH)
    omega
  have hncH : ¬ IsCyclic ↥H := by
    intro hc
    haveI := hc
    exact hncPE ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hPleE)).mpr
      (Subgroup.isCyclic_of_le hPH))
  -- `S` is not cyclic, so `S ≅ DihedralGroup m`
  have hncS : ¬ IsCyclic ↥(S : Subgroup Y) := by
    intro hc
    haveI := hc
    exact hncH (Subgroup.isCyclic_of_le hHS)
  obtain ⟨m, ⟨e⟩⟩ : ∃ m, Nonempty (↥(S : Subgroup Y) ≃* DihedralGroup m) := by
    rcases hsyl S with hc | h
    · exact absurd hc hncS
    · exact h
  haveI hNeZero : NeZero m :=
    neZero_of_finite_dihedral (Finite.of_injective (e.symm : DihedralGroup m → ↥(S : Subgroup Y))
      e.symm.injective)
  -- the embedding of `H` into `DihedralGroup m`
  let phi : ↥H →* DihedralGroup m := e.toMonoidHom.comp (Subgroup.inclusion hHS)
  have hphiinj : Function.Injective phi :=
    e.injective.comp (Subgroup.inclusion_injective hHS)
  let isoH : ↥H ≃* ↥(phi.range) := MonoidHom.ofInjective hphiinj
  have hcenter_eq : Nat.card (Subgroup.center ↥H) = Nat.card (Subgroup.center ↥(phi.range)) :=
    Nat.card_congr (Subgroup.centerCongr isoH).toEquiv
  have hncRange : ¬ IsCyclic ↥(phi.range) := fun hc => hncH ((isoH.isCyclic).mpr hc)
  have hcardRange : 5 ≤ Nat.card ↥(phi.range) := by
    rw [← Nat.card_congr isoH.toEquiv]
    exact hcardH
  have hupper : Nat.card (Subgroup.center ↥(phi.range)) ≤ 2 :=
    center_card_le_two_of_le_dihedral phi.range hncRange hcardRange
  -- `Z(P)` is non-trivial, choose an involution `w` in it
  have hPgrp : IsPGroup 2 ↥P := (S.isPGroup').to_le hPleS
  haveI : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hZPbot : ⊥ < Subgroup.center ↥P := hPgrp.bot_lt_center
  have hZPtwo : 2 ∣ Nat.card ↥(Subgroup.center ↥P) := by
    rcases (hPgrp.to_subgroup (Subgroup.center ↥P)).card_eq_or_dvd with h1 | h2
    · exact absurd h1 (by
        have h := (Subgroup.one_lt_card_iff_ne_bot (Subgroup.center ↥P)).mpr
          (bot_lt_iff_ne_bot.mp hZPbot)
        omega)
    · exact h2
  obtain ⟨v, hv2⟩ := exists_prime_orderOf_dvd_card' 2 hZPtwo
  -- the involution `v` of `Z(P)`, viewed in `↥P` and in `Y`
  have hvP2 : orderOf (v : ↥P) = 2 := by
    rw [← Subgroup.orderOf_mk (v : ↥P) v.2]
    exact hv2
  have hv_sq : (v : ↥P) ^ 2 = 1 := ((orderOf_eq_iff (by norm_num : 0 < 2)).mp hvP2).1
  have hv_ne : (v : ↥P) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hvP2
    omega
  have hvP : ((v : ↥P) : Y) ∈ P := (v : ↥P).2
  -- `v` centralizes `P`, and `z` centralizes `P`
  have hvcent : ∀ p ∈ P, p * ((v : ↥P) : Y) = ((v : ↥P) : Y) * p := by
    intro p hp
    exact congrArg (fun t : ↥P => (t : Y)) (Subgroup.mem_center_iff.mp v.2 ⟨p, hp⟩)
  -- centrality of `uH` and of `zH` in `↥H`
  have hHcentU : H ≤ Subgroup.centralizer ({(((v : ↥P) : Y))} : Set Y) := by
    rw [hHdef]
    refine sup_le ?_ ?_
    · intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (hvcent p hp).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hzc _ (hPleS hvP)
  have hHcentZ : H ≤ Subgroup.centralizer ({z} : Set Y) := by
    rw [hHdef]
    refine sup_le ?_ ?_
    · intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (hzc p (hPleS hp)).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rfl
  -- the two involutions of `↥H`
  let uH : ↥H := Subgroup.inclusion hPH (v : ↥P)
  let zH : ↥H := ⟨z, hzH⟩
  have huH_val : ((uH : ↥H) : Y) = ((v : ↥P) : Y) := rfl
  have hzH_val : ((zH : ↥H) : Y) = z := rfl
  have huH2 : uH ^ 2 = 1 := by
    show (Subgroup.inclusion hPH (v : ↥P)) ^ 2 = 1
    rw [← map_pow, hv_sq, map_one]
  have hzH2 : zH ^ 2 = 1 := by
    apply Subtype.ext
    show z ^ 2 = (1 : Y)
    exact ((orderOf_eq_iff (by norm_num : 0 < 2)).mp hz2).1
  have huH1 : uH ≠ 1 := by
    intro h
    have h1 : (v : ↥P) = 1 := Subgroup.inclusion_injective hPH (by simpa using h)
    exact hv_ne h1
  have hzH1 : zH ≠ 1 := by
    intro h
    have h1 : z = (1 : Y) := congrArg Subtype.val h
    rw [h1, orderOf_one] at hz2
    omega
  have hcommH : uH * zH = zH * uH := by
    apply Subtype.ext
    show ((v : ↥P) : Y) * z = z * ((v : ↥P) : Y)
    exact hzc _ (hPleS hvP)
  have hneH : uH ≠ zH := by
    intro h
    have h1 : ((v : ↥P) : Y) = z := congrArg Subtype.val h
    exact hzP (h1 ▸ hvP)
  have huHcent : uH ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    show ((t : Y)) * ((v : ↥P) : Y) = ((v : ↥P) : Y) * ((t : Y))
    exact (Subgroup.mem_centralizer_iff.mp (hHcentU t.2) _ (Set.mem_singleton _)).symm
  have hzHcent : zH ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    show ((t : Y)) * z = z * ((t : Y))
    exact (Subgroup.mem_centralizer_iff.mp (hHcentZ t.2) _ (Set.mem_singleton _)).symm
  have hclosure_le : Subgroup.closure ({uH, zH} : Set ↥H) ≤ Subgroup.center ↥H := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact huHcent
    · exact hzHcent
  have hcard_cl : Nat.card ↥(Subgroup.closure ({uH, zH} : Set ↥H)) = 4 :=
    (isFourGroup_closure_pair huH2 hzH2 hcommH huH1 hzH1 hneH).1
  have h4center : 4 ≤ Nat.card (Subgroup.center ↥H) := by
    rw [← hcard_cl]
    refine Nat.card_le_card_of_injective
      (fun x : ↥(Subgroup.closure ({uH, zH} : Set ↥H)) =>
        (⟨(x : ↥H), hclosure_le x.2⟩ : ↥(Subgroup.center ↥H))) ?_
    intro a b hab
    have h1 : (a : ↥H) = (b : ↥H) := congrArg (fun y : ↥(Subgroup.center ↥H) => (y : ↥H)) hab
    exact Subtype.ext h1
  have : Nat.card (Subgroup.center ↥H) ≤ 2 := hcenter_eq ▸ hupper
  omega

theorem Thm26bTmemLayer {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (hFT : Work.GW2.FeitThompsonProp) (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (hE : Work.GW2.layerIn B.Hhat ≠ ⊥) : B.t ∈ Work.GW2.layerIn B.Hhat := by
  classical
  -- a non-trivial layer contains a normal quasisimple subgroup
  have hlayer_ne : Work.GW2.layer ↥B.Hhat ≠ ⊥ := by
    intro hbot
    exact hE (by rw [Work.GW2.layerIn, hbot, Subgroup.map_bot])
  obtain ⟨E0, hE0n, hE0q⟩ :
      ∃ E0 : Subgroup ↥B.Hhat, E0.Normal ∧ Work.GW2.IsQuasisimple E0 := by
    by_contra hcon
    exact hlayer_ne (by
      show sSup {E : Subgroup ↥B.Hhat | E.Normal ∧ Work.GW2.IsQuasisimple E} = ⊥
      rw [show {E : Subgroup ↥B.Hhat | E.Normal ∧ Work.GW2.IsQuasisimple E} = ∅ by
        ext E
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hcon ⟨E, h.1, h.2⟩, sSup_empty])
  -- `S` as a Sylow 2-subgroup of `Ĥ`
  have hSle : (B.S : Subgroup G) ≤ B.Hhat := bSetup_S_le_Hhat B
  let S' : Sylow 2 ↥B.Hhat := (B.S).subtype hSle
  have hS'coe : (S' : Subgroup ↥B.Hhat) = (B.S : Subgroup G).subgroupOf B.Hhat :=
    Sylow.coe_subtype (B.S) hSle
  -- `t` as an element of `Ĥ`
  let z : ↥B.Hhat := ⟨B.t, bSetup_t_mem_Hhat B⟩
  have hz2 : orderOf z = 2 := by
    show orderOf (⟨B.t, bSetup_t_mem_Hhat B⟩ : ↥B.Hhat) = 2
    rw [Subgroup.orderOf_mk B.t (bSetup_t_mem_Hhat B)]
    exact B.t_order
  have hzS : z ∈ (S' : Subgroup ↥B.Hhat) := by
    rw [hS'coe]
    exact B.S0_le B.t_mem
  have hzc : ∀ x ∈ (S' : Subgroup ↥B.Hhat), x * z = z * x := by
    intro x hx
    apply Subtype.ext
    have hxS : (x : G) ∈ (B.S : Subgroup G) := by
      rw [hS'coe] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    show (x : G) * B.t = B.t * (x : G)
    have h := Subgroup.mem_centralizer_iff.mp (bSetup_S_le_H B hxS) B.t (Set.mem_singleton B.t)
    exact h.symm
  -- the required inputs for the general statement
  have hsyl : Work.GW2.DihOrCycSylow ↥B.Hhat := dihOrCycSylow_subgroup hbc.sylow B.Hhat
  have h2p : ∀ P : Sylow 2 ↥E0, ¬ IsCyclic P := fun P =>
    Work.DSTR.quasisimpleSylow ↥B.Hhat hFT E0 hE0q P
  have hzE0 : z ∈ E0 :=
    involution_mem_of_mem_center_sylow hsyl E0 hE0n hE0q h2p S' z hzS hz2 hzc
  -- conclude
  have hE0le : E0 ≤ Work.GW2.layer ↥B.Hhat := le_sSup ⟨hE0n, hE0q⟩
  show B.t ∈ (Work.GW2.layer ↥B.Hhat).map B.Hhat.subtype
  exact Subgroup.mem_map.mpr ⟨z, hE0le hzE0, rfl⟩

end Work.CORE2A
