import Mathlib
import Submission.Work.PSU3.StageA.caseC_not_abelian
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3.StageA

/-- **Case c) of Peterfalvi II Ch. VI §1, abelian case: `C_Q(P) ≤ Q₀`.**

If `Q` is abelian and `P ≤ V = C_D(t)` is a subgroup of prime order, then `Q ⊓ C_G(P) ≤ Q₀`;
this is steps (2)–(7) of the argument of `caseC_not_abelian` (the case distinction `Q ⊓ C_G(P) = S`
for the Sylow `2`-subgroup `S` of `F = O^{2'}(C_G(P))`, and the model fact that the image of `S`
in the simple Bender group `Y = F/Z(F)` is an elementary abelian Sylow `2`-subgroup).

Note that the hypothesis `IsAbelianSubgroup Q` is used only in step (7), to see that
`S ↪ Y` has abelian image. -/
theorem caseC_CQ_le_Q0sub_of_abelian {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q)
    {P : Subgroup G} (hPle : P ≤ Submission.Blueprint.centD H t)
    (hPprime : (Nat.card P).Prime) :
    Q ⊓ Subgroup.centralizer (P : Set G) ≤ Work.ThmF.Q0sub H := by
  classical

  have hsplit : IsSplitRankOne H Q t := hS.split
  have hH : IsStronglyEmbedded H := hsplit.stronglyEmbedded
  have ht2 : orderOf t = 2 := hsplit.invol
  have htH : t ∉ H := hsplit.not_mem
  have hfour : HasFourGroup G := hS.situation.1.1
  have hcomm := Work.ThmF.L5.involutions_commute hS.situation hC4 hsplit
  have hQ0el := Work.ThmF.L5.Q0sub_elementary hcomm
  have hQ0mem := mem_Q0sub_iff_sq_eq_one hS hC4
  have hQ0card : Nat.card ↥(Work.ThmF.Q0sub H) = (involutions (H : Set G)).ncard + 1 :=
    Work.ThmF.L5.card_Q0sub_eq hcomm
  have hInv2 : 2 ≤ (involutions (H : Set G)).ncard := Work.ThmF.Bender.cardInvGeTwo hH hfour
  have hq3 : 3 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by rw [hQ0card]; omega
  -- (0) the distinguished involution and the two-point stabiliser
  obtain ⟨⟨s, r⟩, hbody, -⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hsplit)
  obtain ⟨hsQ, hs2, hrQ, hsr0⟩ := hbody
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsr : t * s * t = (r⁻¹)⁻¹ * t * r⁻¹ := by simpa only [inv_inv, hti] using hsr0
  have hVeq := Work.PSU3.StageA.centD_eq_centralizer_s hS hsQ hs2 (Q.inv_mem hrQ) hsr
  have hsInv : s ∈ involutions (H : Set G) := ⟨hsplit.le hsQ, hs2⟩
  -- (1) `P ≤ V = centD H t` has prime order, so its centraliser has 4-rank ≥ 2
  have hPne : P ≠ ⊥ := by
    intro hc
    have h1 : Nat.card ↥P = 1 := by rw [hc]; simp
    exact hPprime.ne_one h1
  have hB3P : HasFourGroup (Subgroup.centralizer (P : Set G)) := hS.B3 P hPle hPprime
  haveI : Fact (Nat.Prime (Nat.card ↥P)) := ⟨hPprime⟩

  -- (2) Ch. II §4 Prop. 3 for `X = P`
  have hP1b := (hC4 G hS.situation H hH t ht2 htH).1
  have hX3 : 3 ≤ (fixedPts H P).ncard :=
    le_trans (Work.ThreePoints.three_le_ncard_fixedPts_centD hH ht2 htH)
      (Set.ncard_le_ncard (Work.ThreePoints.fixedPts_mono hPle))
  obtain ⟨k, hkK, hk1, hkN⟩ := Work.ThmF.ChV12.exists_k_normalizing hH ht2 htH hPle hX3 hB3P hP1b
  have hP3 := (hC4 G hS.situation H hH t ht2 htH).2.2.2.1
  set C : Subgroup G := Subgroup.centralizer (P : Set G) with hCdef
  set F : Subgroup G := Subgroup.map C.subtype (Submission.Blueprint.oddResidual ↥C) with hFdef
  set NN : Subgroup G := Subgroup.normalizer (P : Set G) with hNNdef
  have hP3c := hP3 P hPne hPle ⟨k, hkK, hk1, hkN⟩
  dsimp only at hP3c
  rw [← hCdef, ← hFdef, ← hNNdef] at hP3c
  obtain ⟨-, ⟨S, hSp, hSFH, -, hSNG, hSD, hSsup⟩, hFdata, -⟩ := hP3c
  obtain ⟨hFcenter, Y, instY, φ, hφsurj, hφker, hYsimple⟩ := hFdata
  have hSF : S ≤ F := fun z hz => (Subgroup.mem_inf.mp (hSFH hz)).1
  have hSH : S ≤ H := fun z hz => (Subgroup.mem_inf.mp (hSFH hz)).2
  have hFC : F ≤ C := by rw [hFdef]; exact Subgroup.map_subtype_le _
  have hSC : S ≤ C := hSF.trans hFC
  have hCNN : C ≤ NN := by rw [hCdef, hNNdef]; exact Subgroup.centralizer_le_normalizer _
  -- (3) `S ≤ Q`: `Q` is the (unique) Sylow `2`-subgroup of the odd-index normal subgroup
  have hQn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff (show Q ≤ H from hsplit.le)).mpr
      (fun a b ha hb => (Subgroup.mem_normalizer_iff.mp (hsplit.normal hb) a).mp ha)
  have hQidx : (Q.subgroupOf H).index = Nat.card ↥(twoPoint H t) := by
    have h1 : Nat.card ↥(Q.subgroupOf H) * (Q.subgroupOf H).index = Nat.card ↥H :=
      Subgroup.card_mul_index _
    have h2 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsplit.le).toEquiv
    have h3 : Nat.card ↥H = Nat.card ↥Q * Nat.card ↥(twoPoint H t) :=
      Work.ThmF.card_H_eq_mul_of_data (Work.ThmF.IsSplitRankOne.toData hsplit)
    have h4 : Nat.card ↥Q * (Q.subgroupOf H).index =
        Nat.card ↥Q * Nat.card ↥(twoPoint H t) := by
      rw [← h2, h1, h3, h2]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h4
  have hQodd : Odd (Q.subgroupOf H).index := by
    rw [hQidx]; exact Work.ThmF.split_odd_card_twoPoint hsplit
  have hSQ : S ≤ Q := by
    intro z hz
    have hzH : z ∈ H := hSH hz
    obtain ⟨j, hj⟩ := Work.PSU3.StageA.exists_orderOf_eq_two_pow_of_mem_isPGroup hSp hz
    have hj' : orderOf (⟨z, hzH⟩ : ↥H) = 2 ^ j := by
      rw [← Subgroup.orderOf_coe (a := (⟨z, hzH⟩ : ↥H))]
      exact hj
    haveI := hQn
    have hmem : (⟨z, hzH⟩ : ↥H) ∈ Q.subgroupOf H :=
      Work.PSU3.StageA.mem_of_orderOf_eq_two_pow_of_normal_odd_index hQodd hj'
    exact hmem
  -- (4) `S` is a Sylow `2`-subgroup of `F`, and `S ≤ Q ⊓ C = C_Q(P)`
  have hCQle : Q ⊓ C ≤ H ⊓ NN :=
    le_inf (le_trans inf_le_left hsplit.le) (le_trans inf_le_right hCNN)
  have hDNodd : Odd (Nat.card ↥(twoPoint H t ⊓ NN)) := by
    have h := card_inf_dvd NN (twoPoint H t)
    rw [inf_comm] at h
    exact Odd.of_dvd_nat (Work.ThmF.split_odd_card_twoPoint hsplit) h
  have hLcard : Nat.card ↥(H ⊓ NN) = Nat.card ↥S * Nat.card ↥(twoPoint H t ⊓ NN) := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := S)
      (K := twoPoint H t ⊓ NN)
      (le_trans (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) hSNG)
    rw [hSsup] at h
    have hinf : S ⊓ (twoPoint H t ⊓ NN) = ⊥ := by
      have hassoc : S ⊓ (twoPoint H t ⊓ NN) = (S ⊓ twoPoint H t) ⊓ NN :=
        (inf_assoc S (twoPoint H t) NN).symm
      rw [hassoc, hSD, bot_inf_eq]
    rw [hinf, Subgroup.card_bot, mul_one] at h
    exact h
  have hCQS : Q ⊓ C = S := by
    have hle : S ≤ Q ⊓ C := le_inf hSQ hSC
    obtain ⟨k1, hk1⟩ := IsPGroup.iff_card.mp (hS.two.to_le inf_le_left :
      IsPGroup 2 ↥(Q ⊓ C))
    obtain ⟨k2, hk2⟩ := IsPGroup.iff_card.mp hSp
    have hdvd : 2 ^ k1 ∣ 2 ^ k2 * Nat.card ↥(twoPoint H t ⊓ NN) := by
      rw [← hk1, ← hk2, ← hLcard]
      exact card_dvd_card_of_le (Q ⊓ C) (H ⊓ NN) hCQle
    have hle2 : 2 ^ k1 ≤ 2 ^ k2 := pow_two_le_of_dvd_odd_mul hDNodd hdvd
    have hcardle : Nat.card ↥(Q ⊓ C) ≤ Nat.card ↥S := by rw [hk1, hk2]; exact hle2
    exact (Subgroup.eq_of_le_of_card_ge hle hcardle).symm
  -- (5) `|F| = |S| * odd`
  have hcount' := fixedPts_card_and_centralizer_index hS hC4 hPle hPne
  rw [← hCdef] at hcount'
  have hfp_odd : Odd (fixedPts H P).ncard := hcount'.2.2
  have hCCH : Nat.card ↥C = Nat.card ↥(H ⊓ C) * (fixedPts H P).ncard := hcount'.2.1
  have hFrelC : Nat.card ↥C = Nat.card ↥F * F.relIndex C := by
    have h := Subgroup.card_mul_index (F.subgroupOf C)
    have h2 : Nat.card ↥(F.subgroupOf C) = Nat.card ↥F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv
    rw [h2] at h
    exact h.symm
  have hHCl : H ⊓ C ≤ H ⊓ NN := le_inf inf_le_left (le_trans inf_le_right hCNN)
  have hHCrel : Nat.card ↥(H ⊓ NN) = Nat.card ↥(H ⊓ C) * (H ⊓ C).relIndex (H ⊓ NN) := by
    have h := Subgroup.card_mul_index ((H ⊓ C).subgroupOf (H ⊓ NN))
    have h2 : Nat.card ↥((H ⊓ C).subgroupOf (H ⊓ NN)) = Nat.card ↥(H ⊓ C) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHCl).toEquiv
    rw [h2] at h
    exact h.symm
  have hFrelS : Nat.card ↥F = Nat.card ↥S * S.relIndex F := by
    have h := Subgroup.card_mul_index (S.subgroupOf F)
    have h2 : Nat.card ↥(S.subgroupOf F) = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv
    rw [h2] at h
    exact h.symm
  have hkey : S.relIndex F * (F.relIndex C * (H ⊓ C).relIndex (H ⊓ NN)) =
      (fixedPts H P).ncard * Nat.card ↥(twoPoint H t ⊓ NN) := by
    have hSpos : 0 < Nat.card ↥S := Nat.card_pos
    have hstep : Nat.card ↥S * (S.relIndex F * (F.relIndex C * (H ⊓ C).relIndex (H ⊓ NN))) =
        Nat.card ↥S * ((fixedPts H P).ncard * Nat.card ↥(twoPoint H t ⊓ NN)) := by
      calc Nat.card ↥S * (S.relIndex F * (F.relIndex C * (H ⊓ C).relIndex (H ⊓ NN)))
          = (Nat.card ↥S * S.relIndex F) *
              (F.relIndex C * (H ⊓ C).relIndex (H ⊓ NN)) := by ring
        _ = Nat.card ↥F * (F.relIndex C * (H ⊓ C).relIndex (H ⊓ NN)) := by rw [hFrelS]
        _ = (Nat.card ↥F * F.relIndex C) * (H ⊓ C).relIndex (H ⊓ NN) := by ring
        _ = (Nat.card ↥(H ⊓ C) * (fixedPts H P).ncard) *
              (H ⊓ C).relIndex (H ⊓ NN) := by rw [← hFrelC, hCCH]
        _ = (Nat.card ↥(H ⊓ C) * (H ⊓ C).relIndex (H ⊓ NN)) *
              (fixedPts H P).ncard := by ring
        _ = Nat.card ↥(H ⊓ NN) * (fixedPts H P).ncard := by rw [← hHCrel]
        _ = (Nat.card ↥S * Nat.card ↥(twoPoint H t ⊓ NN)) * (fixedPts H P).ncard := by
              rw [hLcard]
        _ = Nat.card ↥S * ((fixedPts H P).ncard * Nat.card ↥(twoPoint H t ⊓ NN)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hSpos hstep
  have hSrelodd : Odd (S.relIndex F) :=
    Odd.of_dvd_nat (by rw [hkey]; exact hfp_odd.mul hDNodd) ⟨_, rfl⟩
  -- (6) `|F| = |oddCore F| * |Y|`, `S ↪ Y`: `(S.map φ).index` is odd
  set Sf : Subgroup ↥F := S.subgroupOf F with hSfdef
  set Sbar : Subgroup Y := Sf.map φ with hSbardef
  have hSfker : Sf ⊓ φ.ker = ⊥ := by
    have hSf_p : IsPGroup 2 ↥Sf := hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSF).symm
    obtain ⟨kf, hkf⟩ := IsPGroup.iff_card.mp hSf_p
    have hker_odd : Odd (Nat.card ↥(φ.ker)) := by
      rw [hφker, ← hFcenter]
      exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
    have hcop : Nat.Coprime (Nat.card ↥Sf) (Nat.card ↥(φ.ker)) := by
      rw [hkf]
      exact (Nat.coprime_two_left.mpr hker_odd).pow_left kf
    exact Subgroup.inf_eq_bot_of_coprime hcop
  have hSfcard : Nat.card ↥Sf = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv
  have hSbar_card : Nat.card ↥Sbar = Nat.card ↥Sf := by
    have hinj : Function.Injective
        (fun x : ↥Sf => (⟨φ x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ : ↥Sbar)) := by
      intro a b hab
      have hab' : φ (a : ↥F) = φ (b : ↥F) := congrArg Subtype.val hab
      have h1 : ((a : ↥F) * (b : ↥F)⁻¹) ∈ φ.ker := by
        have h2 : φ ((a : ↥F) * (b : ↥F)⁻¹) = 1 := by
          rw [map_mul, map_inv, hab', mul_inv_cancel]
        simpa [MonoidHom.mem_ker] using h2
      have h3 : ((a : ↥F) * (b : ↥F)⁻¹) ∈ Sf := Sf.mul_mem a.2 (Sf.inv_mem b.2)
      have h4 : ((a : ↥F) * (b : ↥F)⁻¹) ∈ (⊥ : Subgroup ↥F) := by
        rw [← hSfker]
        exact ⟨h3, h1⟩
      have h5 : (a : ↥F) * (b : ↥F)⁻¹ = 1 := by simpa using h4
      apply Subtype.ext
      have h6 : ((a : ↥F) * (b : ↥F)⁻¹ : ↥F) = 1 := h5
      exact mul_inv_eq_one.mp h6
    exact (Nat.card_congr (Equiv.ofBijective _
      ⟨hinj, fun y => by
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩)).symm
  have hYcard : Nat.card Y = Nat.card ↥Sbar * Sbar.index := (Subgroup.card_mul_index Sbar).symm
  have hFker : Nat.card ↥F = Nat.card ↥(oddCore ↥F) * Nat.card Y := by
    have h := Subgroup.card_mul_index (φ.ker)
    have h1 : Nat.card ↥(φ.ker) = Nat.card ↥(oddCore ↥F) := by rw [hφker, ← hFcenter]
    rw [h1, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφsurj, Subgroup.card_top] at h
    exact h.symm
  have hGrel : S.relIndex F = Nat.card ↥(oddCore ↥F) * Sbar.index := by
    have hSpos : 0 < Nat.card ↥S := Nat.card_pos
    have hstep : Nat.card ↥S * S.relIndex F =
        Nat.card ↥S * (Nat.card ↥(oddCore ↥F) * Sbar.index) := by
      calc Nat.card ↥S * S.relIndex F = Nat.card ↥F := hFrelS.symm
        _ = Nat.card ↥(oddCore ↥F) * Nat.card Y := hFker
        _ = Nat.card ↥(oddCore ↥F) * (Nat.card ↥Sbar * Sbar.index) := by rw [hYcard]
        _ = Nat.card ↥(oddCore ↥F) * (Nat.card ↥S * Sbar.index) := by
              rw [hSbar_card, hSfcard]
        _ = Nat.card ↥S * (Nat.card ↥(oddCore ↥F) * Sbar.index) := by ring
    exact Nat.eq_of_mul_eq_mul_left hSpos hstep
  have hSbar_odd : Odd Sbar.index :=
    Odd.of_dvd_nat hSrelodd ⟨_, by rw [hGrel]; ring⟩
  -- (7) the model fact: `Sbar` is elementary abelian
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  have hSbar_p : IsPGroup 2 ↥Sbar :=
    (hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSF).symm).map φ
  have hSbar_comm : ∀ a ∈ Sbar, ∀ b ∈ Sbar, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    have haQ : ((a₀ : ↥F) : G) ∈ Q := hSQ (Subgroup.mem_subgroupOf.mp ha₀)
    have hbQ : ((b₀ : ↥F) : G) ∈ Q := hSQ (Subgroup.mem_subgroupOf.mp hb₀)
    have hcomm₀ : a₀ * b₀ = b₀ * a₀ :=
      Subtype.ext (hab ((a₀ : ↥F) : G) haQ ((b₀ : ↥F) : G) hbQ)
    calc φ a₀ * φ b₀ = φ (a₀ * b₀) := (map_mul φ a₀ b₀).symm
      _ = φ (b₀ * a₀) := by rw [hcomm₀]
      _ = φ b₀ * φ a₀ := map_mul φ b₀ a₀
  have hSbar_sq : ∀ a ∈ Sbar, a * a = 1 :=
    abelian_sylow_two_sq_one hYsimple hSbar_p hSbar_odd hSbar_comm
  have hFsq : ∀ z ∈ S, z * z = 1 := by
    intro z hz
    have hzF : z ∈ F := hSF hz
    have hzSf : (⟨z, hzF⟩ : ↥F) ∈ Sf := Subgroup.mem_subgroupOf.mpr hz
    have h1 : φ ⟨z, hzF⟩ * φ ⟨z, hzF⟩ = 1 :=
      hSbar_sq _ (Subgroup.mem_map.mpr ⟨⟨z, hzF⟩, hzSf, rfl⟩)
    have h2 : (⟨z, hzF⟩ : ↥F) * ⟨z, hzF⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact h1
    have h3 : (⟨z, hzF⟩ : ↥F) * ⟨z, hzF⟩ ∈ (⊥ : Subgroup ↥F) := by
      rw [← hSfker]
      exact ⟨Sf.mul_mem hzSf hzSf, h2⟩
    have h4 : (⟨z, hzF⟩ : ↥F) * ⟨z, hzF⟩ = 1 := by simpa using h3
    exact congrArg (fun w : ↥F => (w : G)) h4
  have hS_le_Q0 : S ≤ Work.ThmF.Q0sub H := by
    intro z hz
    exact (hQ0mem ⟨z, hSQ hz⟩).mpr (Subtype.ext (hFsq z hz))
  have hCQ_le_Q0 : Q ⊓ C ≤ Work.ThmF.Q0sub H := hCQS.le.trans hS_le_Q0
  rw [hCdef] at hCQ_le_Q0
  exact hCQ_le_Q0

end Work.PSU3.StageA
