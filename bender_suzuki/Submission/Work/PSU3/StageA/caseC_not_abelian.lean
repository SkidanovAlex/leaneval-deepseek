import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.PSU3.StageA.coarseFrame_defs
import Submission.Work.PSU3.StageA.lemma2cAux
import Submission.Work.PSU3.StageA.CaseCIndex.fixedPts_card_and_centralizer_index
import Submission.Work.PSU3.StageA.CaseCModels.abelian_sylow_two_sq_one
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.lemma4
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.Reductions.OddResidual

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

/-- If `A, B` are subgroups then `|A ⊓ B|` divides `|B|`. -/
lemma card_inf_dvd {G : Type} [Group G] (A B : Subgroup G) :
    Nat.card ↥(A ⊓ B) ∣ Nat.card ↥B := by
  have h := Subgroup.card_mul_index ((A ⊓ B).subgroupOf B)
  have h2 : Nat.card ↥((A ⊓ B).subgroupOf B) = Nat.card ↥(A ⊓ B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [h2] at h
  exact ⟨_, h.symm⟩

/-- If `A ≤ B` are subgroups then `|A|` divides `|B|`. -/
lemma card_dvd_card_of_le {G : Type} [Group G] (A B : Subgroup G) (h : A ≤ B) :
    Nat.card ↥A ∣ Nat.card ↥B := by
  have h1 := Subgroup.card_mul_index (A.subgroupOf B)
  have h2 : Nat.card ↥(A.subgroupOf B) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [h2] at h1
  exact ⟨_, h1.symm⟩

/-- A `2`-power dividing `2 ^ k` times an odd number is at most `2 ^ k`. -/
lemma pow_two_le_of_dvd_odd_mul {k k' m : ℕ} (hm : Odd m) (h : 2 ^ k ∣ 2 ^ k' * m) :
    2 ^ k ≤ 2 ^ k' := by
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have h2 : 2 ^ k ∣ 2 ^ k' := hcop.dvd_of_dvd_mul_right h
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_iff_right (by norm_num) |>.mp
    (Nat.le_of_dvd (by positivity) h2))

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- In the situation `PSU3Hyp H Q t`, the subgroup `Q₀ = ⟨Inv H⟩` consists exactly of the
elements of `Q` of order dividing `2` (Ch. V §1 Prop. 1 (c)). -/
lemma mem_Q0sub_iff_sq_eq_one (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) :
    ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hcomm := Work.ThmF.L5.involutions_commute hS.situation hC4 hsplit
  have hQ0 := Work.ThmF.L5.Q0sub_elementary hcomm
  intro x
  constructor
  · intro hx
    exact Subtype.ext (hQ0.1 (x : G) hx)
  · intro hx
    by_cases h1 : x = 1
    · subst h1
      exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.one_mem_Q0 H)
    · have hmemH : (x : G) ∈ H := hsplit.le x.2
      have hxx : (x : G) * (x : G) = 1 := congrArg Subtype.val hx
      have h2 : orderOf (x : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hxx)
      have hord : orderOf (x : G) = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) (by simpa using h1)
        · exact h
      exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H ⟨hmemH, hord⟩)

/-- **Case c) of Peterfalvi II Ch. VI §1: `Q` is not abelian.**

If `|Q| = q³` with `q = |Q₀|`, `Q` cannot be abelian.  The proof follows the source's case 1 of
the Ch. VI §1 Proposition in a form that avoids the trichotomy of Ch. V §2 Lemma 2 (c): assuming
`Q` abelian, for a prime order subgroup `P ≤ V` the Sylow `2`-subgroup `S = C_Q(P)` of `C_H(P)`
has `|S| = |F|₂ = |Y|₂`, where `F = O^{2'}(C_G(P))` and `Y = F/Z(F)` is a simple Bender group;
so the image of `S` in `Y` is an abelian Sylow `2`-subgroup of `Y`, hence elementary abelian,
whence `S ≤ Q₀ = Ω₁(Q)`.  Then Peterfalvi's argument: `Q ⊋ Q₀` gives `x ∈ Q` of order `4`, and
conjugating its square to the distinguished involution `s` produces a `P`-set of size `q` on
which `P` (of odd prime order) has a fixed point `y` with `y² = s ≠ 1` — but `y ∈ C_Q(P) = S`,
contradiction. -/
theorem caseC_not_abelian {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) :
    ¬ Submission.Blueprint.IsAbelianSubgroup Q := by
  intro hab
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
  -- (1) a prime order subgroup `P ≤ V = C_D(t)`
  have hVne : centD H t ≠ ⊥ := Work.PSU3.StageA.centD_ne_bot hS
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hcardV : Nat.card ↥(centD H t) ≠ 1 := by
    intro hc
    haveI : Subsingleton ↥(centD H t) := (Nat.card_eq_one_iff_unique.mp hc).1
    exact hx (Subsingleton.elim x 1)
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hcardV
  haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centD H t)) p hpdvd
  set P : Subgroup G := Subgroup.zpowers (y : G) with hPdef
  have hPle : P ≤ centD H t := Subgroup.zpowers_le.mpr y.2
  have hPcard : Nat.card ↥P = p := by
    rw [hPdef, Nat.card_zpowers, Subgroup.orderOf_coe, hyord]
  have hPprime : (Nat.card P).Prime := by rw [hPcard]; exact hpprime
  have hPne : P ≠ ⊥ := by
    intro hc
    have h1 : Nat.card ↥P = 1 := by rw [hc]; simp
    rw [hPcard] at h1
    exact hpprime.ne_one h1
  have hB3P : HasFourGroup (Subgroup.centralizer (P : Set G)) := hS.B3 P hPle hPprime
  haveI : Fact (Nat.Prime (Nat.card ↥P)) := ⟨by rw [hPcard]; exact hpprime⟩
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
  -- (8) `Q ⊋ Q0sub`, so there is `z ∈ Q` of order `4`
  have hq1 : 1 < Nat.card ↥(Work.ThmF.Q0sub H) := by omega
  have hQne : Q ≠ Work.ThmF.Q0sub H := by
    intro hce
    have h1 : Nat.card ↥(Work.ThmF.Q0sub H) * Nat.card ↥(Work.ThmF.Q0sub H) = 1 := by
      have h2 : Nat.card ↥(Work.ThmF.Q0sub H) ^ 3 = Nat.card ↥(Work.ThmF.Q0sub H) := by
        rw [← hcard, hce]
      have h2' : Nat.card ↥(Work.ThmF.Q0sub H) *
          (Nat.card ↥(Work.ThmF.Q0sub H) * Nat.card ↥(Work.ThmF.Q0sub H)) =
          Nat.card ↥(Work.ThmF.Q0sub H) := by
        calc Nat.card ↥(Work.ThmF.Q0sub H) *
              (Nat.card ↥(Work.ThmF.Q0sub H) * Nat.card ↥(Work.ThmF.Q0sub H)) =
              Nat.card ↥(Work.ThmF.Q0sub H) ^ 3 := by ring
          _ = Nat.card ↥(Work.ThmF.Q0sub H) := h2
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [h2', mul_one])
    have h3 : 1 < Nat.card ↥(Work.ThmF.Q0sub H) * Nat.card ↥(Work.ThmF.Q0sub H) := by
      nlinarith [hq1]
    have h4 : (1 : ℕ) < 1 := h1 ▸ h3
    exact absurd h4 (by norm_num)
  obtain ⟨z, hzQ, hznot⟩ : ∃ z ∈ Q, z ∉ Work.ThmF.Q0sub H := by
    by_contra hcon
    push_neg at hcon
    exact hQne (le_antisymm hcon (Work.PSU3.StageA.Q0sub_le_Q hsplit))
  obtain ⟨j, hj⟩ := Work.PSU3.StageA.exists_orderOf_eq_two_pow_of_mem_isPGroup hS.two hzQ
  have hz2ne : z * z ≠ 1 := by
    intro hzz
    exact hznot ((hQ0mem ⟨z, hzQ⟩).mpr (Subtype.ext hzz))
  have hj2 : 2 ≤ j := by
    by_contra hcon
    have hjle : j ≤ 1 := by omega
    have hdvd : 2 ^ j ∣ 2 := by
      interval_cases j <;> norm_num
    have hzpow : z ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hj]
      exact hdvd
    exact hz2ne (by rwa [pow_two] at hzpow)
  set v : G := z ^ (2 ^ (j - 2)) with hvdef
  have hvQ : v ∈ Q := Q.pow_mem hzQ _
  have hv2 : v * v = z ^ (2 ^ (j - 1)) := by
    rw [hvdef, ← pow_add]
    congr 1
    have hjm : j - 1 = (j - 2) + 1 := by omega
    rw [hjm, pow_succ]
    ring_nf
  have hv4 : (v * v) * (v * v) = 1 := by
    rw [hv2, ← pow_add]
    have hexp : 2 ^ (j - 1) + 2 ^ (j - 1) = 2 ^ j := by
      have hjm : j = (j - 1) + 1 := by omega
      conv_rhs => rw [hjm, pow_succ]
      ring_nf
    rw [hexp]
    rw [← hj]
    exact pow_orderOf_eq_one z
  have hv2ne : v * v ≠ 1 := by
    intro hcontra
    rw [hv2] at hcontra
    have hdvd : orderOf z ∣ 2 ^ (j - 1) := orderOf_dvd_iff_pow_eq_one.mpr hcontra
    rw [hj] at hdvd
    have hle : 2 ^ j ≤ 2 ^ (j - 1) := Nat.le_of_dvd (by positivity) hdvd
    have h2 : j ≤ j - 1 := Nat.pow_le_pow_iff_right (by norm_num) |>.mp hle
    omega
  have hv2Inv : v * v ∈ involutions (H : Set G) := by
    refine ⟨hsplit.le (Q.mul_mem hvQ hvQ), ?_⟩
    have h2 : orderOf (v * v) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hv4)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hv2ne
    · exact h
  obtain ⟨d, hdD, hds⟩ := Work.ThmF.Bender.DTransitiveInv hH ht2 htH (v * v) hv2Inv s hsInv
  have hdH : d ∈ H := (Subgroup.mem_inf.mp hdD).1
  set w : G := d * v * d⁻¹ with hwdef
  have hwQ : w ∈ Q := (Subgroup.mem_normalizer_iff.mp (hsplit.normal hdH) v).mp hvQ
  have hw2 : w * w = s := by
    rw [hwdef]
    calc (d * v * d⁻¹) * (d * v * d⁻¹) = d * (v * v) * d⁻¹ := by group
      _ = s := hds
  -- (9) the `P`-set `{y ∈ Q | y² = s} = w · Q₀` has a `P`-fixed point
  set Yset : Set G := {y' : G | y' ∈ Q ∧ y' * y' = s} with hYsetdef
  have hYset_image : Yset = Set.image (fun y : G => w * y) (Work.ThmF.Q0sub H : Set G) := by
    ext y'
    constructor
    · intro hy'
      obtain ⟨hy'Q, hy'sq⟩ := hy'
      have h1 : y' * w⁻¹ = w⁻¹ * y' := hab y' hy'Q w⁻¹ (Q.inv_mem hwQ)
      refine ⟨w⁻¹ * y', ?_, ?_⟩
      · have hgoal : (w⁻¹ * y') * (w⁻¹ * y') = 1 := by
          calc (w⁻¹ * y') * (w⁻¹ * y') = w⁻¹ * (y' * w⁻¹) * y' := by group
            _ = w⁻¹ * (w⁻¹ * y') * y' := by rw [← h1]
            _ = (w⁻¹ * w⁻¹) * (y' * y') := by group
            _ = (w * w)⁻¹ * s := by
                rw [hy'sq, show w⁻¹ * w⁻¹ = (w * w)⁻¹ from by group]
            _ = s⁻¹ * s := by rw [hw2]
            _ = 1 := inv_mul_cancel s
        exact (hQ0mem ⟨w⁻¹ * y', Q.mul_mem (Q.inv_mem hwQ) hy'Q⟩).mpr (Subtype.ext hgoal)
      · show w * (w⁻¹ * y') = y'
        group
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Q.mul_mem hwQ (Work.PSU3.StageA.Q0sub_le_Q hsplit hy), ?_⟩
      have hcommw : y * w = w * y := hab y (Work.PSU3.StageA.Q0sub_le_Q hsplit hy) w hwQ
      calc (w * y) * (w * y) = w * (y * w) * y := by group
        _ = w * (w * y) * y := by rw [hcommw]
        _ = (w * w) * (y * y) := by group
        _ = s := by rw [hw2, hQ0el.1 y hy, mul_one]
  have hYcard' : Yset.ncard = Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hYset_image, Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel h)]
    exact (Nat.card_coe_set_eq (Work.ThmF.Q0sub H : Set G)).symm
  have hYinv : ∀ (g : ↥P), ∀ y' ∈ Yset, ((g : G) * y' * (g : G)⁻¹) ∈ Yset := by
    intro g y' hy'
    obtain ⟨hy'Q, hy'sq⟩ := hy'
    have hgD : (g : G) ∈ twoPoint H t := (Subgroup.mem_inf.mp (hPle g.2)).1
    have hgH : (g : G) ∈ H := (Subgroup.mem_inf.mp hgD).1
    have hgs : (g : G) * s * (g : G)⁻¹ = s := by
      have hmem : (g : G) ∈ centD H t := hPle g.2
      rw [hVeq] at hmem
      have hmem' : s * (g : G) = (g : G) * s :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmem).2 s (Set.mem_singleton s)
      rw [← hmem', mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hsplit.normal hgH) y').mp hy'Q, ?_⟩
    calc ((g : G) * y' * (g : G)⁻¹) * ((g : G) * y' * (g : G)⁻¹)
        = (g : G) * (y' * y') * (g : G)⁻¹ := by group
      _ = (g : G) * s * (g : G)⁻¹ := by rw [hy'sq]
      _ = s := hgs
  letI : MulAction ↥P ↥Yset :=
    { smul := fun g y' => ⟨(g : G) * (y' : G) * (g : G)⁻¹, hYinv g y' y'.2⟩
      one_smul := fun y' => Subtype.ext (by
        show ((1 : ↥P) : G) * (y' : G) * ((1 : ↥P) : G)⁻¹ = (y' : G)
        simp)
      mul_smul := fun g h y' => Subtype.ext (by
        show ((g : G) * (h : G)) * (y' : G) * ((g : G) * (h : G))⁻¹ =
          (g : G) * ((h : G) * (y' : G) * (h : G)⁻¹) * (g : G)⁻¹
        group) }
  have hpndvd : ¬ Nat.card ↥P ∣ Yset.ncard := by
    rw [hYcard', hPcard]
    have hQ0p : IsPGroup 2 ↥(Work.ThmF.Q0sub H) := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro w
      exact ⟨1, Subtype.ext (by simpa [pow_two] using hQ0el.1 (w : G) w.2)⟩
    obtain ⟨kq, hkq⟩ := IsPGroup.iff_card.mp hQ0p
    have hpodd : Odd p := by
      rw [← hPcard]
      exact Odd.of_dvd_nat (Work.ThmF.split_odd_card_twoPoint hsplit)
        (card_dvd_card_of_le P (twoPoint H t) (le_trans hPle inf_le_left))
    intro hpd
    rw [hkq] at hpd
    have hp2 : p ∣ 2 := hpprime.dvd_of_dvd_pow hpd
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
    · exact hpprime.ne_one h
    · rw [h] at hpodd
      exact absurd hpodd (by norm_num)
  obtain ⟨y₀, hy₀fix⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card
    (IsPGroup.card : IsPGroup (Nat.card ↥P) ↥P) ↥Yset hpndvd
  have hy₀fix' : ∀ g : ↥P, (g : G) * (y₀ : G) * (g : G)⁻¹ = (y₀ : G) := fun g =>
    congrArg Subtype.val (MulAction.mem_fixedPoints.mp hy₀fix g)
  have hy₀C : (y₀ : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h := hy₀fix' ⟨g, hg⟩
    calc (g : G) * (y₀ : G) = ((g : G) * (y₀ : G) * (g : G)⁻¹) * (g : G) := by group
      _ = (y₀ : G) * (g : G) := by rw [h]
  have hy₀Q : (y₀ : G) ∈ Q := y₀.2.1
  have hy₀sq : (y₀ : G) * (y₀ : G) = s := y₀.2.2
  have hy₀Q0 : (y₀ : G) ∈ Work.ThmF.Q0sub H :=
    hCQ_le_Q0 ⟨hy₀Q, hy₀C⟩
  have hfinal : (y₀ : G) * (y₀ : G) = 1 := by
    have h := (hQ0mem ⟨(y₀ : G), hy₀Q⟩).mp hy₀Q0
    exact congrArg Subtype.val h
  exact absurd (by rw [← hy₀sq, hfinal] : s = 1) (by
    intro hs1
    have h := hs2
    rw [hs1, orderOf_one] at h
    exact absurd h (by norm_num))

end Work.PSU3.StageA
