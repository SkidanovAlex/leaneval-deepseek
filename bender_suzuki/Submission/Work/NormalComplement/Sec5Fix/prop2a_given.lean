import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.NormalComplement.appIII
import Submission.Work.NormalComplement.sec5_prop2a
import Submission.Work.NormalComplement.p2a_invol_unique
import Submission.Work.NormalComplement.p2a_pow_four
import Submission.Work.NormalComplement.p2a_appIII_cyclic
import Submission.Work.NormalComplement.Sec5Fix.Defs
import Submission.Work.NormalComplement.Sec5Fix.Prelim
import Submission.Work.NormalComplement.Sec5Fix.p3F_inf_H_stronglyEmbedded_V
import Submission.Work.NormalComplement.Sec5Fix.no_fourGroup_of_sylow_odd_index
import Submission.Work.NormalComplement.Sec5Fix.no_fourGroup_of_involutions_ncard_eq_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Classical
open scoped Pointwise
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.Sec5Fix

private theorem mem_oddResidual_of_pow_two_eq_one {G : Type} [Group G] [Finite G] :
    ∀ (k : ℕ) (x : G), x ^ 2 ^ k = 1 → x ∈ Submission.Blueprint.oddResidual G := by
  intro k
  induction k with
  | zero =>
      intro x h
      have hx : x = 1 := by simpa using h
      rw [hx]
      exact one_mem _
  | succ k ih =>
      intro x h
      refine Work.Reductions.mem_oddResidual_of_mul_self_mem ?_
      refine ih (x * x) ?_
      have h1 : (x * x) ^ 2 ^ k = x ^ 2 ^ (k + 1) := by
        rw [← pow_two x, ← pow_mul, ← pow_succ']
      rw [h1]
      exact h

private theorem conj_mul_inv_self {G : Type} [Group G] {u t : G} (ht : orderOf t = 2)
    (hu : orderOf u = 2) : u * (u * t) * u⁻¹ = (u * t)⁻¹ := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu2, inv_eq_of_mul_eq_one_right ht2]
  calc u * (u * t) * u = (u * u) * (t * u) := by group
    _ = t * u := by rw [hu2, one_mul]

private theorem card_subgroupOf_eq {G : Type} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
  Nat.card_congr
    { toFun := fun x => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y => ⟨⟨(y : G), h y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl }

private theorem prime_eq_three_or_five_of_pow {f m : ℕ} (hf : f.Prime) (hm : 0 < m)
    (hn : f ^ m = 3 ∨ f ^ m = 5 ∨ f ^ m = 9) : f = 3 ∨ f = 5 := by
  have hdvd : f ∣ f ^ m := dvd_pow_self f (by omega)
  rcases hn with h | h | h
  · left
    rw [h] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hf.ne_one
    · exact h3
  · right
    rw [h] at hdvd
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · exact absurd h1 hf.ne_one
    · exact h5
  · left
    rw [h] at hdvd
    have h3 : f ∣ 3 := hf.dvd_of_dvd_pow (by rwa [show (9 : ℕ) = 3 ^ 2 from by norm_num] at hdvd)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3
    · exact absurd h1 hf.ne_one
    · exact h3

theorem prop2a_given (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    orderOf (u * t) = 3 ∨ orderOf (u * t) = 5 := by
  classical
  set V : Subgroup G := Submission.Blueprint.centD H t with hVdef
  have hVle : V ≤ Submission.Blueprint.centD H t := le_of_eq hVdef
  obtain ⟨S, hS2, hSle, hSidx, hSnorm, hSD, hSsup, hScard⟩ :=
    Work.NormalComplement.p2a_p3_data (G := G) hFT hC h
  have hSleH : S ≤ H := fun x hx => (hSle hx).2
  have hSleF : S ≤ Fc H t := hSle.trans inf_le_left
  have hScardO : (fixedPts H V).ncard = Nat.card ↥S + 1 := by
    rw [hScard, ← Nat.card_coe_set_eq]
    rfl
  have h3O : 3 ≤ (fixedPts H V).ncard :=
    Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem hVle
  have hcardS2 : 2 ≤ Nat.card ↥S := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSpow : ∃ k : ℕ, Nat.card ↥S = 2 ^ k := IsPGroup.iff_card.mp hS2
  have hdvdS : 2 ∣ Nat.card ↥S := by
    obtain ⟨k, hk⟩ := hSpow
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hk
      omega
    rw [hk]
    exact dvd_pow_self 2 hk0
  have huniqAll : (Submission.Blueprint.involutions
      ((H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)).ncard = 1 := by
    have h1 := p2a_invol_unique (G := G) hFT hC hC4 hP3 h
    simpa only [hVdef] using h1
  have hSsub : Submission.Blueprint.involutions (S : Set G) ⊆
      Submission.Blueprint.involutions
        ((H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rintro x ⟨hxS, hx2⟩
    exact ⟨Subgroup.mem_inf.mpr ⟨hSleH hxS, Work.ThreePoints.p3F_le_centralizer V (hSleF hxS)⟩,
      hx2⟩
  obtain ⟨y, hyS, hy2⟩ : ∃ y ∈ S, orderOf y = 2 := by
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvdS
    exact ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  have huniqS : (Submission.Blueprint.involutions (S : Set G)).ncard = 1 := by
    refine le_antisymm ?_ ?_
    · have h := Set.ncard_le_ncard hSsub (Set.toFinite _)
      omega
    · have hmem : y ∈ Submission.Blueprint.involutions (S : Set G) := ⟨hyS, hy2⟩
      have hpos : 0 < (Submission.Blueprint.involutions (S : Set G)).ncard :=
        Set.ncard_pos (Set.toFinite _) |>.mpr ⟨y, hmem⟩
      omega
  have huniqInvS : Work.BrauerSuzuki.HasUniqueInvolution ↥S :=
    p2a_appIII_hasUniqueInvolution_of_ncard_eq_one huniqS
  have hpowS : ∀ x ∈ S, ∃ k : ℕ, orderOf x = 2 ^ k := by
    intro x hx
    obtain ⟨k, hk⟩ := hS2 ⟨x, hx⟩
    have hdvd : orderOf x ∣ 2 ^ k := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have h := congrArg (fun z : ↥S => (z : G)) hk
      simpa [Subgroup.coe_pow] using h
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have hS_le_p3FA : S ≤ Work.ThreePoints.p3F A := by
    intro x hx
    have hxCV : x ∈ Subgroup.centralizer (V : Set G) :=
      Work.ThreePoints.p3F_le_centralizer V (hSleF hx)
    have hxCA : x ∈ Subgroup.centralizer (A : Set G) :=
      Subgroup.centralizer_le (fun y hy => h.A_le hy) hxCV
    obtain ⟨k, hk⟩ := hpowS x hx
    have hpoweq : (⟨x, hxCA⟩ : ↥(Subgroup.centralizer (A : Set G))) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      show x ^ 2 ^ k = 1
      rw [← hk]
      exact pow_orderOf_eq_one x
    exact Work.ThreePoints.mem_p3F.mpr
      ⟨⟨x, hxCA⟩,
        mem_oddResidual_of_pow_two_eq_one k (⟨x, hxCA⟩ : ↥(Subgroup.centralizer (A : Set G)))
          hpoweq, rfl⟩
  have hexpS : ∀ x ∈ S, x ^ 4 = 1 := by
    intro x hx
    exact p2a_pow_four (G := G) hFT hC hC4 hMF2 h x (hSleH hx) (hS_le_p3FA hx) (hpowS x hx)
  have hcardS_le8 : Nat.card ↥S ≤ 8 := by
    rcases Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution hS2 huniqInvS with
      hcyc | hgen
    · have h := p2a_appIII_cyclic_card_le_four hcyc hexpS
      omega
    · have h := p2a_appIII_genQuaternion_card_eq_eight hgen hexpS
      omega
  have hcards : Nat.card ↥S = 2 ∨ Nat.card ↥S = 4 ∨ Nat.card ↥S = 8 := by
    obtain ⟨k, hk⟩ := hSpow
    have hk1 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hk
      omega
    have hk3 : k ≤ 3 := by
      rw [hk] at hcardS_le8
      by_contra hcon
      push_neg at hcon
      have h16 : 16 ≤ 2 ^ k := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> simp_all [pow_succ]
  have hO3 : (fixedPts H V).ncard = 3 ∨ (fixedPts H V).ncard = 5 ∨
      (fixedPts H V).ncard = 9 := by
    rcases hcards with h | h | h <;> rw [hScardO, h] <;> omega
  have hOodd : Odd (fixedPts H V).ncard := by
    rcases hO3 with h | h | h <;> rw [h] <;> norm_num
  have hZodd : Odd (Nat.card ↥(Zact H t)) :=
    Odd.of_dvd_nat (Work.ThreePoints.IsStronglyEmbedded.odd_card_inf_conj h.se h.notMem)
      (Subgroup.card_dvd_of_le (Zact_le_twoPoint H t))
  have huF : u ∈ Fc H t :=
    Work.ThreePoints.mem_p3F_of_involution (X := V) hu.2.2 hu.2.1
  have htV : t ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp (Vc_le_centralizer H t hv)) t (by simp)).symm
  have htF : t ∈ Fc H t := Work.ThreePoints.mem_p3F_of_involution (X := V) htV h.invol
  have hsubA : Submission.Blueprint.IsSubnormalIn A V := by
    rw [hVdef]
    exact p2a_IsSubnormalIn_A_V (G := G) h
  have hNKA : Work.ThreePoints.HasNonTrivialNK H t A := p2a_HasNonTrivialNK_A (G := G) h
  have hNG_eq : Subgroup.normalizer (V : Set G) =
      Work.ThreePoints.p3F V ⊔ (Submission.Blueprint.centD H t ⊓
        Subgroup.normalizer (V : Set G)) :=
    (hP3 G h.sit H h.se t h.invol h.notMem V A hVle h.A_ne hsubA hNKA).1
  have hsupNG : V ⊔ Fc H t = Subgroup.normalizer (V : Set G) := by
    rw [hNG_eq, show Work.ThreePoints.p3F V = Fc H t from rfl,
      inf_eq_left.mpr (Subgroup.le_normalizer (H := Submission.Blueprint.centD H t))]
    exact sup_comm V (Fc H t)
  have hBrSz : Submission.Blueprint.BrauerSuzukiProp := Work.BrauerSuzuki.brauerSuzuki
  have hZJ : Submission.Blueprint.GlaubermanZJProp := Work.ThmF.ChV12.glaubermanZJ_free
  have hThmA : Submission.Blueprint.ThmAProp := Work.DoubleTransitivity.Sec7.ThmA hFT hZJ hBrSz
  have hMod : Submission.Blueprint.ModelFactsProp := Work.Models.models hFT
  have h2tNG : Work.DoubleTransitivity.IsTwoTransitiveOnSub
      (Subgroup.normalizer (V : Set G)) (fixedPts H V) :=
    (Work.ThreePoints.p3pkg hFT hC hThmA hZJ hBrSz hMod h.sit h.se h.invol h.notMem V hVle
      ⟨A, h.A_ne, hsubA, hNKA⟩).2
  have h2tFc : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Fc H t) (fixedPts H V) := by
    intro c hc d hd hcd c' hc' d' hd' hcd'
    obtain ⟨g, hgN, hg1, hg2⟩ := h2tNG c hc d hd hcd c' hc' d' hd' hcd'
    obtain ⟨v, hv, f, hf, hvf⟩ :=
      Work.ThreePoints.P3Sub.eq_mul_of_mem_sup_of_normal (S := V) (D := Fc H t)
        (K := Subgroup.normalizer (V : Set G)) Subgroup.le_normalizer
        (Work.ThreePoints.p3F_le_normalizer V) le_rfl hsupNG hgN
    refine ⟨f, hf, ?_, ?_⟩
    · have h1 : v • (f • c) = c' := by rw [← mul_smul, hvf, hg1]
      calc f • c = v⁻¹ • (v • (f • c)) := (inv_smul_smul v (f • c)).symm
        _ = v⁻¹ • c' := by rw [h1]
        _ = c' := hc' v⁻¹ (V.inv_mem hv)
    · have h1 : v • (f • d) = d' := by rw [← mul_smul, hvf, hg2]
      calc f • d = v⁻¹ • (v • (f • d)) := (inv_smul_smul v (f • d)).symm
        _ = v⁻¹ • d' := by rw [h1]
        _ = d' := hd' v⁻¹ (V.inv_mem hv)
  have htransFc : ∀ c d : ↥(Om H t), ∃ f : ↥(Fc H t), f • c = d := by
    intro c d
    obtain ⟨f, hf, hff⟩ := h2tFc.isTransitiveOnSub c.1 c.2 d.1 d.2
    exact ⟨⟨f, hf⟩, by apply Subtype.ext; rw [smul_coe]; exact hff⟩
  have h2tFc_sub : ∀ a1 a2 b1 b2 : ↥(Om H t), a1 ≠ a2 → b1 ≠ b2 →
      ∃ f : ↥(Fc H t), f • a1 = b1 ∧ f • a2 = b2 := by
    intro a1 a2 b1 b2 ha hb
    obtain ⟨f, hf, h1, h2⟩ :=
      h2tFc a1.1 a1.2 a2.1 a2.2 (fun h => ha (Subtype.ext h))
        b1.1 b1.2 b2.1 b2.2 (fun h => hb (Subtype.ext h))
    exact ⟨⟨f, hf⟩, by apply Subtype.ext; rw [smul_coe]; exact h1,
      by apply Subtype.ext; rw [smul_coe]; exact h2⟩
  have hptOm : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ Om H t :=
    Work.ThreePoints.pt_mem_fixedPts_of_le_centD hVle
  set a : ↥(Om H t) := ⟨QuotientGroup.mk (1 : G), hptOm⟩ with hadef
  have a_val : (a : G ⧸ H) = QuotientGroup.mk (1 : G) := rfl
  have hstab : MulAction.stabilizer ↥(Fc H t) a = (Fc H t ⊓ H).subgroupOf (Fc H t) := by
    ext x
    constructor
    · intro hx
      have hx' : x • a = a := MulAction.mem_stabilizer_iff.mp hx
      have h3 : ((x • a : ↥(Om H t)) : G ⧸ H) = (a : G ⧸ H) := congrArg _ hx'
      have h2 : (x : G) • (a : G ⧸ H) = (a : G ⧸ H) := by
        rwa [smul_coe (H := H) (t := t) x a] at h3
      have h2' : (QuotientGroup.mk (x : G) : G ⧸ H) = QuotientGroup.mk (1 : G) := by
        have h := h2
        rw [show (a : G ⧸ H) = QuotientGroup.mk (1 : G) from rfl,
          Work.DoubleTransitivity.smul_mk, mul_one] at h
        exact h
      have hxH : (x : G) ∈ H := by
        have h := QuotientGroup.eq.mp h2'
        rw [mul_one] at h
        simpa using H.inv_mem h
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨x.2, hxH⟩)
    · intro hx
      refine MulAction.mem_stabilizer_iff.mpr ?_
      have hxH : (x : G) ∈ H := (Subgroup.mem_subgroupOf.mp hx).2
      have h2 : (x : G) • (a : G ⧸ H) = (a : G ⧸ H) := by
        rw [show (a : G ⧸ H) = QuotientGroup.mk (1 : G) from rfl,
          Work.DoubleTransitivity.smul_mk, mul_one]
        exact QuotientGroup.eq.mpr (by simpa using hxH)
      apply Subtype.ext
      rw [smul_coe (H := H) (t := t) x a]
      exact h2
  haveI hpre : MulAction.IsPretransitive ↥(Fc H t) ↥(Om H t) :=
    ⟨fun c d => htransFc c d⟩
  have hstab_index : (MulAction.stabilizer ↥(Fc H t) a).index = (Om H t).ncard := by
    rw [MulAction.index_stabilizer_of_transitive, Nat.card_coe_set_eq]
  have hstab_index_odd : Odd ((Fc H t ⊓ H).subgroupOf (Fc H t)).index := by
    rw [← hstab, hstab_index]
    exact hOodd
  have hrelS_infH : Odd (S.relIndex (Fc H t ⊓ H)) := by
    have h := hSidx
    simp only [Subgroup.relIndex] at h ⊢
    exact Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have hrel_pow : S.relIndex (Fc H t ⊓ H) * (Fc H t ⊓ H).relIndex (Fc H t) =
      S.relIndex (Fc H t) :=
    Subgroup.relIndex_mul_relIndex S (Fc H t ⊓ H) (Fc H t) hSle inf_le_left
  have hrel_odd : Odd (S.relIndex (Fc H t)) := by
    rw [← hrel_pow]
    refine Odd.mul hrelS_infH ?_
    rw [show (Fc H t ⊓ H).relIndex (Fc H t) = ((Fc H t ⊓ H).subgroupOf (Fc H t)).index from rfl]
    exact hstab_index_odd
  have huniqS1 : (Submission.Blueprint.involutions
      ((S.subgroupOf (Fc H t)) : Set ↥(Fc H t))).ncard = 1 := by
    rw [Work.NormalComplement.involutions_ncard_subgroupOf_eq (F := Fc H t) (L := S) hSleF]
    exact huniqS
  have hS4 : ¬ Submission.Blueprint.HasFourGroup ↥(S.subgroupOf (Fc H t)) :=
    no_fourGroup_of_involutions_ncard_eq_one huniqS1
  have hSp1 : IsPGroup 2 (S.subgroupOf (Fc H t)) := by
    obtain ⟨k, hk⟩ := hSpow
    refine IsPGroup.iff_card.mpr ⟨k, ?_⟩
    rw [card_subgroupOf_eq hSleF, hk]
  have hF4 : ¬ Submission.Blueprint.HasFourGroup ↥(Fc H t) :=
    no_fourGroup_of_sylow_odd_index (S.subgroupOf (Fc H t)) (S.subgroupOf (Fc H t)) le_rfl hSp1
      (by rw [Subgroup.subgroupOf_self, Subgroup.index_top]; norm_num)
      (by simpa only [Subgroup.relIndex] using hrel_odd) hS4
  let phi : ↥(Fc H t) →* Equiv.Perm ↥(Om H t) := MulAction.toPermHom ↥(Fc H t) ↥(Om H t)
  let Gam : Subgroup (Equiv.Perm ↥(Om H t)) := phi.range
  have hkerphi : phi.ker = (Zact H t).subgroupOf (Fc H t) := by
    ext x
    constructor
    · intro hx
      refine Subgroup.mem_subgroupOf.mpr (mem_Zact.mpr ⟨x.2, ?_⟩)
      intro ω hω
      have h := congrArg
        (fun (e : Equiv.Perm ↥(Om H t)) => ((e ⟨ω, hω⟩ : ↥(Om H t)) : G ⧸ H))
        (MonoidHom.mem_ker.mp hx)
      simpa [phi, MulAction.toPermHom_apply, MulAction.toPerm_apply, smul_coe] using h
    · intro hx
      refine MonoidHom.mem_ker.mpr ?_
      have hx' : x ∈ (Zact H t).subgroupOf (Fc H t) := hx
      have hx2 : ∀ ω : G ⧸ H, ω ∈ Om H t → (x : G) • ω = ω :=
        (mem_Zact.mp (Subgroup.mem_subgroupOf.mp hx')).2
      ext ω
      have h1 : ((phi x) ω : ↥(Om H t)) = x • ω := rfl
      have h2 : (((phi x) ω : ↥(Om H t)) : G ⧸ H) = (x : G) • (ω : G ⧸ H) := by
        rw [h1, smul_coe (H := H) (t := t) x ω]
      rw [h2]
      simpa using hx2 ω.1 ω.2
  have hkerodd : Odd (Nat.card ↥(phi.ker)) := by
    rw [hkerphi, card_subgroupOf_eq (Zact_le H t)]
    exact hZodd
  have hGam4 : ¬ Submission.Blueprint.HasFourGroup ↥Gam := by
    intro h4
    have h1 : ¬ Submission.Blueprint.HasFourGroup (↥(Fc H t) ⧸ phi.ker) :=
      Work.ThreePoints.P3NeBot.not_hasFourGroup_quotient phi.ker hkerodd hF4
    exact h1 (hasFourGroup_of_mulEquiv (QuotientGroup.quotientKerEquivRange phi) h4)
  let psi : ↥(Fc H t) →* ↥Gam := phi.codRestrict Gam (fun x => ⟨x, rfl⟩)
  have hpsi_apply : ∀ x : ↥(Fc H t), ((psi x : ↥Gam) : Equiv.Perm ↥(Om H t)) = phi x :=
    fun x => rfl
  have hpsismul : ∀ (x : ↥(Fc H t)) (c : ↥(Om H t)), (psi x) • c = x • c := by
    intro x c
    have h1 : (psi x) • c = (MulAction.toPerm x) c := rfl
    rw [h1, MulAction.toPerm_apply]
  have hkerpsi : psi.ker = (Zact H t).subgroupOf (Fc H t) := by
    have h : ∀ x : ↥(Fc H t), x ∈ psi.ker ↔ x ∈ phi.ker := by
      intro x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      constructor
      · intro hx
        have h1 := congrArg (fun y : ↥Gam => (y : Equiv.Perm ↥(Om H t))) hx
        simpa [hpsi_apply] using h1
      · intro hx
        exact Subtype.ext (by simpa [hpsi_apply] using hx)
    ext x
    rw [h x, hkerphi]
  have hkerpsiodd : Odd (Nat.card ↥(psi.ker)) := by
    rw [hkerpsi, card_subgroupOf_eq (Zact_le H t)]
    exact hZodd
  have hsurjpsi : Function.Surjective psi := by
    rintro ⟨g, hg⟩
    rw [MonoidHom.mem_range] at hg
    obtain ⟨x, hx⟩ := hg
    exact ⟨x, Subtype.ext hx⟩
  have hkerpsi_le : psi.ker ≤ (Fc H t ⊓ H).subgroupOf (Fc H t) := by
    intro x hx
    have hxmem : x ∈ MulAction.stabilizer ↥(Fc H t) a := by
      rw [MulAction.mem_stabilizer_iff]
      have h1 : (psi x) • a = a := by
        rw [MonoidHom.mem_ker.mp hx]
        simp
      rwa [hpsismul] at h1
    rw [hstab] at hxmem
    exact hxmem
  have hLse : IsStronglyEmbedded ((Fc H t ⊓ H).subgroupOf (Fc H t)) :=
    p3F_inf_H_stronglyEmbedded_V (G := G) hC4 h
  have hstabGam : ((Fc H t ⊓ H).subgroupOf (Fc H t)).map psi = MulAction.stabilizer ↥Gam a := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      have hxmem : x ∈ MulAction.stabilizer ↥(Fc H t) a := by
        rw [hstab]
        exact hx
      rw [MulAction.mem_stabilizer_iff] at hxmem
      rw [hpsismul]
      exact hxmem
    · intro hg
      rw [MulAction.mem_stabilizer_iff] at hg
      obtain ⟨x, hx⟩ := hsurjpsi g
      refine ⟨x, ?_, hx⟩
      have h1 : (psi x) • a = a := by
        have h2 : g • a = a := hg
        rwa [← hx] at h2
      rw [hpsismul] at h1
      rw [← hstab]
      exact MulAction.mem_stabilizer_iff.mpr h1
  have hseGam : IsStronglyEmbedded (MulAction.stabilizer ↥Gam a) := by
    have h := Work.NormalComplement.isStronglyEmbedded_map_of_surjective psi hsurjpsi rfl
      hkerpsiodd hkerpsi_le hLse
    rwa [hstabGam] at h
  have hcoatGam : IsCoatom (MulAction.stabilizer ↥Gam a) := by
    have hb : ∃ b : ↥(Om H t), b ≠ a :=
      ⟨⟨QuotientGroup.mk t, Work.ThreePoints.mk_t_mem_fixedPts_of_le_centD hVle⟩,
        fun hne => Work.ThreePoints.P3Sub.mk_one_ne_mk_t h.notMem (Subtype.ext_iff.mp hne.symm)⟩
    have hcoatF : IsCoatom (MulAction.stabilizer ↥(Fc H t) a) :=
      Commons.GroupTheory.GroupAction.isCoatom_stabilizer_of_forall_pair
        (G := ↥(Fc H t)) (Ω := ↥(Om H t)) (fun p q r s => h2tFc_sub p q r s) a hb
    have hcoatF' : IsCoatom ((Fc H t ⊓ H).subgroupOf (Fc H t)) := by
      rw [← hstab]
      exact hcoatF
    have h2 := Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le (f := psi)
      (M := (Fc H t ⊓ H).subgroupOf (Fc H t)) hsurjpsi hcoatF' hkerpsi_le
    rwa [hstabGam] at h2
  have htransGam : MulAction.IsPretransitive ↥Gam ↥(Om H t) := by
    refine ⟨fun c d => ?_⟩
    obtain ⟨f, hf⟩ := htransFc c d
    exact ⟨psi f, by rw [hpsismul]; exact hf⟩
  have hfaithGam : ∀ g : ↥Gam, (∀ x : ↥(Om H t), g • x = x) → g = 1 := by
    intro g hg
    have h1 : (g : Equiv.Perm ↥(Om H t)) = 1 := by
      ext x
      have h2 : ((g : Equiv.Perm ↥(Om H t)) x : G ⧸ H) = (x : G ⧸ H) := congrArg _ (hg x)
      simpa using h2
    exact Subtype.ext h1
  obtain ⟨f, Q, hfprime, hQnorm, hQne, hQab, hQexp, hQinf, hQsup, huniqGam, hclause4, -⟩ :=
    hIII ↥Gam ↥(Om H t) a htransGam hfaithGam hGam4 hseGam hcoatGam
  haveI : Fact (Nat.Prime f) := ⟨hfprime⟩
  have hQpg : IsPGroup f Q := fun x =>
    ⟨1, by apply Subtype.ext; simpa [Subgroup.coe_pow] using hQexp x.1 x.2⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQpg
  have hcardQ : Nat.card ↥Q = (Om H t).ncard := by
    refine Nat.card_congr (Equiv.ofBijective (fun q : ↥Q => q • a) ⟨?_, ?_⟩)
    · intro q1 q2 hq
      change (q1 : ↥Gam) • a = (q2 : ↥Gam) • a at hq
      haveI := hQnorm
      have hmem : (q1 : ↥Gam)⁻¹ * q2 ∈ Q ⊓ MulAction.stabilizer ↥Gam a := by
        refine Subgroup.mem_inf.mpr ⟨Q.mul_mem (Q.inv_mem q1.2) q2.2, ?_⟩
        rw [MulAction.mem_stabilizer_iff, mul_smul, ← hq, inv_smul_smul]
      rw [hQinf] at hmem
      have h1 : (q1 : ↥Gam)⁻¹ * q2 = 1 := Subgroup.mem_bot.mp hmem
      exact Subtype.ext (inv_mul_eq_one.mp h1)
    · intro c
      obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := ↥Gam) a c
      haveI := hQnorm
      obtain ⟨q, hqQ, s, hs, hqs⟩ :=
        Subgroup.mem_sup_of_normal_left.mp (by rw [hQsup]; exact Subgroup.mem_top g)
      refine ⟨⟨q, hqQ⟩, ?_⟩
      show q • a = c
      rw [← hg, ← hqs, mul_smul, MulAction.mem_stabilizer_iff.mp hs]
  have hfm : f ^ m = (fixedPts H V).ncard := by rw [← hm, hcardQ]
  have hOpow : f ^ m = 3 ∨ f ^ m = 5 ∨ f ^ m = 9 := by
    rw [hfm]
    exact hO3
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hOpow
      rcases hOpow with h | h | h <;> omega
    · exact hpos
  have hf35 : f = 3 ∨ f = 5 := prime_eq_three_or_five_of_pow hfprime hmpos hOpow
  have hordpsiu : orderOf (psi ⟨u, huF⟩) = 2 := by
    have hdvd : orderOf (psi ⟨u, huF⟩) ∣ 2 := by
      have h1 := orderOf_map_dvd psi (⟨u, huF⟩ : ↥(Fc H t))
      rwa [(Subgroup.orderOf_coe (⟨u, huF⟩ : ↥(Fc H t))).symm.trans hu.2.1] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      have h2 : (⟨u, huF⟩ : ↥(Fc H t)) ∈ psi.ker := MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h)
      rw [hkerpsi] at h2
      have h3 : u ∈ Zact H t := Subgroup.mem_subgroupOf.mp h2
      have h4 : orderOf u ∣ Nat.card ↥(Zact H t) := Subgroup.orderOf_dvd_natCard _ h3
      rw [hu.2.1] at h4
      exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr h4)
    · exact h
  have hordpsit : orderOf (psi ⟨t, htF⟩) = 2 := by
    have hdvd : orderOf (psi ⟨t, htF⟩) ∣ 2 := by
      have h1 := orderOf_map_dvd psi (⟨t, htF⟩ : ↥(Fc H t))
      rwa [(Subgroup.orderOf_coe (⟨t, htF⟩ : ↥(Fc H t))).symm.trans h.invol] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exfalso
      have h2 : (⟨t, htF⟩ : ↥(Fc H t)) ∈ psi.ker :=
        MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h1)
      rw [hkerpsi] at h2
      exact h.notMem (Zact_le_H H t (Subgroup.mem_subgroupOf.mp h2))
    · exact h1
  have hpsine : psi ⟨u, huF⟩ ≠ psi ⟨t, htF⟩ := by
    intro hcon
    have h1 : (⟨u, huF⟩ : ↥(Fc H t))⁻¹ * ⟨t, htF⟩ ∈ psi.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcon, inv_mul_cancel]
    rw [hkerpsi] at h1
    have h2 : u⁻¹ * t ∈ Zact H t := by
      have h3 := Subgroup.mem_subgroupOf.mp h1
      simpa [Subgroup.coe_mul] using h3
    have h3 : u⁻¹ * t ∈ H := Zact_le_H H t h2
    have h4 : t ∈ H := by
      have h5 : u * (u⁻¹ * t) ∈ H := H.mul_mem hu.1 h3
      rwa [mul_inv_cancel_left] at h5
    exact h.notMem h4
  obtain ⟨hutQ, hordpsiut⟩ := hclause4 (psi ⟨u, huF⟩) (psi ⟨t, htF⟩) hordpsiu hordpsit hpsine
  have hpow1 : ((psi ⟨u, huF⟩) * (psi ⟨t, htF⟩)) ^ f = 1 := by
    rw [← hordpsiut, pow_orderOf_eq_one]
  have hZ : (u * t) ^ f ∈ Zact H t := by
    have h1 : ((⟨u, huF⟩ * ⟨t, htF⟩ : ↥(Fc H t)) ^ f) ∈ psi.ker := by
      rw [MonoidHom.mem_ker, map_pow, map_mul, hpow1]
    rw [hkerpsi] at h1
    have h2 : ((⟨u, huF⟩ * ⟨t, htF⟩ : ↥(Fc H t)) ^ f : ↥(Fc H t)) ∈
        (Zact H t).subgroupOf (Fc H t) := h1
    have h3 := Subgroup.mem_subgroupOf.mp h2
    have h4 : (((⟨u, huF⟩ * ⟨t, htF⟩ : ↥(Fc H t)) ^ f : ↥(Fc H t)) : G) = (u * t) ^ f := rfl
    rwa [h4] at h3
  have ht2 : t * t = 1 := by rw [← pow_two, ← h.invol]; exact pow_orderOf_eq_one t
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu.2.1]; exact pow_orderOf_eq_one u
  have huinv : u * (u * t) ^ f * u⁻¹ = ((u * t) ^ f)⁻¹ := by
    calc u * (u * t) ^ f * u⁻¹ = (MulAut.conj u) ((u * t) ^ f) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj u) (u * t)) ^ f := map_pow _ _ _
      _ = ((u * t)⁻¹) ^ f := by rw [MulAut.conj_apply, conj_mul_inv_self h.invol hu.2.1]
      _ = ((u * t) ^ f)⁻¹ := inv_pow _ _
  have huCentZ : ∀ x ∈ Zact H t, u * x = x * u :=
    hC G h.sit H h.se t h.notMem u ⟨hu.1, hu.2.1⟩ (Zact H t) (Zact_le_twoPoint H t)
      ((Fc_le_normalizer_Zact H t) huF)
  have hxsq : (u * t) ^ f * (u * t) ^ f = 1 := by
    have h1 : (u * t) ^ f = ((u * t) ^ f)⁻¹ := by
      have hx := huCentZ ((u * t) ^ f) hZ
      rw [← huinv, hx]
      group
    have h2 : (u * t) ^ f * (u * t) ^ f = (u * t) ^ f * ((u * t) ^ f)⁻¹ :=
      congrArg (fun y => (u * t) ^ f * y) h1
    rw [h2, mul_inv_cancel]
  have hxone : (u * t) ^ f = 1 := by
    have hdvd2 : orderOf ((u * t) ^ f) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hxsq
    have hdvdZ : orderOf ((u * t) ^ f) ∣ Nat.card ↥(Zact H t) :=
      Subgroup.orderOf_dvd_natCard _ hZ
    have hodd : Odd (orderOf ((u * t) ^ f)) := Odd.of_dvd_nat hZodd hdvdZ
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd
      exact absurd hodd (by norm_num)
  have hdvd : orderOf (u * t) ∣ f := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hxone
  have hne1 : orderOf (u * t) ≠ 1 := by
    intro h1
    have h2 : u * t = 1 := orderOf_eq_one_iff.mp h1
    have h3 : t = u := by
      calc t = u⁻¹ * (u * t) := by group
        _ = u⁻¹ := by rw [h2, mul_one]
        _ = u := inv_eq_of_mul_eq_one_right hu2
    exact h.notMem (h3 ▸ hu.1)
  rcases hfprime.eq_one_or_self_of_dvd (orderOf (u * t)) hdvd with h1 | h1
  · exact absurd h1 hne1
  · rcases hf35 with h3 | h5
    · left; rw [h1, h3]
    · right; rw [h1, h5]

end Work.NormalComplement.Sec5Fix
