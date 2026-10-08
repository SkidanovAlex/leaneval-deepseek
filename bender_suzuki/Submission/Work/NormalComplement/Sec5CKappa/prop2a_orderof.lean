import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.appIII
import Submission.Work.NormalComplement.sec5_prop2a
import Submission.Work.NormalComplement.sec5f_setup
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.NormalComplement.involutions_eq_of_odd_index
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.NormalComplement.p2a_appIII_cyclic
import Submission.Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
import Submission.Work.ThreePoints.P3NeBot.app3_1
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.PSU3.StageA.lemma2cAux
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.Sec5CKappa

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

variable {G : Type} [Group G] [Finite G]
  {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- `N_G(V)/K`, where `V = centD H t` and `K` is the kernel of the action of `N_G(V)` on `Ω_V`. -/
abbrev QuotNN (H : Subgroup G) (t : G) : Type :=
  ↥(Sec5f.NN H t) ⧸ Sec5f.KK H t

/-! ## Elementary facts about the configuration -/

/-- `3 ≤ |Ω_V|` for `V = centD H t`. -/
lemma p2a_three_le_fixedPts_V (h : Design.Setup5 G H t W p P A r) :
    3 ≤ (fixedPts H (centD H t)).ncard :=
  Work.ThreePoints.three_le_ncard_fixedPts_of_le_centD h.se h.invol h.notMem le_rfl

/-- `t ∈ N_G(V)`. -/
lemma p2a_t_mem_NN (h : Design.Setup5 G H t W p P A r) : t ∈ Sec5f.NN H t := by
  refine Subgroup.centralizer_le_normalizer _ (fun y hy => ?_)
  rw [Work.ThreePoints.centD_eq] at hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy).2

/-- `u ∈ N_G(V)` for an involution `u ∈ H` centralising `V`. -/
lemma p2a_mem_NN_of_mem_centralizer {u : G}
    (huC : u ∈ Subgroup.centralizer (centD H t : Set G)) : u ∈ Sec5f.NN H t :=
  Subgroup.centralizer_le_normalizer _ huC

/-- An involution of `H ⊓ N_G(V)` centralises `V`.  Its involutions are the involutions of
`O^{2'}(C_G(V)) ⊓ H` (`involutions_eq_of_odd_index`), and those centralise `V`. -/
lemma p2a_mem_centralizer_of_involution_NN (hFT : FeitThompsonProp) (hC : ThmCProp)
    (h : Design.Setup5 G H t W p P A r) {x : G}
    (hx : x ∈ H ⊓ Sec5f.NN H t) (hx2 : orderOf x = 2) :
    x ∈ Subgroup.centralizer (centD H t : Set G) := by
  classical
  obtain ⟨S, hSpg, hSle, hSidx, hSnorm, hSD, hSsup, -⟩ := p2a_p3_data hFT hC h
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  have hcard : Nat.card ↥(H ⊓ Sec5f.NN H t) =
      Nat.card ↥S * Nat.card ↥(twoPoint H t ⊓ Sec5f.NN H t) := by
    have hKle : (twoPoint H t ⊓ Sec5f.NN H t) ≤ Subgroup.normalizer (S : Set G) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨hy1a, -⟩ := Subgroup.mem_inf.mp hy1
      exact hSnorm (Subgroup.mem_inf.mpr ⟨hy1a, hy2⟩)
    have hinf : S ⊓ (twoPoint H t ⊓ Sec5f.NN H t) = ⊥ := by
      refine le_antisymm (fun z hz => ?_) bot_le
      have hz' : z ∈ S ⊓ twoPoint H t :=
        ⟨(Subgroup.mem_inf.mp hz).1, (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hz).2).1⟩
      rwa [hSD] at hz'
    have hprod := card_sup_mul_card_inf (H := S) (K := twoPoint H t ⊓ Sec5f.NN H t) hKle
    rw [hSsup, hinf, Subgroup.card_bot, mul_one] at hprod
    exact hprod
  have heq := Work.NormalComplement.involutions_eq_of_odd_index
    (F := Work.ThreePoints.p3F (centD H t)) (N := Sec5f.NN H t) (H := H) (S := S)
    (D := twoPoint H t) hSsup hSnorm hcard hDodd hSle
    (Work.ThreePoints.p3F_le_normalizer _)
  have hx' : x ∈ Work.ThreePoints.p3F (centD H t) ⊓ H := by
    have h1 : x ∈ {x : G | x ∈ H ⊓ Sec5f.NN H t ∧ orderOf x = 2} := ⟨hx, hx2⟩
    rw [← heq] at h1
    exact h1.1
  exact Work.ThreePoints.p3F_le_centralizer _ hx'.1

/-- **The point stabiliser `N_G(V) ⊓ H` is strongly embedded in `N_G(V)`** (Ch. II §4 Prop. 1 (b)
at `X = V`). -/
lemma p2a_NN_strong (hC4 : ChIIFourProp) (h : Design.Setup5 G H t W p P A r) :
    IsStronglyEmbedded ((Sec5f.NN H t ⊓ H).subgroupOf (Sec5f.NN H t)) := by
  have h3 : 3 ≤ (fixedPts H (centD H t)).ncard := p2a_three_le_fixedPts_V h
  have hinv : involutions (Subgroup.centralizer (centD H t : Set G) : Set G) ⊆
      (Sec5f.NN H t : Set G) := fun x hx => Subgroup.centralizer_le_normalizer _ hx.1
  have hVH : centD H t ≤ Submission.Blueprint.conj 1 H := by
    rw [Work.ThreePoints.conj_one]
    exact (Work.ThreePoints.le_of_le_centD (le_refl (centD H t))).1
  have hres := (hC4 G h.sit H h.se t h.invol h.notMem).1 (centD H t)
    (Sec5f.NN H t) h3 hinv le_rfl 1 hVH
  simpa [Sec5f.NN, Work.ThreePoints.conj_one] using hres

/-! ## `|S| ∈ {2,4,8}` for the Sylow `2`-subgroup `S` of `O^{2'}(C_G(V)) ⊓ H` -/

/-- **Peterfalvi I Ch. III §5 Prop. 2 (a), the `2`-group count** (p. 184): `S` has exactly one
involution and exponent dividing `4`, so `|S| ∈ {2,4,8}`. -/
lemma p2a_S_card (hFT : FeitThompsonProp) (hC : ThmCProp) (hC4 : ChIIFourProp)
    (hP3 : ChIIFourP3SubnormalProp) (hMF2 : BenderModelFacts2Prop)
    (h : Design.Setup5 G H t W p P A r) {S : Subgroup G}
    (hSpg : IsPGroup 2 S)
    (hSle : S ≤ Work.ThreePoints.p3F (centD H t) ⊓ H)
    (hSidx : ¬ 2 ∣ (S.subgroupOf (Work.ThreePoints.p3F (centD H t) ⊓ H)).index)
    (hSnorm : H ⊓ Sec5f.NN H t ≤ Subgroup.normalizer (S : Set G))
    (hSD : S ⊓ twoPoint H t = ⊥)
    (hSsup : S ⊔ (twoPoint H t ⊓ Sec5f.NN H t) = H ⊓ Sec5f.NN H t) :
    (S : Set G).ncard = 2 ∨ (S : Set G).ncard = 4 ∨ (S : Set G).ncard = 8 := by
  classical
  obtain ⟨u, hu, huniq⟩ := sec5_setup_invol hFT hC4 hP3 h
  have huH : u ∈ H := hu.1
  have hu2 : orderOf u = 2 := hu.2.1
  have huC : u ∈ Subgroup.centralizer (centD H t : Set G) := hu.2.2
  have huF : u ∈ Work.ThreePoints.p3F (centD H t) :=
    Work.ThreePoints.mem_p3F_of_involution huC hu2
  -- `S` is the unique Sylow `2`-subgroup of `p3F V ⊓ H`
  have hFleNN : Work.ThreePoints.p3F (centD H t) ≤ Sec5f.NN H t :=
    Work.ThreePoints.p3F_le_normalizer _
  have hNormS : Work.ThreePoints.p3F (centD H t) ⊓ H ≤ Subgroup.normalizer (S : Set G) :=
    fun x hx => hSnorm (Subgroup.mem_inf.mpr ⟨hx.2, hFleNN hx.1⟩)
  have hSnormal : (S.subgroupOf (Work.ThreePoints.p3F (centD H t) ⊓ H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSle).mpr hNormS
  have hodd : Odd (S.subgroupOf (Work.ThreePoints.p3F (centD H t) ⊓ H)).index := by
    rcases Nat.even_or_odd (S.subgroupOf (Work.ThreePoints.p3F (centD H t) ⊓ H)).index with h | h
    · exact absurd (even_iff_two_dvd.mp h) hSidx
    · exact h
  haveI := hSnormal
  have huFH : u ∈ Work.ThreePoints.p3F (centD H t) ⊓ H := Subgroup.mem_inf.mpr ⟨huF, huH⟩
  have huS : u ∈ S := by
    have hmem : (⟨u, huFH⟩ : ↥(Work.ThreePoints.p3F (centD H t) ⊓ H)) ∈
        S.subgroupOf (Work.ThreePoints.p3F (centD H t) ⊓ H) :=
      Work.NormalComplement.mem_of_orderOf_eq_two_of_odd_index hodd
        ((Subgroup.orderOf_coe (⟨u, huFH⟩ : ↥(Work.ThreePoints.p3F (centD H t) ⊓ H))).symm.trans
          hu2)
    exact Subgroup.mem_subgroupOf.mp hmem
  -- the unique involution
  have huniqS : (involutions (S : Set G)).ncard = 1 := by
    have hsub : involutions (S : Set G) ⊆ ({u} : Set G) := by
      intro x hx
      rw [involutions, Set.mem_setOf_eq] at hx
      obtain ⟨hxS, hx2⟩ := hx
      have hxC : x ∈ Subgroup.centralizer (centD H t : Set G) :=
        Work.ThreePoints.p3F_le_centralizer _ (hSle hxS).1
      rw [huniq x ⟨(hSle hxS).2, hx2, hxC⟩]
      exact Set.mem_singleton u
    have hone : u ∈ involutions (S : Set G) := by
      rw [involutions, Set.mem_setOf_eq]; exact ⟨huS, hu2⟩
    have heq : involutions (S : Set G) = {u} :=
      le_antisymm hsub (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hone)
    rw [heq, Set.ncard_singleton]
  -- the exponent divides `4`
  have hexp : ∀ x ∈ S, x ^ 4 = 1 := by
    intro x hxS
    have hxH : x ∈ H := (hSle hxS).2
    have hxC : x ∈ Subgroup.centralizer (A : Set G) :=
      Subgroup.centralizer_le h.A_le (Work.ThreePoints.p3F_le_centralizer _ (hSle hxS).1)
    obtain ⟨k, hk⟩ := hSpg.exists_card_dvd_pow
    have hdvd : orderOf x ∣ 2 ^ k := (Subgroup.orderOf_dvd_natCard S hxS).trans hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hxF : x ∈ Work.ThreePoints.p3F A := by
      rw [Work.ThreePoints.mem_p3F]
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      refine Work.PSU3.StageA.mem_oddResidual_of_orderOf_eq_two_pow (k := j) ?_
      rw [← Subgroup.orderOf_coe (⟨x, hxC⟩ : ↥(Subgroup.centralizer (A : Set G)))]
      exact hj
    exact p2a_pow_four hFT hC hC4 hMF2 h x hxH hxF ⟨j, hj⟩
  -- `|S| ∈ {2,4,8}`
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard_pos : 2 ≤ Nat.card ↥S := by
    have h2 : 2 ∣ Nat.card ↥S := by rw [← hu2]; exact Subgroup.orderOf_dvd_natCard S huS
    exact Nat.le_of_dvd Nat.card_pos h2
  have hle8 : Nat.card ↥S ≤ 8 := by
    have huniqinv : Work.BrauerSuzuki.HasUniqueInvolution ↥S :=
      p2a_appIII_hasUniqueInvolution_of_ncard_eq_one huniqS
    rcases Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution hSpg huniqinv with
      hcyc | hgen
    · exact le_trans (p2a_appIII_cyclic_card_le_four hcyc hexp) (by norm_num)
    · exact le_of_eq (p2a_appIII_genQuaternion_card_eq_eight hgen hexp)
  obtain ⟨k, hk⟩ := hSpg.exists_card_eq
  rw [p2a_appIII_ncard_sub_eq_natCard S, hk]
  have h2k : 2 ≤ 2 ^ k := by rw [← hk]; exact hcard_pos
  have h8k : 2 ^ k ≤ 8 := by rw [← hk]; exact hle8
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp only [pow_zero] at h2k; omega
    · omega
  have hk3 : k ≤ 3 := by
    by_contra hc
    push_neg at hc
    have h16 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    have : 16 ≤ 2 ^ k := by norm_num at h16 ⊢; exact h16
    omega
  interval_cases k <;> norm_num

/-! ## `N_G(V)` has `2`-rank `1` -/

/-- **A finite group with a strongly embedded subgroup whose involution is unique has 2-rank
one.**  All involutions of `X` are conjugate (`involutions_conj_of_stronglyEmbedded`), so a
four-group can be conjugated so that one of its involutions is the unique involution `u` of `L`;
the other one then lies outside `L` (`L` has no other involution) and centralises `u`, contradicting
`Odd |L ⊓ L^a|`. -/
lemma p2a_noFourGroup_of_stronglyEmbedded_unique_involution {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (hse : IsStronglyEmbedded L)
    (hun : ∃! u : X, u ∈ L ∧ orderOf u = 2) : ¬ HasFourGroup X := by
  classical
  obtain ⟨u, ⟨huL, hu2⟩, huniq⟩ := hun
  rintro ⟨a, b, ha2, hb2, hane, hcomm⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (Work.ThreePoints.involutions_conj_of_stronglyEmbedded hse hb2 hu2)
  set a' : X := c * a * c⁻¹ with ha'def
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha'2 : orderOf a' = 2 := by
    refine Work.ThreePoints.orderOf_eq_two_of ?_ ?_
    · intro h1
      have : a = 1 := by
        have h2 := congrArg (fun z => c⁻¹ * z * c) h1
        simpa [ha'def, mul_assoc] using h2
      rw [this] at ha2
      exact absurd ha2 (by norm_num)
    · rw [ha'def]
      calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
        _ = 1 := by rw [haa]; group
  have ha'ne : a' ≠ u := by
    intro hcon
    apply hane
    have h1 : c * a * c⁻¹ = c * b * c⁻¹ := by rw [← ha'def]; exact hcon.trans hc.symm
    have h2 := congrArg (fun z => c⁻¹ * z * c) h1
    simpa [mul_assoc] using h2
  have ha'notL : a' ∉ L := fun hle => ha'ne (huniq a' ⟨hle, ha'2⟩)
  have ha'comm : a' * u = u * a' := by
    have h2 : c * a * c⁻¹ * (c * b * c⁻¹) = c * b * c⁻¹ * (c * a * c⁻¹) := by
      calc c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
        _ = c * (b * a) * c⁻¹ := by rw [hcomm]
        _ = c * b * c⁻¹ * (c * a * c⁻¹) := by group
    rw [ha'def, ← hc]
    exact h2
  have hodd := hse.2.2 a' ha'notL
  have hmem : u ∈ L ⊓ L.map (MulAut.conj a').toMonoidHom := by
    refine ⟨huL, Subgroup.mem_map.mpr ⟨u, huL, ?_⟩⟩
    show a' * u * a'⁻¹ = u
    calc a' * u * a'⁻¹ = u * a' * a'⁻¹ := by rw [ha'comm]
      _ = u := by group
  have h2dvd : 2 ∣ Nat.card ↥(L ⊓ L.map (MulAut.conj a').toMonoidHom) := by
    rw [← hu2]
    exact Subgroup.orderOf_dvd_natCard (L ⊓ L.map (MulAut.conj a').toMonoidHom) hmem
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)

/-- **`N_G(V)` has 2-rank one.** -/
lemma p2a_noFourGroup_NN (hFT : FeitThompsonProp) (hC : ThmCProp) (hC4 : ChIIFourProp)
    (hP3 : ChIIFourP3SubnormalProp) (hIII : AppIIIProp) (hMF2 : BenderModelFacts2Prop)
    (h : Design.Setup5 G H t W p P A r) :
    ¬ HasFourGroup ↥(Sec5f.NN H t) := by
  classical
  obtain ⟨u, hu, huniq⟩ := sec5_setup_invol hFT hC4 hP3 h
  have huNN : u ∈ Sec5f.NN H t := p2a_mem_NN_of_mem_centralizer hu.2.2
  have hkey : ∀ x : G, x ∈ H ⊓ Sec5f.NN H t → orderOf x = 2 → x = u := by
    intro x hx hx2
    exact huniq x ⟨(Subgroup.mem_inf.mp hx).1, hx2,
      p2a_mem_centralizer_of_involution_NN hFT hC h hx hx2⟩
  refine p2a_noFourGroup_of_stronglyEmbedded_unique_involution (p2a_NN_strong hC4 h) ?_
  refine ⟨⟨u, huNN⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [Subgroup.mem_subgroupOf]; exact ⟨huNN, hu.1⟩
  · rw [← Subgroup.orderOf_coe (⟨u, huNN⟩ : ↥(Sec5f.NN H t))]; exact hu.2.1
  · intro x hx
    have hxK : ((x : ↥(Sec5f.NN H t)) : G) ∈ H ⊓ Sec5f.NN H t := by
      have h := Subgroup.mem_subgroupOf.mp hx.1
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h).2, (Subgroup.mem_inf.mp h).1⟩
    have hxG : orderOf ((x : ↥(Sec5f.NN H t)) : G) = 2 :=
      (Subgroup.orderOf_coe x).trans hx.2
    exact Subtype.ext (hkey (x : G) hxK hxG)

/-! ## The point stabiliser is maximal -/

/-- The point stabiliser `N_G(V) ⊓ H` is maximal in `N_G(V)` (`2`-transitivity of `N_G(V)` on
`Ω_V`). -/
lemma p2a_isCoatom_stabilizer (hFT : FeitThompsonProp) (hC : ThmCProp) (hC4 : ChIIFourProp)
    (hP3 : ChIIFourP3SubnormalProp) (hIII : AppIIIProp) (hMF2 : BenderModelFacts2Prop)
    (h : Design.Setup5 G H t W p P A r) :
    IsCoatom ((Sec5f.NN H t ⊓ H).subgroupOf (Sec5f.NN H t)) := by
  classical
  have hBrSz : BrauerSuzukiProp := Work.BrauerSuzuki.brauerSuzuki
  have hZJ : GlaubermanZJProp := Work.ThmF.ChV12.glaubermanZJ_free
  have hA : ThmAProp := Work.DoubleTransitivity.Sec7.ThmA hFT hZJ hBrSz
  have hMod : ModelFactsProp := Work.Models.models hFT
  have hPkg : Work.ThreePoints.P3Pkg H t (centD H t) :=
    Work.ThreePoints.p3pkg hFT hC hA hZJ hBrSz hMod h.sit h.se h.invol h.notMem
      (centD H t) le_rfl ⟨A, h.A_ne, p2a_IsSubnormalIn_A_V h, p2a_HasNonTrivialNK_A h⟩
  obtain ⟨-, h2t⟩ := hPkg
  have h3 : 3 ≤ (fixedPts H (centD H t)).ncard := p2a_three_le_fixedPts_V h
  have hmaxI : ∀ M : Subgroup G, Sec5f.NN H t ⊓ H ≤ M → M ≤ Sec5f.NN H t →
      M = Sec5f.NN H t ⊓ H ∨ M = Sec5f.NN H t := fun M hle hle' =>
    Work.ThreePoints.P3NeBot.maximal_of_twoTransitive (H := H) (F := Sec5f.NN H t) (M := M)
      (X := centD H t) (Work.ThreePoints.le_of_le_centD le_rfl).1 le_rfl h3 h2t hle hle'
  rw [SetLike.isCoatom_iff]
  refine ⟨?_, ?_⟩
  · intro htop
    have htH : t ∈ H := by
      have : (⟨t, p2a_t_mem_NN h⟩ : ↥(Sec5f.NN H t)) ∈
          (Sec5f.NN H t ⊓ H).subgroupOf (Sec5f.NN H t) := by
        rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2
    exact h.notMem htH
  · intro M g hle hgK hgM
    have hle' : Sec5f.NN H t ⊓ H ≤ M.map (Sec5f.NN H t).subtype := by
      intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x, (Subgroup.mem_inf.mp hx).1⟩, ?_, rfl⟩
      exact hle (by rw [Subgroup.mem_subgroupOf]; exact hx)
    rcases hmaxI (M.map (Sec5f.NN H t).subtype) hle' (Subgroup.map_subtype_le M) with
      hcase | hcase
    · exfalso
      apply hgK
      rw [Subgroup.mem_subgroupOf]
      have : (g : G) ∈ M.map (Sec5f.NN H t).subtype :=
        Subgroup.mem_map.mpr ⟨g, hgM, rfl⟩
      rwa [hcase] at this
    · refine le_antisymm le_top fun x _ => ?_
      have : (x : G) ∈ M.map (Sec5f.NN H t).subtype := by rw [hcase]; exact x.2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp this
      rwa [Subtype.ext hyx] at hy

/-! ## Appendix III applied to `N_G(V)` -/

/-- `N_G(V)/K` acts transitively on `Ω_V` (Ch. II §4 Prop. 3). -/
lemma p2a_quot_transitive (hFT : FeitThompsonProp) (hC : ThmCProp)
    (h : Design.Setup5 G H t W p P A r) :
    MulAction.IsPretransitive (QuotNN H t) (Sec5f.Omega H t) := by
  classical
  have hBrSz : BrauerSuzukiProp := Work.BrauerSuzuki.brauerSuzuki
  have hZJ : GlaubermanZJProp := Work.ThmF.ChV12.glaubermanZJ_free
  have hA : ThmAProp := Work.DoubleTransitivity.Sec7.ThmA hFT hZJ hBrSz
  have hMod : ModelFactsProp := Work.Models.models hFT
  have hPkg : Work.ThreePoints.P3Pkg H t (centD H t) :=
    Work.ThreePoints.p3pkg hFT hC hA hZJ hBrSz hMod h.sit h.se h.invol h.notMem
      (centD H t) le_rfl ⟨A, h.A_ne, p2a_IsSubnormalIn_A_V h, p2a_HasNonTrivialNK_A h⟩
  obtain ⟨-, h2t⟩ := hPkg
  refine ⟨fun c d => ?_⟩
  obtain ⟨g, hg, hgc⟩ := h2t.isTransitiveOnSub (c : G ⧸ H) c.2 (d : G ⧸ H) d.2
  exact ⟨QuotientGroup.mk' (Sec5f.KK H t) ⟨g, hg⟩, Subtype.ext hgc⟩

/-- **Appendix III applied to `N_G(V)/K`** (`K` the kernel of its action on `Ω_V`). -/
lemma p2a_appIII_quotient_data (hFT : FeitThompsonProp) (hC : ThmCProp) (hC4 : ChIIFourProp)
    (hP3 : ChIIFourP3SubnormalProp) (hIII : AppIIIProp) (hMF2 : BenderModelFacts2Prop)
    (h : Design.Setup5 G H t W p P A r)
    (h4 : ¬ HasFourGroup ↥(Sec5f.NN H t))
    (hcoat : IsCoatom ((Sec5f.NN H t ⊓ H).subgroupOf (Sec5f.NN H t))) :
    ∃ (f : ℕ) (Q : Subgroup (QuotNN H t)),
      f.Prime ∧ Q.Normal ∧ Q ≠ ⊥ ∧ (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧
      (∀ x ∈ Q, x ^ f = 1) ∧
      Q ⊓ MulAction.stabilizer (QuotNN H t) (Sec5f.ptV H t) = ⊥ ∧
      Q ⊔ MulAction.stabilizer (QuotNN H t) (Sec5f.ptV H t) = ⊤ ∧
      (∀ x y : QuotNN H t,
        orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y ∈ Q ∧ orderOf (x * y) = f) := by
  classical
  have hBrSz : BrauerSuzukiProp := Work.BrauerSuzuki.brauerSuzuki
  have hZJ : GlaubermanZJProp := Work.ThmF.ChV12.glaubermanZJ_free
  have hA : ThmAProp := Work.DoubleTransitivity.Sec7.ThmA hFT hZJ hBrSz
  have hMod : ModelFactsProp := Work.Models.models hFT
  have hPkg : Work.ThreePoints.P3Pkg H t (centD H t) :=
    Work.ThreePoints.p3pkg hFT hC hA hZJ hBrSz hMod h.sit h.se h.invol h.notMem
      (centD H t) le_rfl ⟨A, h.A_ne, p2a_IsSubnormalIn_A_V h, p2a_HasNonTrivialNK_A h⟩
  obtain ⟨-, h2t⟩ := hPkg
  -- the action of `N_G(V)/K` on `Ω_V` is transitive
  have htrans : MulAction.IsPretransitive (QuotNN H t) (Sec5f.Omega H t) := by
    refine ⟨fun c d => ?_⟩
    obtain ⟨g, hg, hgc⟩ := h2t.isTransitiveOnSub (c : G ⧸ H) c.2 (d : G ⧸ H) d.2
    exact ⟨QuotientGroup.mk' (Sec5f.KK H t) ⟨g, hg⟩, Subtype.ext hgc⟩
  -- it is faithful
  have hfaith : ∀ g : QuotNN H t, (∀ x : Sec5f.Omega H t, g • x = x) → g = 1 := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Sec5f.KK H t) g
    have hx : x ∈ Sec5f.KK H t := by
      rw [Sec5f.KK, MonoidHom.mem_ker]
      refine Equiv.ext (fun ω => ?_)
      show x • ω = ω
      have h3 := hg ω
      rwa [Sec5f.quotient_smul_mk] at h3
    have hmem : x ∈ (QuotientGroup.mk' (Sec5f.KK H t)).ker :=
      (QuotientGroup.ker_mk' (Sec5f.KK H t)).symm ▸ hx
    exact MonoidHom.mem_ker.mp hmem
  -- `|K|` is odd
  have hKKodd : Odd (Nat.card ↥(Sec5f.KK H t)) := by
    have h1 : Nat.card ↥(Sec5f.KK H t) =
        Nat.card ↥((Sec5f.KK H t).map (Sec5f.NN H t).subtype) :=
      (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
    rw [h1]
    exact Odd.of_dvd_nat (h.se.2.2 t h.notMem)
      (Subgroup.card_dvd_of_le (Sec5f.KK_map_le_twoPoint (H := H) (t := t)))
  have h4q : ¬ HasFourGroup (QuotNN H t) :=
    Work.ThreePoints.P3NeBot.not_hasFourGroup_quotient (Sec5f.KK H t) hKKodd h4
  -- strong embedding and maximality pass to the quotient
  have hSEq : IsStronglyEmbedded
      (MulAction.stabilizer (QuotNN H t) (Sec5f.ptV H t)) := by
    rw [Sec5f.stabilizer_ptV_quot]
    exact isStronglyEmbedded_map_of_surjective (QuotientGroup.mk' (Sec5f.KK H t))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hKKodd
      Sec5f.KK_le_subgroupOf (p2a_NN_strong hC4 h)
  have hcoatq : IsCoatom (MulAction.stabilizer (QuotNN H t) (Sec5f.ptV H t)) := by
    rw [Sec5f.stabilizer_ptV_quot]
    exact Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le
      (QuotientGroup.mk'_surjective (Sec5f.KK H t)) hcoat
      ((QuotientGroup.ker_mk' (Sec5f.KK H t)).trans_le Sec5f.KK_le_subgroupOf)
  obtain ⟨f, Q, hf, hQn, hQne, hQab, hQexp, hQinf, hQsup, -, hclause, -, -⟩ :=
    hIII (QuotNN H t) (Sec5f.Omega H t) (Sec5f.ptV H t) htrans hfaith h4q hSEq hcoatq
  exact ⟨f, Q, hf, hQn, hQne, hQab, hQexp, hQinf, hQsup, hclause⟩

/-! ## The prime `f` and the kernel subgroup `Z` -/

/-- **Peterfalvi I Ch. III §5 Prop. 2 (a)**: there are a prime `f` and a subgroup `Z ≤ D`
normalised by `N_G(V)` with `f ∣ |Ω_V|` and `(u t) ^ f ∈ Z` for every involution `u ∈ H`
centralising `V`. -/
lemma p2a_appIII_prime_data (hFT : FeitThompsonProp) (hC : ThmCProp) (hC4 : ChIIFourProp)
    (hP3 : ChIIFourP3SubnormalProp) (hIII : AppIIIProp) (hMF2 : BenderModelFacts2Prop)
    (h : Design.Setup5 G H t W p P A r)
    (h4 : ¬ HasFourGroup ↥(Sec5f.NN H t))
    (hcoat : IsCoatom ((Sec5f.NN H t ⊓ H).subgroupOf (Sec5f.NN H t))) :
    ∃ (f : ℕ) (Z : Subgroup G), f.Prime ∧ f ∣ (fixedPts H (centD H t)).ncard ∧
      Z ≤ twoPoint H t ∧
      Sec5f.NN H t ≤ Subgroup.normalizer (Z : Set G) ∧
      ∀ u : G, u ∈ H → orderOf u = 2 →
        u ∈ Subgroup.centralizer (centD H t : Set G) → (u * t) ^ f ∈ Z := by
  classical
  obtain ⟨f, Q, hf, hQn, hQne, hQab, hQexp, hQinf, hQsup, hclause⟩ :=
    p2a_appIII_quotient_data hFT hC hC4 hP3 hIII hMF2 h h4 hcoat
  haveI : Q.Normal := hQn
  haveI htransQ : MulAction.IsPretransitive (QuotNN H t) (Sec5f.Omega H t) :=
    p2a_quot_transitive hFT hC h
  -- `|Q| = |Ω_V|`
  have hcardQ : Nat.card ↥Q = (fixedPts H (centD H t)).ncard := by
    have hstab : MulAction.stabilizer (QuotNN H t) (Sec5f.ptV H t) =
        ((Sec5f.NN H t ⊓ H).subgroupOf (Sec5f.NN H t)).map
          (QuotientGroup.mk' (Sec5f.KK H t)) :=
      Sec5f.stabilizer_ptV_quot
    let φ : ↥Q → Sec5f.Omega H t := fun q => (q : QuotNN H t) • Sec5f.ptV H t
    have hφinj : Function.Injective φ := by
      intro q₁ q₂ hq
      have hq' : (q₁ : QuotNN H t) • Sec5f.ptV H t = (q₂ : QuotNN H t) • Sec5f.ptV H t := hq
      have h1 : ((q₁ : QuotNN H t)⁻¹ * (q₂ : QuotNN H t)) • Sec5f.ptV H t =
          Sec5f.ptV H t := by
        rw [mul_smul, ← hq', inv_smul_smul]
      have h2 : (q₁ : QuotNN H t)⁻¹ * (q₂ : QuotNN H t) ∈
          MulAction.stabilizer (QuotNN H t) (Sec5f.ptV H t) :=
        MulAction.mem_stabilizer_iff.mpr h1
      have h3 : (q₁ : QuotNN H t)⁻¹ * (q₂ : QuotNN H t) ∈
          Q ⊓ MulAction.stabilizer (QuotNN H t) (Sec5f.ptV H t) :=
        ⟨Q.mul_mem (Q.inv_mem q₁.2) q₂.2, h2⟩
      rw [hQinf] at h3
      have h4 : (q₁ : QuotNN H t)⁻¹ * (q₂ : QuotNN H t) = 1 := Subgroup.mem_bot.mp h3
      have h5 : (q₂ : QuotNN H t) = (q₁ : QuotNN H t) := by
        have := congrArg (fun x => (q₁ : QuotNN H t) * x) h4
        simpa [mul_assoc] using this
      exact Subtype.ext h5.symm
    have hφsurj : Function.Surjective φ := by
      intro ω
      obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := QuotNN H t)
        (α := Sec5f.Omega H t) (Sec5f.ptV H t) ω
      have hmem : g ∈ Q ⊔ MulAction.stabilizer (QuotNN H t) (Sec5f.ptV H t) := by
        rw [hQsup]; exact Subgroup.mem_top g
      obtain ⟨q, hq, s, hs, hqs⟩ := (Subgroup.mem_sup_of_normal_left (s := Q)).mp hmem
      refine ⟨⟨q, hq⟩, ?_⟩
      show (q : QuotNN H t) • Sec5f.ptV H t = ω
      have hsv : s • Sec5f.ptV H t = Sec5f.ptV H t := MulAction.mem_stabilizer_iff.mp hs
      calc (q : QuotNN H t) • Sec5f.ptV H t = (q * s) • Sec5f.ptV H t := by rw [mul_smul, hsv]
        _ = g • Sec5f.ptV H t := by rw [hqs]
        _ = ω := hg
    exact (Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)).trans
      (p2a_natCard_set_eq_ncard (fixedPts H (centD H t)))
  -- `f ∣ |Ω_V|`
  have hfdvd : f ∣ (fixedPts H (centD H t)).ncard := by
    rw [← hcardQ]
    obtain ⟨y, hyQ, hy1⟩ : ∃ y ∈ Q, y ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hQne (le_antisymm (fun x hx => Subgroup.mem_bot.mpr (hcon x hx)) bot_le)
    have h1 : orderOf y ∣ f := orderOf_dvd_iff_pow_eq_one.mpr (hQexp y hyQ)
    have h2 : orderOf y = f := by
      rcases (Nat.dvd_prime hf).mp h1 with h' | h'
      · exact absurd (orderOf_eq_one_iff.mp h') hy1
      · exact h'
    rw [← h2]
    exact Subgroup.orderOf_dvd_natCard Q hyQ
  refine ⟨f, (Sec5f.KK H t).map (Sec5f.NN H t).subtype, hf, hfdvd,
    Sec5f.KK_map_le_twoPoint (H := H) (t := t), ?_, ?_⟩
  · -- `Z` is normalised by `N_G(V)`
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp hz
      rw [← hkz]
      exact Subgroup.mem_map_of_mem (Sec5f.NN H t).subtype
        ((inferInstance : (Sec5f.KK H t).Normal).conj_mem k hk ⟨n, hn⟩)
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp hz
      have hkz' : ((k : ↥(Sec5f.NN H t)) : G) = n * z * n⁻¹ := hkz
      have hw : (⟨n, hn⟩⁻¹ * k * ⟨n, hn⟩ : ↥(Sec5f.NN H t)) ∈ Sec5f.KK H t := by
        simpa using (inferInstance : (Sec5f.KK H t).Normal).conj_mem k hk ⟨n, hn⟩⁻¹
      have hval : ((⟨n, hn⟩⁻¹ * k * ⟨n, hn⟩ : ↥(Sec5f.NN H t)) : G) = z := by
        have hcoe : ((⟨n, hn⟩⁻¹ * k * ⟨n, hn⟩ : ↥(Sec5f.NN H t)) : G) =
            n⁻¹ * ((k : ↥(Sec5f.NN H t)) : G) * n := by simp [Subgroup.coe_mul]
        rw [hcoe, hkz']
        group
      rw [← hval]
      exact Subgroup.mem_map_of_mem (Sec5f.NN H t).subtype hw
  · -- the element `u * t`
    intro u huH hu2 huC
    have huNN : u ∈ Sec5f.NN H t := p2a_mem_NN_of_mem_centralizer huC
    have htNN : t ∈ Sec5f.NN H t := p2a_t_mem_NN h
    have huord : orderOf (⟨u, huNN⟩ : ↥(Sec5f.NN H t)) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨u, huNN⟩ : ↥(Sec5f.NN H t))]; exact hu2
    have htord : orderOf (⟨t, htNN⟩ : ↥(Sec5f.NN H t)) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨t, htNN⟩ : ↥(Sec5f.NN H t))]; exact h.invol
    have hub2 : orderOf (QuotientGroup.mk' (Sec5f.KK H t) ⟨u, huNN⟩) = 2 := by
      have hdvd := orderOf_map_dvd (QuotientGroup.mk' (Sec5f.KK H t))
        (⟨u, huNN⟩ : ↥(Sec5f.NN H t))
      rw [huord] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
      · exfalso
        have hker : (⟨u, huNN⟩ : ↥(Sec5f.NN H t)) ∈ (QuotientGroup.mk' (Sec5f.KK H t)).ker :=
          MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h')
        have hmem : (⟨u, huNN⟩ : ↥(Sec5f.NN H t)) ∈ Sec5f.KK H t :=
          (QuotientGroup.ker_mk' (Sec5f.KK H t)) ▸ hker
        have hmemMap : u ∈ (Sec5f.KK H t).map (Sec5f.NN H t).subtype :=
          Subgroup.mem_map_of_mem (Sec5f.NN H t).subtype hmem
        have hD : u ∈ twoPoint H t := Sec5f.KK_map_le_twoPoint (H := H) (t := t) hmemMap
        have h2dvd : 2 ∣ Nat.card ↥(twoPoint H t) := by
          rw [← hu2]; exact Subgroup.orderOf_dvd_natCard _ hD
        exact (Nat.not_even_iff_odd.mpr (h.se.2.2 t h.notMem)) (even_iff_two_dvd.mpr h2dvd)
      · exact h'
    have htb2 : orderOf (QuotientGroup.mk' (Sec5f.KK H t) ⟨t, htNN⟩) = 2 := by
      have hdvd := orderOf_map_dvd (QuotientGroup.mk' (Sec5f.KK H t))
        (⟨t, htNN⟩ : ↥(Sec5f.NN H t))
      rw [htord] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
      · exfalso
        have hker : (⟨t, htNN⟩ : ↥(Sec5f.NN H t)) ∈ (QuotientGroup.mk' (Sec5f.KK H t)).ker :=
          MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h')
        have hmem : (⟨t, htNN⟩ : ↥(Sec5f.NN H t)) ∈ Sec5f.KK H t :=
          (QuotientGroup.ker_mk' (Sec5f.KK H t)) ▸ hker
        have hmemMap : t ∈ (Sec5f.KK H t).map (Sec5f.NN H t).subtype :=
          Subgroup.mem_map_of_mem (Sec5f.NN H t).subtype hmem
        have hD : t ∈ twoPoint H t := Sec5f.KK_map_le_twoPoint (H := H) (t := t) hmemMap
        exact h.notMem (Subgroup.mem_inf.mp hD).1
      · exact h'
    have hubne : QuotientGroup.mk' (Sec5f.KK H t) ⟨u, huNN⟩ ≠
        QuotientGroup.mk' (Sec5f.KK H t) ⟨t, htNN⟩ := by
      intro heq
      have hker : (QuotientGroup.mk' (Sec5f.KK H t))
          ((⟨u, huNN⟩ : ↥(Sec5f.NN H t))⁻¹ * ⟨t, htNN⟩) = 1 := by
        rw [map_mul, map_inv, heq, inv_mul_cancel]
      have hmem : (⟨u, huNN⟩ : ↥(Sec5f.NN H t))⁻¹ * ⟨t, htNN⟩ ∈ Sec5f.KK H t :=
        (QuotientGroup.ker_mk' (Sec5f.KK H t)) ▸ MonoidHom.mem_ker.mpr hker
      have hmemMap : (((⟨u, huNN⟩ : ↥(Sec5f.NN H t))⁻¹ * ⟨t, htNN⟩ :
          ↥(Sec5f.NN H t)) : G) ∈
          (Sec5f.KK H t).map (Sec5f.NN H t).subtype :=
        Subgroup.mem_map_of_mem (Sec5f.NN H t).subtype hmem
      have hD : (((⟨u, huNN⟩ : ↥(Sec5f.NN H t))⁻¹ * ⟨t, htNN⟩ : ↥(Sec5f.NN H t)) : G) ∈
          twoPoint H t :=
        Sec5f.KK_map_le_twoPoint (H := H) (t := t) hmemMap
      have huH' : u⁻¹ * t ∈ H := by simpa using (Subgroup.mem_inf.mp hD).1
      exact h.notMem (by
        have := H.mul_mem huH huH'
        rwa [mul_inv_cancel_left] at this)
    obtain ⟨hmem, hord⟩ := hclause _ _ hub2 htb2 hubne
    -- `(u * t)^f ∈ K`
    have hprod : (QuotientGroup.mk' (Sec5f.KK H t)
          (⟨u * t, (Sec5f.NN H t).mul_mem huNN htNN⟩ : ↥(Sec5f.NN H t))) =
        (QuotientGroup.mk' (Sec5f.KK H t) ⟨u, huNN⟩) *
          (QuotientGroup.mk' (Sec5f.KK H t) ⟨t, htNN⟩) := by
      rw [← map_mul]
      rfl
    have h1 : (QuotientGroup.mk' (Sec5f.KK H t)
        (⟨u * t, (Sec5f.NN H t).mul_mem huNN htNN⟩ : ↥(Sec5f.NN H t))) ^ f = 1 := by
      rw [hprod]
      have h2 := pow_orderOf_eq_one ((QuotientGroup.mk' (Sec5f.KK H t) ⟨u, huNN⟩) *
        (QuotientGroup.mk' (Sec5f.KK H t) ⟨t, htNN⟩))
      rwa [hord] at h2
    have h2 : (⟨u * t, (Sec5f.NN H t).mul_mem huNN htNN⟩ : ↥(Sec5f.NN H t)) ^ f ∈
        Sec5f.KK H t := by
      have hmem' : (QuotientGroup.mk' (Sec5f.KK H t))
          ((⟨u * t, (Sec5f.NN H t).mul_mem huNN htNN⟩ : ↥(Sec5f.NN H t)) ^ f) = 1 := by
        rw [map_pow]; exact h1
      exact (QuotientGroup.ker_mk' (Sec5f.KK H t)) ▸ MonoidHom.mem_ker.mpr hmem'
    exact Subgroup.mem_map.mpr ⟨_, h2, by simp⟩

/-! ## The main theorem -/

theorem prop2a_orderof (hFT : Submission.Blueprint.FeitThompsonProp)
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
  obtain ⟨S, hSpg, hSle, hSidx, hSnorm, hSD, hSsup, hcardS⟩ := p2a_p3_data hFT hC h
  -- `|S| ∈ {2,4,8}`, hence `|Ω_V| ∈ {3,5,9}`
  have hScard := p2a_S_card hFT hC hC4 hP3 hMF2 h hSpg hSle hSidx hSnorm hSD hSsup
  have hΩ : (fixedPts H (centD H t)).ncard = 3 ∨ (fixedPts H (centD H t)).ncard = 5 ∨
      (fixedPts H (centD H t)).ncard = 9 := by
    rw [hcardS]
    rcases hScard with h3 | h3 | h3 <;> rw [h3]
    · exact Or.inl (by norm_num)
    · exact Or.inr (Or.inl (by norm_num))
    · exact Or.inr (Or.inr (by norm_num))
  -- Appendix III
  obtain ⟨f, Z, hf, hfdvd, hZle, hZnorm, hclause⟩ :=
    p2a_appIII_prime_data hFT hC hC4 hP3 hIII hMF2 h
      (p2a_noFourGroup_NN hFT hC hC4 hP3 hIII hMF2 h)
      (p2a_isCoatom_stabilizer hFT hC hC4 hP3 hIII hMF2 h)
  have hf35 : f = 3 ∨ f = 5 := by
    rcases hΩ with h3 | h5 | h9
    · rw [h3] at hfdvd
      exact Or.inl (((Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hfdvd).resolve_left
        hf.ne_one)
    · rw [h5] at hfdvd
      exact Or.inr (((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hfdvd).resolve_left
        hf.ne_one)
    · rw [h9, show (9 : ℕ) = 3 ^ 2 from by norm_num] at hfdvd
      exact Or.inl (((Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp
        (hf.dvd_of_dvd_pow hfdvd)).resolve_left hf.ne_one)
  -- `(u*t)^f = 1`
  have ht2 : t * t = 1 := by
    have hh := pow_orderOf_eq_one t
    rw [h.invol] at hh
    simpa [pow_two] using hh
  have hu2 : u * u = 1 := by
    have hh := pow_orderOf_eq_one u
    rw [hu.2.1] at hh
    simpa [pow_two] using hh
  have hconj : t * (u * t) * t⁻¹ = (u * t)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, inv_eq_of_mul_eq_one_right hu2]
    calc t * (u * t) * t = (t * u) * (t * t) := by group
      _ = t * u := by rw [ht2, mul_one]
  have hzt : (u * t) ^ f = 1 := by
    set z : G := (u * t) ^ f with hz
    have hzZ : z ∈ Z := hclause u hu.1 hu.2.1 hu.2.2
    -- `u` commutes with `z` (`ThmCProp`)
    have hzu : u * z = z * u :=
      hC G h.sit H h.se t h.notMem u ⟨hu.1, hu.2.1⟩ Z hZle
        (hZnorm (p2a_mem_NN_of_mem_centralizer hu.2.2)) z hzZ
    -- `t` inverts `z`
    have htz : t * z * t⁻¹ = z⁻¹ := by
      have hinner : MulAut.conj t (u * t) = (u * t)⁻¹ := by
        rw [MulAut.conj_apply]; exact hconj
      have hmain : MulAut.conj t z = z⁻¹ := by
        rw [hz, map_pow, hinner, inv_pow]
      simpa [MulAut.conj_apply] using hmain
    -- and commutes with it
    have hcomm_ut : z * (u * t) = (u * t) * z :=
      (Commute.refl (u * t)).pow_right f |>.eq.symm
    have hut2 : u * (u * t) = t := by rw [← mul_assoc, hu2, one_mul]
    have hzt_comm : z * t = t * z := by
      calc z * t = z * (u * (u * t)) := by rw [hut2]
        _ = (z * u) * (u * t) := by group
        _ = (u * z) * (u * t) := by rw [hzu]
        _ = u * (z * (u * t)) := by group
        _ = u * ((u * t) * z) := by rw [hcomm_ut]
        _ = (u * (u * t)) * z := by group
        _ = t * z := by rw [hut2]
    have htz' : t * z * t⁻¹ = z := by rw [← hzt_comm]; group
    have hzinv : z = z⁻¹ := htz'.symm.trans htz
    have hzz : z * z = 1 := mul_eq_one_iff_eq_inv.mpr hzinv
    -- `z ∈ D` has odd order and `z² = 1`, so `z = 1`
    have hzD : z ∈ twoPoint H t := hZle hzZ
    have hdvd2 : orderOf z ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hzz)
    have hdvdD : orderOf z ∣ Nat.card ↥(twoPoint H t) :=
      Subgroup.orderOf_dvd_natCard _ hzD
    have hoddD : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
    have hone : orderOf z = 1 := by
      have hg := Nat.dvd_gcd hdvd2 hdvdD
      rw [hoddD.coprime_two_left.gcd_eq_one] at hg
      exact Nat.dvd_one.mp hg
    exact hz ▸ orderOf_eq_one_iff.mp hone
  have hdvdf : orderOf (u * t) ∣ f := orderOf_dvd_iff_pow_eq_one.mpr hzt
  have hne1 : orderOf (u * t) ≠ 1 := by
    intro h1
    have hut1 : u * t = 1 := orderOf_eq_one_iff.mp h1
    have htH : t ∈ H := by
      have h2 : t = u⁻¹ := by
        have := congrArg (fun x => u⁻¹ * x) hut1
        simpa [mul_assoc] using this
      rw [h2]
      exact H.inv_mem hu.1
    exact h.notMem htH
  rcases hf35 with h3 | h5
  · left
    exact ((Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp (h3 ▸ hdvdf)).resolve_left hne1
  · right
    exact ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (h5 ▸ hdvdf)).resolve_left hne1

end Work.NormalComplement.Sec5CKappa
