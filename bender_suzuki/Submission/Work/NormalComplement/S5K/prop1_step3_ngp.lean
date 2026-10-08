/-
# `Submission.Work.NormalComplement.S5K.prop1_step3_ngp`

Port of the four facts about `𝒢 = N_G(P)` needed for the Appendix III input of
Peterfalvi I Ch. III §4 Prop. 1 step 3, from `Setup5` (as in `Sec5Fix/ngpInverted.lean`) to
`Setup45A + IsSylowIn p P (twoPoint H t)`:

* `stronglyEmbedded_normalizer` — `N_H(P) = H ⊓ N_G(P)` is strongly embedded in `N_G(P)`
  (`ChIIFourProp` P1 (b));
* `invNormalizer` / `kset_inf_normalizer_trivial` — `|Inv N_H(P)| = 1`;
* `not_hasFourGroup_normalizer` — `N_G(P)` has 2-rank `1`;
* `normalizerTwoTransitive` / `isCoatom_normalizer` — `N_G(P)` acts 2-transitively on `Ω_P` and the
  point stabiliser is maximal (`IsCoatom`).
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.S5K.prop1_step3_defs
import Submission.Work.NormalComplement.S5K.Defs
import Submission.Work.NormalComplement.S5K.prop1_step3_aux
import Submission.Work.NormalComplement.S5K.prop1_step3_aux2
import Submission.Work.NormalComplement.S5K.prop1_step3_aux3
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
import Submission.Work.ThreePoints.P3NeBot.app3_1
import Submission.Work.DoubleTransitivity.Sec7.ThmA
import Submission.Work.DoubleTransitivity.App2.app2_5
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThreePoints.Omega
import Submission.Work.BrauerSuzuki.Main
import Submission.Work.ThmF.ChV12.glaubermanZJ_free

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Classical
open scoped Pointwise
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.S5K

variable {G : Type} [Group G] [Finite G]
variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}


/-- `t` commutes with every element of `P`: `P ≤ centD H t ≤ C_G(t)`. -/
lemma commute_t_of_mem_P (h : Design.Setup45A G H t W p P A) {x : G} (hx : x ∈ P) :
    t * x * t⁻¹ = x := by
  have hxV : x ∈ centD H t := (h.P_le hx).2
  have hxct : x ∈ Subgroup.centralizer ({t} : Set G) := hxV.2
  rw [Subgroup.mem_centralizer_singleton_iff] at hxct
  rw [← hxct]
  group


/-- `t` lies in `N_G(P)`. -/
lemma mem_normalizer_t (h : Design.Setup45A G H t W p P A) : t ∈ NGP P := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, hxy⟩
    rw [← hxy]
    change t * x * t⁻¹ ∈ P
    rw [commute_t_of_mem_P h hx]
    exact hx
  · intro y hy
    exact ⟨y, hy, by simp [MulAut.conj_apply, commute_t_of_mem_P h hy]⟩


/-- `p ≠ 2`: `p ∣ |E : E'|` divides `|E|`, which divides the odd number `|D|`. -/
lemma setup5_p_ne_two (h : Design.Setup45A G H t W p P A) : p ≠ 2 := by
  intro hp
  have hdvd : p ∣ Nat.card ↥(Design.Egrp H t W) :=
    h.dvd.trans (Subgroup.relIndex_dvd_card _ _)
  have h2 : 2 ∣ Nat.card ↥(Design.Egrp H t W) := hp ▸ hdvd
  have hodd : Odd (Nat.card ↥(Design.Egrp H t W)) :=
    Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le inf_le_right)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)


/-- Every element of `(A ⊓ C_G(P)) ⊔ P` of order dividing `2` is `1`: the group
`C_A(P) · P = C_A(P) × P` has odd order (`A ⊓ P = ⊥`). -/
lemma eq_one_of_mem_sup_of_sq_eq_one (h : Design.Setup45A G H t W p P A) {x : G}
    (hx : x ∈ (((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) : Set G))
    (hx2 : x * x = 1) : x = 1 := by
  classical
  set C : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hC
  have hCnorm : C ≤ Subgroup.normalizer (P : Set G) :=
    le_trans inf_le_right (Subgroup.centralizer_le_normalizer (P : Set G))
  have hprod : ((P : Set G) * (C : Set G)) = (((C ⊔ P : Subgroup G)) : Set G) := by
    rw [sup_comm]
    exact (Subgroup.coe_mul_of_right_le_normalizer_left P C hCnorm).symm
  have hx' : x ∈ (P : Set G) * (C : Set G) := by
    rw [hprod]; exact hx
  obtain ⟨q, hqP, a, haC, hqa⟩ := Set.mem_mul.mp hx'
  have haA : a ∈ A := (Subgroup.mem_inf.mp (hC ▸ haC)).1
  have haC : a ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp (hC ▸ haC)).2
  have hcomm : a * q = q * a := ((Subgroup.mem_centralizer_iff.mp haC) q hqP).symm
  have hsq : q * q * (a * a) = 1 := by
    have h6 : (q * a) * (q * a) = 1 := by rw [hqa]; exact hx2
    rw [show q * a * (q * a) = q * q * (a * a) from by
      rw [mul_assoc, ← mul_assoc a q a, hcomm]; group] at h6
    exact h6
  have hkey : q * q = (a * a)⁻¹ := mul_eq_one_iff_eq_inv.mp hsq
  have haaA : a * a ∈ A := A.mul_mem haA haA
  have hqqA : q * q ∈ A := by rw [hkey]; exact A.inv_mem haaA
  have hqqP : q * q ∈ P := P.mul_mem hqP hqP
  have hqq1 : q * q = 1 := by
    have h7 : q * q ∈ A ⊓ P := ⟨hqqA, hqqP⟩
    rw [h.A_inf] at h7
    simpa using h7
  have haa1 : a * a = 1 := by
    have h8 := hkey
    rw [hqq1] at h8
    exact inv_eq_one.mp h8.symm
  have hq1 : q = 1 := by
    have h1 : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have h2 : orderOf q ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hqP
    rw [h.P_card] at h2
    have hcop : Nat.Coprime 2 p :=
      Nat.coprime_two_left.mpr (h.prime.odd_of_ne_two (setup5_p_ne_two h))
    have h3 : orderOf q ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 2 p = 1 from hcop] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have ha1 : a = 1 := by
    have h1 : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have haT : a ∈ twoPoint H t :=
      (inf_le_left : centD H t ≤ twoPoint H t) (h.A_le haA)
    have h2 : orderOf a ∣ Nat.card ↥(twoPoint H t) :=
      Subgroup.orderOf_dvd_natCard _ haT
    have hodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
    have hgcd : Nat.gcd 2 (Nat.card ↥(twoPoint H t)) = 1 :=
      Nat.coprime_two_left.mpr hodd
    have h3 : orderOf a ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [hgcd] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [← hqa, hq1, ha1, one_mul]

/-! ## `N_H(P)` is strongly embedded in `N_G(P)` -/


/-- `N_H(P) = H ⊓ N_G(P)` is a strongly embedded subgroup of `N_G(P)` (`ChIIFourProp` P1 (b)
applied to `X = P`). -/
theorem stronglyEmbedded_normalizer (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup45A G H t W p P A) :
    IsStronglyEmbedded ((H ⊓ NGP P).subgroupOf (NGP P)) := by
  classical
  set 𝒢 : Subgroup G := NGP P with h𝒢
  obtain ⟨hP1b, -⟩ := hC4 G h.sit H h.se t h.invol h.notMem
  have hPleV : P ≤ centD H t := h.P_le.trans inf_le_right
  have hPleH : P ≤ H := hPleV.trans (inf_le_left.trans inf_le_left)
  have h3 : 3 ≤ (fixedPts H P).ncard := by
    have h3' : 3 ≤ (fixedPts H (centD H t)).ncard :=
      Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem le_rfl
    exact le_trans h3'
      (Set.ncard_le_ncard (Work.ThreePoints.fixedPts_mono hPleV) (Set.toFinite _))
  have hinv : involutions
      (Subgroup.centralizer (P : Set G) : Set G) ⊆ 𝒢 := by
    intro x hx
    rw [Work.ThreePoints.mem_involutions] at hx
    exact Subgroup.centralizer_le_normalizer _ hx.1
  have h1 := hP1b P 𝒢 h3 hinv (by rw [h𝒢]) (1 : G)
    (by rw [Work.DoubleTransitivity.conj_one]; exact hPleH)
  rw [Work.DoubleTransitivity.conj_one] at h1
  rw [h𝒢, inf_comm] at h1
  exact h1

/-! ## The involution of `N_H(P)` is unique -/


/-- The `J`-set of the pair `(N_H(P), t)` inside `N_G(P)` is trivial. -/
theorem kset_inf_normalizer_trivial (hFT : Submission.Blueprint.FeitThompsonProp)
    (h : Design.Setup45A G H t W p P A) :
    (Work.ThmF.Kset ((H ⊓ NGP P).subgroupOf (NGP P)) ⟨t, mem_normalizer_t h⟩).ncard = 1 := by
  classical
  set 𝒢 : Subgroup G := NGP P with h𝒢
  set H₁ : Subgroup G := H ⊓ 𝒢 with hH₁
  have ht𝒢 : t ∈ 𝒢 := mem_normalizer_t h
  rw [Set.ncard_eq_one]
  refine ⟨1, Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · unfold Work.ThmF.Kset
    rw [Work.ThreePoints.mem_invertedBy]
    exact ⟨Subgroup.one_mem _, by simp⟩
  · intro x hx
    unfold Work.ThmF.Kset at hx
    rw [Work.ThreePoints.mem_invertedBy] at hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hxH1, hxH2⟩ := Subgroup.mem_inf.mp hx1
    have hxH₁ : (x : G) ∈ H₁ := Subgroup.mem_subgroupOf.mp hxH1
    have hxG : (x : G) ∈ NGP P := hxH₁.2
    have h2 : t * (x : G) * t⁻¹ = (x : G)⁻¹ := by
      have h4 := congrArg (fun y : ↥𝒢 => (y : G)) hx2
      simpa using h4
    have hxconj : (x : G) ∈ Submission.Blueprint.conj t H := by
      rw [Work.ThreePoints.mem_conj_iff]
      have h3' : (↑(⟨t, ht𝒢⟩⁻¹ * x * ⟨t, ht𝒢⟩) : G) ∈ H₁ :=
        Subgroup.mem_subgroupOf.mp ((Work.ThreePoints.mem_conj_iff).mp hxH2)
      have h1 : H₁ ≤ H := by rw [hH₁]; exact inf_le_left
      exact h1 (by simpa using h3')
    have hxD : (x : G) ∈ Submission.Blueprint.twoPoint H t := ⟨hxH₁.1, hxconj⟩
    have hxAP : (x : G) ∈ (((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) : Set G) := by
      rw [← (Work.NormalComplement.sec4_one_c hFT h).1]
      exact ⟨hxD, hxG⟩
    have hx2' : (x : G) * (x : G) = 1 := by
      have hxct : (x : G) ∈ Subgroup.centralizer ({t} : Set G) := by
        have hle1 : (A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) ≤
            Subgroup.centralizer ({t} : Set G) := by
          refine le_trans inf_le_left ?_
          intro y hy
          exact (Subgroup.mem_inf.mp (h.A_le hy)).2
        have hsup : ((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) ≤
            Subgroup.centralizer ({t} : Set G) := by
          refine sup_le hle1 ?_
          intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hyc := commute_t_of_mem_P h hy
          calc y * t = (t * y * t⁻¹) * t := by rw [hyc]
            _ = t * y := by group
        exact hsup hxAP
      rw [Subgroup.mem_centralizer_singleton_iff] at hxct
      rw [← hxct, mul_assoc, mul_inv_cancel, mul_one] at h2
      exact mul_eq_one_iff_eq_inv.mpr h2
    have hx1' : (x : G) = 1 := eq_one_of_mem_sup_of_sq_eq_one h hxAP hx2'
    exact Subtype.ext (by simpa using hx1')


/-- The involutions of `N_H(P) = H ⊓ N_G(P)`, viewed inside `N_G(P)`, are exactly `u`
(§5 Prop. 2 (c), `|Inv N_H(P)| = 1`). -/
theorem invNormalizer (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup45A G H t W p P A) :
    (involutions (((H ⊓ NGP P).subgroupOf (NGP P)) : Set ↥(NGP P))).ncard = 1 := by
  classical
  have hse : IsStronglyEmbedded ((H ⊓ NGP P).subgroupOf (NGP P)) :=
    stronglyEmbedded_normalizer hC4 h
  have ht𝒢 : t ∈ NGP P := mem_normalizer_t h
  have ht'H : (⟨t, ht𝒢⟩ : ↥(NGP P)) ∉ (H ⊓ NGP P).subgroupOf (NGP P) := fun hmem =>
    h.notMem (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).1
  have hcard := Work.ThmF.Bender.cardKsetEqInv (H := (H ⊓ NGP P).subgroupOf (NGP P)) hse
    (by rw [← Subgroup.orderOf_coe]; exact h.invol) ht'H
  have hDK := kset_inf_normalizer_trivial hFT h
  have hDK' : (Work.ThmF.Kset ((H ⊓ NGP P).subgroupOf (NGP P)) (⟨t, ht𝒢⟩ : ↥(NGP P))).ncard = 1 :=
    hDK
  exact hcard ▸ hDK'

/-! ## `N_G(P)` has 2-rank `1` -/


/-- `N_G(P)` has no four-group: it has a strongly embedded subgroup `N_H(P)` with a unique
involution, so a four-group in `N_G(P)` would give `N_H(P)` at least two involutions
(`cardInvGeTwo`). -/
theorem not_hasFourGroup_normalizer (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup45A G H t W p P A) :
    ¬ Submission.Blueprint.HasFourGroup ↥(NGP P) := by
  intro h4
  have hse : IsStronglyEmbedded ((H ⊓ NGP P).subgroupOf (NGP P)) :=
    stronglyEmbedded_normalizer hC4 h
  have h2 := Work.ThmF.Bender.cardInvGeTwo (H := (H ⊓ NGP P).subgroupOf (NGP P)) hse h4
  have h1 := invNormalizer hFT hC4 h
  omega

/-! ## `N_G(P)` acts 2-transitively on `Ω_P` -/


/-- Peterfalvi I Ch. III §5 Prop. 2 (c): `N_G(P)` acts 2-transitively on the set `Ω_P` of fixed
points of `P`, by App. II(5) (`app2_5`) applied to the 2-transitive action of `G` on `G ⧸ H`
(Theorem A, `ThmAProp`). -/
theorem normalizerTwoTransitive (hA : Submission.Blueprint.ThmAProp)
    (h : Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t)) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub (NGP P) (fixedPts H P) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have h2 : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := hA G h.sit.1.1 H h.se
  have hab : (Work.DoubleTransitivity.pt H : G ⧸ H) ≠ (QuotientGroup.mk t : G ⧸ H) := by
    intro hcon
    exact h.notMem ((Work.DoubleTransitivity.mk_one_eq_iff (H := H)).mp hcon.symm)
  have hstab : MulAction.stabilizer G (Work.DoubleTransitivity.pt H) ⊓
      MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) = twoPoint H t := by
    rw [show (Work.DoubleTransitivity.pt H : G ⧸ H) = QuotientGroup.mk (1 : G) from rfl]
    rw [Work.ThreePoints.stabilizer_mk H 1, Work.ThreePoints.stabilizer_mk H t,
      Work.DoubleTransitivity.conj_one]
  have hP : Work.DoubleTransitivity.IsSylowSubgroupOf p P
      (MulAction.stabilizer G (Work.DoubleTransitivity.pt H) ⊓
        MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H)) := by
    rw [hstab]
    exact ⟨hPsyl.2.1, hPsyl.1, hPsyl.2.2⟩
  exact Work.DoubleTransitivity.App2.app2_5 (X := G) (E := G ⧸ H) (a :=
    Work.DoubleTransitivity.pt H) (b := (QuotientGroup.mk t : G ⧸ H)) hab h2 hP

/-! ## The point stabiliser `N_H(P)/K` is a coatom -/


/-- `N_H(P)` is a maximal subgroup of `N_G(P)` (`maximal_of_twoTransitive` applied to the
2-transitive action of `N_G(P)` on `Ω_P`). -/
theorem isCoatom_normalizer (hA : Submission.Blueprint.ThmAProp)
    (h : Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t)) :
    IsCoatom ((H ⊓ NGP P).subgroupOf (NGP P)) := by
  classical
  set 𝒢 : Subgroup G := NGP P with h𝒢
  have hPleV : P ≤ centD H t := h.P_le.trans inf_le_right
  have hPleH : P ≤ H := hPleV.trans (inf_le_left.trans inf_le_left)
  have h3 : 3 ≤ (fixedPts H P).ncard := by
    have h3' : 3 ≤ (fixedPts H (centD H t)).ncard :=
      Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem le_rfl
    exact le_trans h3'
      (Set.ncard_le_ncard (Work.ThreePoints.fixedPts_mono hPleV) (Set.toFinite _))
  have h2t := normalizerTwoTransitive hA h hPsyl
  have h2t' : Work.DoubleTransitivity.IsTwoTransitiveOnSub 𝒢 (fixedPts H P) := by
    rw [h𝒢]; exact h2t
  rw [isCoatom_iff_ge_of_le]
  constructor
  · intro htop
    have hle : 𝒢 ≤ H := by
      intro g hg
      have h1 : (⟨g, hg⟩ : ↥𝒢) ∈ (H ⊓ 𝒢).subgroupOf 𝒢 := by
        rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp h1).1
    exact h.notMem (hle (mem_normalizer_t h))
  · intro M hMne hHM
    have hHM' : 𝒢 ⊓ H ≤ M.map (Subgroup.subtype 𝒢) := by
      intro y hy
      obtain ⟨hy𝒢, hyH⟩ := Subgroup.mem_inf.mp hy
      exact Subgroup.mem_map.mpr ⟨⟨y, hy𝒢⟩,
        hHM (Subgroup.mem_subgroupOf.mpr (show y ∈ H ⊓ 𝒢 from ⟨hyH, hy𝒢⟩)), rfl⟩
    have hMF' : M.map (Subgroup.subtype 𝒢) ≤ 𝒢 := Subgroup.map_subtype_le M
    rcases Work.ThreePoints.P3NeBot.maximal_of_twoTransitive (H := H) (F := 𝒢)
        (M := M.map (Subgroup.subtype 𝒢)) (X := P) hPleH le_rfl h3 h2t' hHM' hMF' with h | h
    · intro z hz
      have h1 : (z : G) ∈ 𝒢 ⊓ H := le_of_eq h (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
      exact Subgroup.mem_subgroupOf.mpr
        ⟨(Subgroup.mem_inf.mp h1).2, (Subgroup.mem_inf.mp h1).1⟩
    · exact absurd (by
        refine le_antisymm le_top fun z _ => ?_
        have hz' : (z : G) ∈ M.map (Subgroup.subtype 𝒢) := le_of_eq h.symm z.2
        obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz'
        rwa [Subtype.ext hwz] at hw) hMne

/-! ## Main theorem -/

end Work.NormalComplement.S5K
