import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.isSplitRankOne_map_of_surjective
import Submission.Work.PSU3.StageB.t_mem_and_center_quotient
import Submission.Work.PSU3.StageA.modelDataBorel
import Submission.Work.PSU3.StageA.isSplitRankOneTransfer
import Submission.Work.PSU3.StageA.lemma2cAux
import Submission.Work.PSU3.StageB.NotFpfStep2.quot_isPSU3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep2

open LeanEval.GroupTheory.Defs

/-- `H ⊓ U` is strongly embedded in `U = O^{2'}(C_G(P))`: Peterfalvi Ch. II §4 Prop. 1(b)
applied with `X = P`, `F = U`, `g = 1` (`P` fixes at least three points through `P ≤ V`, and
every involution of `C_G(P)` lies in `U`). -/
private theorem isSplitRankOne_map_center_strongEmb {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (_hPp : (Nat.card P).Prime) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P)) := by
  classical
  have hsplit := hS.split
  have hH := hsplit.stronglyEmbedded
  have ht2 := hsplit.invol
  have htH := hsplit.not_mem
  have hP1b := (hC4 G hS.situation H hH t ht2 htH).1
  have hX3 := Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht2 htH hPV
  have hFle : Work.PSU3.StageB.centralizerOddResidual P ≤
      Subgroup.centralizer (P : Set G) := by
    change (Submission.Blueprint.oddResidual ↥(Subgroup.centralizer (P : Set G))).map
      (Subgroup.centralizer (P : Set G)).subtype ≤ Subgroup.centralizer (P : Set G)
    exact Subgroup.map_subtype_le _
  have hInv : Submission.Blueprint.involutions
      (Subgroup.centralizer (P : Set G) : Set G) ⊆
        Work.PSU3.StageB.centralizerOddResidual P := by
    intro x hx
    exact Work.PSU3.StageA.mem_map_oddResidual_of_orderOf_eq_two_pow
      (C := Subgroup.centralizer (P : Set G)) hx.1 (k := 1) (by rw [hx.2, pow_one])
  have hFN : Work.PSU3.StageB.centralizerOddResidual P ≤ Subgroup.normalizer (P : Set G) :=
    hFle.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  have hPH : P ≤ Submission.Blueprint.conj (1 : G) H := by
    rw [Work.DoubleTransitivity.conj_one]
    exact fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hPV hx)).1).1
  have hres := hP1b P (Work.PSU3.StageB.centralizerOddResidual P) hX3 hInv hFN 1 hPH
  rwa [Work.DoubleTransitivity.conj_one, inf_comm] at hres

/-- `O(U) = Z(U)` for `U = O^{2'}(C_G(P))`: the `oddCore F = center F` conjunct of the P3 clause
of `ChIIFourProp` at `X = P` (the normalising `k ∈ J(D,t)` is supplied by
`ChV12.exists_k_normalizing`). -/
private theorem isSplitRankOne_map_center_oddCore {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime) :
    Submission.Blueprint.oddCore ↥(Work.PSU3.StageB.centralizerOddResidual P) =
      Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P) := by
  classical
  have hsplit := hS.split
  have hH := hsplit.stronglyEmbedded
  have ht2 := hsplit.invol
  have htH := hsplit.not_mem
  have hP1b := (hC4 G hS.situation H hH t ht2 htH).1
  have hP3 := (hC4 G hS.situation H hH t ht2 htH).2.2.2.1
  have hP4 : Submission.Blueprint.HasFourGroup
      ↥(Subgroup.centralizer (P : Set G)) := hS.B3 P hPV hPp
  have hX3 := Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht2 htH hPV
  obtain ⟨k0, hk0K, hk01, hk0N⟩ :=
    Work.ThmF.ChV12.exists_k_normalizing hH ht2 htH hPV hX3 hP4 hP1b
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPp
    exact Nat.not_prime_one hPp
  have hP3c := hP3 P hPne hPV ⟨k0, hk0K, hk01, hk0N⟩
  dsimp only at hP3c
  obtain ⟨-, ⟨S, hSp, hSFH, hSidx, hSNorm, hSD, hSsup⟩, ⟨hZc, hYZc⟩, -⟩ := hP3c
  exact hZc

/-- Inside `F = O^{2'}(C_G(P))`, the pair `(H ⊓ F, Q ⊓ F)` satisfies the five structural
conditions of a split rank-one normal complement: `Q ⊓ F` is a `2`-group, lies in `H ⊓ F`,
is normal in it, and `H ⊓ F = (Q ⊓ F) ⋊ twoPoint (H ⊓ F) ⟨t, ·⟩`.

The only non-elementary point is the last (`sup`) identity: the P3 clause of `ChIIFourProp` at
`X = P` supplies a Sylow `2`-subgroup `S` of `H ⊓ N_G(P)` with
`H ⊓ N_G(P) = S ⊔ (D ⊓ N_G(P))`, and `S ≤ Q` (normality of `Q` in `H` plus odd index), so
intersecting with `F` (note `F ≤ C_G(P) ≤ N_G(P)`) gives the claim. -/
private theorem isSplitRankOne_map_center_relQ {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime) :
    IsPGroup 2 ((Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P)) ∧
      ((Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P)) ≤
        ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P)) ∧
      ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P)) ≤
        Subgroup.normalizer (((Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P) : Subgroup ↥(Work.PSU3.StageB.centralizerOddResidual P)) :
            Set ↥(Work.PSU3.StageB.centralizerOddResidual P)) ∧
      ((Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P)) ⊓
        Submission.Blueprint.twoPoint ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P))
          ⟨t, (Work.PSU3.StageB.t_mem_and_center_quotient hS hPV).1⟩ = ⊥ ∧
      ((Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P)) ⊔
        Submission.Blueprint.twoPoint ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P))
          ⟨t, (Work.PSU3.StageB.t_mem_and_center_quotient hS hPV).1⟩ =
          ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
          (Work.PSU3.StageB.centralizerOddResidual P)) := by
  classical
  let F : Subgroup G := Work.PSU3.StageB.centralizerOddResidual P
  have hsplit := hS.split
  have hH := hsplit.stronglyEmbedded
  have ht2 := hsplit.invol
  have htH := hsplit.not_mem
  have hP1b := (hC4 G hS.situation H hH t ht2 htH).1
  have hP3 := (hC4 G hS.situation H hH t ht2 htH).2.2.2.1
  have hP4 : Submission.Blueprint.HasFourGroup
      ↥(Subgroup.centralizer (P : Set G)) := hS.B3 P hPV hPp
  have hX3 := Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht2 htH hPV
  obtain ⟨k0, hk0K, hk01, hk0N⟩ :=
    Work.ThmF.ChV12.exists_k_normalizing hH ht2 htH hPV hX3 hP4 hP1b
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPp
    exact Nat.not_prime_one hPp
  have hP3c := hP3 P hPne hPV ⟨k0, hk0K, hk01, hk0N⟩
  dsimp only at hP3c
  obtain ⟨-, ⟨S, hSp, hSFH, hSidx, hSNorm, hSD, hSsup⟩, ⟨hZc, hYZc⟩, -⟩ := hP3c
  have htF : t ∈ F := (Work.PSU3.StageB.t_mem_and_center_quotient hS hPV).1
  have hFle : F ≤ Subgroup.centralizer (P : Set G) := by
    change Work.PSU3.StageB.centralizerOddResidual P ≤ Subgroup.centralizer (P : Set G)
    simp only [Work.PSU3.StageB.centralizerOddResidual]
    exact Subgroup.map_subtype_le _
  have hconjF : F.map (MulAut.conj t).toMonoidHom = F := by
    ext x
    rw [Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff]
    constructor
    · intro hx
      have hx_eq : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
      rw [hx_eq]
      exact F.mul_mem (F.mul_mem htF hx) (F.inv_mem htF)
    · intro hx
      exact F.mul_mem (F.mul_mem (F.inv_mem htF) hx) htF
  have htp : Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F) (⟨t, htF⟩ : ↥F)
      = (Submission.Blueprint.twoPoint H t ⊓ F).subgroupOf F := by
    rw [Work.DoubleTransitivity.Sec5.twoPoint_subgroupOf htF]
    congr 1
    change (H ⊓ F) ⊓ (H ⊓ F).map (MulAut.conj t).toMonoidHom
        = (H ⊓ H.map (MulAut.conj t).toMonoidHom) ⊓ F
    rw [Subgroup.map_inf H F (MulAut.conj t).toMonoidHom (MulAut.conj t).injective, hconjF]
    ext x; simp only [Subgroup.mem_inf]; tauto
  have hSF : S ≤ F := hSFH.trans inf_le_left
  have hS_le_H : S ≤ H := fun x hx => (Subgroup.mem_inf.mp (hSFH hx)).2
  have hQHindex : (Q.subgroupOf H).index =
      Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    have hcard := Subgroup.card_mul_index (Q.subgroupOf H)
    have h1 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsplit.le).toEquiv
    rw [h1, Work.ThmF.split_card_H hsplit] at hcard
    exact Nat.mul_left_cancel Nat.card_pos hcard
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := hH.2.2 t htH
  have hS_le_Q : S ≤ Q := by
    intro x hx
    haveI : (Q.subgroupOf H).Normal := Work.ThmF.split_Q_normal_in_H hsplit
    obtain ⟨n, hn⟩ := hSp (⟨x, hx⟩ : ↥S)
    have hxn : (⟨x, hS_le_H hx⟩ : ↥H) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      have := congrArg (fun g : ↥S => (g : G)) hn
      simpa using this
    exact Work.PSU3.StageA.mem_of_pow_two_eq_one_of_normal_odd_index (N := Q.subgroupOf H)
      (by rw [hQHindex]; exact hDodd) hxn
  have hSF_sup : S.subgroupOf F ⊔ Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F)
      (⟨t, htF⟩ : ↥F) = (H ⊓ F).subgroupOf F := by
    apply Subgroup.map_injective F.subtype_injective
    rw [Subgroup.map_sup, htp, Subgroup.map_subgroupOf_eq_of_le hSF,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : Submission.Blueprint.twoPoint H t ⊓ F ≤ F),
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : H ⊓ F ≤ F)]
    refine le_antisymm (sup_le (le_inf (hSFH.trans inf_le_right) (hSFH.trans inf_le_left))
      (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)) ?_
    intro x hx
    obtain ⟨hxH, hxF⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.centralizer_le_normalizer (P : Set G) (hFle hxF)
    have hxmem : x ∈ S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (P : Set G)) := by
      rw [hSsup]; exact ⟨hxH, hxN⟩
    have hnorm : Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (P : Set G)
        ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf (le_trans inf_le_left inf_le_left) inf_le_right).trans hSNorm
    obtain ⟨a, haS, b, hb, hxab⟩ :=
      Commons.GroupTheory.Subgroup.mem_sup_of_le_normalizer S
        (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (P : Set G)) hnorm hxmem
    have hbF : b ∈ F := by
      have hbeq : b = a⁻¹ * x := by rw [hxab]; group
      rw [hbeq]; exact F.mul_mem (F.inv_mem (hSF haS)) hxF
    rw [hxab]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haS)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hb.1, hbF⟩))
  -- ## the five conjuncts, in terms of `F`
  have hQleH' : (Q ⊓ F).subgroupOf F ≤ (H ⊓ F).subgroupOf F := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxQ, hxF⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hsplit.le hxQ, hxF⟩
  have hHnorm' : (H ⊓ F).subgroupOf F ≤
      Subgroup.normalizer (((Q ⊓ F).subgroupOf F : Subgroup ↥F) : Set ↥F) := by
    have hHFN : H ⊓ F ≤ Subgroup.normalizer ((Q ⊓ F : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      obtain ⟨hxH, hxF⟩ := Subgroup.mem_inf.mp hx
      constructor
      · intro hy
        obtain ⟨hyQ, hyF⟩ := Subgroup.mem_inf.mp hy
        exact Subgroup.mem_inf.mpr
          ⟨(Subgroup.mem_normalizer_iff.mp (hsplit.normal hxH) y).mp hyQ,
            F.mul_mem (F.mul_mem hxF hyF) (F.inv_mem hxF)⟩
      · intro hy
        obtain ⟨hyQ, hyF⟩ := Subgroup.mem_inf.mp hy
        refine Subgroup.mem_inf.mpr
          ⟨(Subgroup.mem_normalizer_iff.mp (hsplit.normal hxH) y).mpr hyQ, ?_⟩
        have h1 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
        rw [h1]
        exact F.mul_mem (F.mul_mem (F.inv_mem hxF) hyF) hxF
    rw [Commons.GroupTheory.Subgroup.normalizer_subgroupOf (Q ⊓ F) F inf_le_right]
    exact Subgroup.subgroupOf_mono F (le_inf hHFN inf_le_right)
  have hQinf' : (Q ⊓ F).subgroupOf F ⊓ Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F)
      (⟨t, htF⟩ : ↥F) = ⊥ := by
    rw [htp, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hx1 hx2
    obtain ⟨hxQ, -⟩ := Subgroup.mem_inf.mp hx1
    obtain ⟨hxD, -⟩ := Subgroup.mem_inf.mp hx2
    have hbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hsplit.inf_eq]
      exact Subgroup.mem_inf.mpr ⟨hxQ, hxD⟩
    rw [Subgroup.mem_bot] at hbot
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by simpa using hbot)
  have hQsup' : (Q ⊓ F).subgroupOf F ⊔ Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F)
      (⟨t, htF⟩ : ↥F) = (H ⊓ F).subgroupOf F := by
    refine le_antisymm (sup_le hQleH' inf_le_left) ?_
    have hS' : S.subgroupOf F ≤ (Q ⊓ F).subgroupOf F :=
      Subgroup.subgroupOf_mono F (le_inf hS_le_Q hSF)
    calc (H ⊓ F).subgroupOf F
        = S.subgroupOf F ⊔ Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F) (⟨t, htF⟩ : ↥F) :=
          hSF_sup.symm
      _ ≤ (Q ⊓ F).subgroupOf F ⊔ Submission.Blueprint.twoPoint ((H ⊓ F).subgroupOf F)
            (⟨t, htF⟩ : ↥F) := sup_le_sup_right hS' _
  have hQ2' : IsPGroup 2 ↥((Q ⊓ F).subgroupOf F) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    obtain ⟨n, hn⟩ := hS.two (⟨(x : ↥F), (Subgroup.mem_subgroupOf.mp x.2).1⟩ : ↥Q)
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun g : ↥Q => (g : G)) hn
    simpa using this
  exact ⟨hQ2', hQleH', hHnorm', hQinf', hQsup'⟩

/-- **`Work.PSU3.StageB.NotFpfStep2.isSplitRankOne_map_center`** (Peterfalvi II Ch. VII §4 (2),
the datum-transfer step).  For `F = O^{2'}(C_G(P))` and an epimorphism `φ : ↥F ↠ Y` with
`ker φ = Z(F)` onto a simple Bender group `Y`, the rank-one configuration
`((H ⊓ F)/Z(F), (Q ⊓ F)/Z(F), φ t)` is a split rank-one datum in `Y`.

Proof: transfer along `φ` (`Work.PSU3.StageA.isSplitRankOneTransfer`).  The Borel
`(H ⊓ F).subgroupOf F` is strongly embedded (`isSplitRankOne_map_center_strongEmb`), `ker φ` is
central of odd order (`isSplitRankOne_map_center_oddCore`), `Y` is a simple Bender group so the
image of the Borel is the Borel of a `ModelData` (`Work.PSU3.StageA.modelDataBorel`, using
`Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd`), and the normal complement
`(Q ⊓ F).subgroupOf F` satisfies the five structural conditions of
`isSplitRankOne_map_center_relQ`. -/
theorem isSplitRankOne_map_center {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    {Y : Type} [Group Y] [Finite Y] {φ : ↥(Work.PSU3.StageB.centralizerOddResidual P) →* Y}
    (hφsurj : Function.Surjective φ)
    (hφker : φ.ker = Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P))
    (hY : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y) :
    Submission.Blueprint.IsSplitRankOne
      (((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P)).map φ)
      (((Q ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P)).map φ)
      (φ ⟨t, (Work.PSU3.StageB.t_mem_and_center_quotient hS hPV).1⟩) := by
  classical
  obtain ⟨hQ2, hQleH, hHnorm, hQinf, hQsup⟩ := isSplitRankOne_map_center_relQ hS hC4 hPV hPp
  have hHF : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P)) :=
    isSplitRankOne_map_center_strongEmb hS hC4 hPV hPp
  have hoddCore : Submission.Blueprint.oddCore
      ↥(Work.PSU3.StageB.centralizerOddResidual P) =
      Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P) :=
    isSplitRankOne_map_center_oddCore hS hC4 hPV hPp
  have htF : t ∈ Work.PSU3.StageB.centralizerOddResidual P :=
    (Work.PSU3.StageB.t_mem_and_center_quotient hS hPV).1
  have ht2 : orderOf (⟨t, htF⟩ : ↥(Work.PSU3.StageB.centralizerOddResidual P)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hS.split.invol
  have htH : (⟨t, htF⟩ : ↥(Work.PSU3.StageB.centralizerOddResidual P)) ∉
      (H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P) := by
    intro hmem
    exact hS.split.not_mem (Subgroup.mem_subgroupOf.mp hmem).1
  have hkerH : φ.ker ≤ (H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
      (Work.PSU3.StageB.centralizerOddResidual P) := by
    rw [hφker]
    exact Work.PSU3.StageA.center_le_of_isStronglyEmbedded hHF
  have hoddker : Odd (Nat.card φ.ker) := by
    rw [hφker, ← hoddCore]
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have hemb : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      (((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P)).map φ) :=
    Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd φ hφsurj hoddker hkerH hHF
  obtain ⟨Pmd, hPmdB⟩ := Work.PSU3.StageA.modelDataBorel hY hemb
  exact Work.PSU3.StageA.isSplitRankOneTransfer hHF ht2 htH hoddCore hφsurj hφker
    ⟨Pmd, hPmdB⟩ hQ2 hQleH hHnorm hQinf hQsup

end Work.PSU3.StageB.NotFpfStep2
