import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.DoubleTransitivity.Sec4.lemma2_propagation
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.DoubleTransitivity.Sec2.lemma1
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.S4Prop2.even_card_normalizer_of_maximal_p_subgroup_gen
import Submission.Work.ThreePoints.S4Prop2.sec4_basic
import Submission.Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit
import Submission.Work.ThreePoints.S4Prop2.ncard_involutions_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec4.lemma2_part1`

Peterfalvi I, Ch. I §4 Lemma 2, part 1 (pp. 155–156): if `Q` is maximal among the `p`-subgroups of
`G` with at least three fixed points, `Q` contains a `p`-Sylow `Q₀` of a two-point stabiliser, and
two distinct fixed points `ω₁', ω₂'` of `Q` satisfy `|N_G(Q) ⊓ Stab ω₁'|` even, then `Q` **is** a
`p`-Sylow of `Stab ω₁' ⊓ Stab ω₂'`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

namespace Work.DoubleTransitivity.Sec4

variable {G : Type} [Group G] [Finite G]

/-- A `p`-group with `p` odd has odd order. -/
theorem odd_card_of_isPGroup_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G}
    (hQp : IsPGroup p Q) : Odd (Nat.card ↥Q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  rw [hk]
  have hodd : Odd p := by
    rw [Nat.odd_iff]
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  exact hodd.pow

/-- **Appendix I (3)(b)**, in the form used by Ch. I §4 Lemma 2: if the involution `t` exchanges
the distinct points `ω₁, ω₂` of `Ω = G ⧸ H` and `Q₀` is a `t`-invariant `p`-Sylow of
`Stab ω₁ ⊓ Stab ω₂`, then `|t ^ Q₀| = p ^ (v_p |Inv H|)`. -/
theorem card_conjOrbit_sylow_eq_pPart {H : Subgroup G} (hH : IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) {t : G} (ht : orderOf t = 2) {ω₁ ω₂ : Omega H} (hω₂₁ : ω₂ ≠ ω₁)
    (htω : t • ω₁ = ω₂)
    {Q₀ : Subgroup G}
    (hQ₀syl : IsSylowSubgroupOf p Q₀
      (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂))
    (htQ₀ : conj t Q₀ = Q₀) :
    (Work.DoubleTransitivity.conjOrbit Q₀ t).ncard =
      p ^ ((Submission.Blueprint.involutions (H : Set G)).ncard.factorization p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup G := MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂ with hD
  have hKss : IsStronglyEmbedded (MulAction.stabilizer G ω₁) :=
    Work.ThreePoints.S4Prop2.isStronglyEmbedded_stabilizer hH ω₁
  have hKss' : IsStronglyEmbedded (MulAction.stabilizer G ω₂) :=
    Work.ThreePoints.S4Prop2.isStronglyEmbedded_stabilizer hH ω₂
  have hKB : IsBender (MulAction.stabilizer G ω₁) :=
    (isStronglyEmbedded_iff _).mp hKss |>.2
  have hKne : MulAction.stabilizer G ω₁ ≠ ⊤ := ((isStronglyEmbedded_iff _).mp hKss).1
  have htK : t ∉ MulAction.stabilizer G ω₁ := by
    intro hcon
    have h1 : t • ω₁ = ω₁ := MulAction.mem_stabilizer_iff.mp hcon
    exact hω₂₁ (h1.symm.trans htω).symm
  have htwo : Submission.Blueprint.twoPoint (MulAction.stabilizer G ω₁) t = D := by
    rw [Submission.Blueprint.twoPoint, hD,
      ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t ω₁, htω]
  -- `D` has odd order and is `t`-invariant
  have hDodd : Odd (Nat.card ↥D) := by
    rw [hD]
    exact Work.ThreePoints.S4Prop2.odd_card_stabilizer_inf hH (fun h => hω₂₁ h.symm)
  have htD : t ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conj t (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂) = D
    have htω' : t • ω₂ = ω₁ := by
      have h1 : t • (t • ω₁) = t • ω₂ := by rw [htω]
      rw [← mul_smul, Work.DoubleTransitivity.App1.mul_self_eq_one_of_orderOf_eq_two ht,
        one_smul] at h1
      exact h1.symm
    rw [hD, Work.ThreePoints.conj_inf,
      ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t ω₁,
      ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t ω₂, htω, htω', inf_comm]
  -- `|t ^ D| = |Inv H|`
  have hDinv : (Work.DoubleTransitivity.conjOrbit D t).ncard =
      (Submission.Blueprint.involutions (H : Set G)).ncard := by
    have h1 : (Submission.Blueprint.invertedBy D t).ncard =
        (Submission.Blueprint.involutions (MulAction.stabilizer G ω₁ : Set G)).ncard := by
      have := (Work.DoubleTransitivity.Sec2.prop2 hKB hKne ht htK).2.1
      rwa [htwo] at this
    have h2 : (Submission.Blueprint.invertedBy D t).ncard =
        (Work.DoubleTransitivity.conjOrbit D t).ncard :=
      Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit ht hDodd htD
    have h3 : (Submission.Blueprint.involutions (MulAction.stabilizer G ω₁ : Set G)).ncard =
        (Submission.Blueprint.involutions (H : Set G)).ncard := by
      have h := Work.ThreePoints.S4Prop2.ncard_involutions_stabilizer_eq (K := H) ω₁ (pt H)
      rwa [stabilizer_pt_eq] at h
    rw [← h2, h1, h3]
  -- Appendix I (3)(b)
  rw [Work.ThreePoints.S4Prop2.card_conjOrbit_sylow hp ht hDodd htD hQ₀syl.1 hQ₀syl.2.1
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr htQ₀) hQ₀syl.2.2, hDinv]

/-- If `(D,K)` is a `p`-regular intersection with `D ≤ K`, then *every* `p`-Sylow of `D` has an
even-order normaliser in `K` (Ch. I §4 Lemma 1, (c) ⇒ (d), via Sylow conjugacy inside `D`). -/
theorem even_normalizer_of_isRegularIntersection_sylow {D K : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hreg : IsRegularIntersection p D K) (hDK : D ≤ K) {R : Subgroup G}
    (hRsyl : IsSylowSubgroupOf p R D) :
    Even (Nat.card ↥(Subgroup.normalizer (R : Set G) ⊓ K)) := by
  obtain ⟨P, hPsyl, hPeven⟩ := hreg
  obtain ⟨d, hdD, hd⟩ := Work.ThreePoints.exists_conj_of_isSylowSubgroupOf hp
    hPsyl.1 hPsyl.2.1 hPsyl.2.2 hRsyl.1 hRsyl.2.1 hRsyl.2.2
  have hconjN : conj d (Subgroup.normalizer (P : Set G)) =
      Subgroup.normalizer (conj d P : Set G) := by
    have hmap := Subgroup.map_normalizer_eq_of_bijective (P : Subgroup G)
      (f := (MulAut.conj d).toMonoidHom) (MulAut.conj d).bijective
    rw [show conj d (Subgroup.normalizer (P : Set G)) =
          (Subgroup.normalizer (P : Set G)).map (MulAut.conj d).toMonoidHom from rfl, hmap]
  have hstep : Subgroup.normalizer (R : Set G) ⊓ K =
      conj d (Subgroup.normalizer (P : Set G) ⊓ K) := by
    rw [← hd, Work.ThreePoints.conj_inf, hconjN,
      Work.ThreePoints.conj_eq_self_of_mem (hDK hdD)]
  rw [hstep]
  have hcard : Nat.card ↥(conj d (Subgroup.normalizer (P : Set G) ⊓ K)) =
      Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ K) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj d).toMonoidHom) (MulAut.conj d).injective
  rw [hcard]
  exact hPeven

/-- **Peterfalvi I, Ch. I §4 Lemma 2, part 1** (pp. 155–156).  See `Sec4Lemma2Part1` in
`Submission/Work/DoubleTransitivity/Sec4/RpDefs.lean` for the unrolled statement. -/
theorem lemma2_part1 (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : Sec4Lemma2Part1 p H := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Omega H) := Fintype.ofFinite _
  intro Q hQmax hQinv ω₁' ω₂' hne hQω₁' hQω₂' hEven
  obtain ⟨ω₁, ω₂, hω₂₁, Q₀, hQ₀syl, hQ₀Q⟩ := hQinv
  -- the two exchanging involutions: for the `Q₀` pair and for the target pair
  obtain ⟨t, ht2, htQ₀, htω⟩ := Work.ThreePoints.sec3_lemma1 hH hp (fun h => hω₂₁ h.symm) hQ₀syl
  obtain ⟨t', ht'2, ht'ω⟩ := Work.ThreePoints.exists_involution_smul_eq_of_ne hH (fun h => hne h.symm)
  have ht'K : t' ∉ MulAction.stabilizer G ω₁' := by
    intro hcon
    have h1 : t' • ω₁' = ω₁' := MulAction.mem_stabilizer_iff.mp hcon
    exact hne (h1.symm.trans ht'ω).symm
  have hKss : IsStronglyEmbedded (MulAction.stabilizer G ω₁') :=
    Work.ThreePoints.S4Prop2.isStronglyEmbedded_stabilizer hH ω₁'
  have hKB : IsBender (MulAction.stabilizer G ω₁') :=
    (isStronglyEmbedded_iff _).mp hKss |>.2
  have hKne : MulAction.stabilizer G ω₁' ≠ ⊤ := ((isStronglyEmbedded_iff _).mp hKss).1
  have hdtp : Submission.Blueprint.twoPoint (MulAction.stabilizer G ω₁') t' =
      MulAction.stabilizer G ω₁' ⊓ MulAction.stabilizer G ω₂' := by
    rw [Submission.Blueprint.twoPoint,
      ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t' ω₁', ht'ω]
  have hKcard : (Submission.Blueprint.involutions (MulAction.stabilizer G ω₁' : Set G)).ncard =
      (Submission.Blueprint.involutions (H : Set G)).ncard := by
    have h := Work.ThreePoints.S4Prop2.ncard_involutions_stabilizer_eq (K := H) ω₁' (pt H)
    rwa [stabilizer_pt_eq] at h
  -- the hypothesis of Appendix I (3)(d)
  have hkey : ∃ P : Subgroup G,
      P ≤ Submission.Blueprint.twoPoint (MulAction.stabilizer G ω₁') t' ∧ IsPGroup p P ∧
      ∃ u ∈ Submission.Blueprint.involutions (MulAction.stabilizer G ω₁' : Set G),
        u ∈ Subgroup.normalizer (P : Set G) ∧
        (Submission.Blueprint.involutions (MulAction.stabilizer G ω₁' : Set G)).ncard.factorization p
          ≤ (Work.DoubleTransitivity.conjOrbit P u).ncard.factorization p := by
    by_cases htK : t ∈ MulAction.stabilizer G ω₁'
    · -- Case 2: `u := t`, `P := Q₀`
      refine ⟨Q₀, ?_, hQ₀syl.2.1, t, ⟨htK, ht2⟩,
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr htQ₀, ?_⟩
      · rw [hdtp]; exact le_trans hQ₀Q (le_inf hQω₁' hQω₂')
      · have hnum := card_conjOrbit_sylow_eq_pPart hH hp ht2 hω₂₁ htω hQ₀syl htQ₀
        have h1 : (Work.DoubleTransitivity.conjOrbit Q₀ t).ncard.factorization p =
            (Submission.Blueprint.involutions (H : Set G)).ncard.factorization p := by
          rw [hnum, Work.ThreePoints.S4Prop2.factorization_pow_self hp]
        rw [hKcard, ← h1]
    · -- Case 1: the involution `u` supplied by the evenness hypothesis
      haveI : Fintype ↥(Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω₁') :=
        Fintype.ofFinite _
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G :=
        ↥(Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω₁')) 2
        (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hEven)
      have hu2 : orderOf ((u : G)) = 2 := (Subgroup.orderOf_coe u).trans hu
      have huN : (u : G) ∈ Subgroup.normalizer (Q : Set G) := u.2.1
      have huK : (u : G) ∈ MulAction.stabilizer G ω₁' := u.2.2
      refine ⟨Q, ?_, hQmax.1, u, ⟨huK, hu2⟩, huN, ?_⟩
      · rw [hdtp]; exact le_inf hQω₁' hQω₂'
      · -- `v_p |Inv (Stab ω₁')| ≤ v_p |u ^ Q|`
        have hnum := card_conjOrbit_sylow_eq_pPart hH hp ht2 hω₂₁ htω hQ₀syl htQ₀
        have hQ₀odd : Odd (Nat.card ↥Q₀) :=
          odd_card_of_isPGroup_of_odd_prime hp hp2 hQ₀syl.2.1
        have htQ₀' : t ∈ Subgroup.normalizer (Q₀ : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr htQ₀
        have h1 : (Submission.Blueprint.invertedBy Q₀ t).ncard =
            p ^ ((Submission.Blueprint.involutions (H : Set G)).ncard.factorization p) := by
          rw [Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit ht2 hQ₀odd htQ₀', hnum]
        have h2 : (Submission.Blueprint.invertedBy Q₀ t).ncard ≤
            (Submission.Blueprint.invertedBy Q t).ncard :=
          Set.ncard_le_ncard (fun x hx => ⟨hQ₀Q hx.1, hx.2⟩)
        have h3 : (Submission.Blueprint.invertedBy Q t).ncard ≤
            (Work.DoubleTransitivity.conjOrbit Q (u : G)).ncard :=
          Work.DoubleTransitivity.Sec2.lemma1 hKB hKne hQω₁'
            (odd_card_of_isPGroup_of_odd_prime hp hp2 hQmax.1) ⟨huK, hu2⟩ ht2 htK
        have h4 : p ^ ((Submission.Blueprint.involutions (H : Set G)).ncard.factorization p) ≤
            (Work.DoubleTransitivity.conjOrbit Q (u : G)).ncard := by
          rw [← h1]; exact le_trans h2 h3
        have h5 : (Work.DoubleTransitivity.conjOrbit Q (u : G)).ncard =
            p ^ ((Work.DoubleTransitivity.conjOrbit Q (u : G)).ncard.factorization p) := by
          rw [Work.ThreePoints.S4Prop2.card_conjOrbit_eq_pow_sub hp hQmax.1 huN,
            Work.ThreePoints.S4Prop2.factorization_pow_self hp]
        rw [h5] at h4
        have h6 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h4
        rw [hKcard]
        exact h6
  -- Appendix I (3)(d) turns this into a `p`-regular intersection
  have hreg : IsRegularIntersection p
      (MulAction.stabilizer G ω₁' ⊓ MulAction.stabilizer G ω₂')
      (MulAction.stabilizer G ω₁') := by
    have h := Work.ThreePoints.S4Prop2.isRegularIntersection_of_invariant hKss hp ht'2 ht'K hkey
    rwa [hdtp] at h
  -- every `p`-Sylow of the two-point stabiliser has an even normaliser in `Stab ω₁'`
  have hEvenAll : ∀ R : Subgroup G,
      IsSylowSubgroupOf p R (MulAction.stabilizer G ω₁' ⊓ MulAction.stabilizer G ω₂') →
      Even (Nat.card ↥(Subgroup.normalizer (R : Set G) ⊓ MulAction.stabilizer G ω₁')) :=
    fun R hR => even_normalizer_of_isRegularIntersection_sylow hp hreg inf_le_left hR
  have hQD : Q ≤ MulAction.stabilizer G ω₁' ⊓ MulAction.stabilizer G ω₂' := le_inf hQω₁' hQω₂'
  obtain ⟨R', hQR', hR'syl⟩ := exists_isSylowSubgroupOf_le hQmax.1 hQD
  have hR'3 : 3 ≤ (fixedPts H R').ncard := by
    have h2 : 2 ≤ (fixedPts H R').ncard := by
      have hsub : ({ω₁', ω₂'} : Set (Omega H)) ⊆ fixedPts H R' := by
        intro y hy
        rcases hy with rfl | rfl
        · exact mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hR'syl.1 inf_le_left)
        · exact mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hR'syl.1 inf_le_right)
      have hle := Set.ncard_le_ncard hsub
      rwa [Set.ncard_pair (fun h => hne h.symm)] at hle
    exact three_le_fixedPts_of_even_normalizer (((isStronglyEmbedded_iff H).mp hH).2)
      (mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hR'syl.1 inf_le_left))
      (hEvenAll R' hR'syl) h2
  have hR'Q : R' ≤ Q := hQmax.2.2 R' hR'syl.2.1 hR'3 hQR'
  have hQeq : Q = R' := le_antisymm hQR' hR'Q
  rw [hQeq]
  exact hR'syl

end Work.DoubleTransitivity.Sec4
