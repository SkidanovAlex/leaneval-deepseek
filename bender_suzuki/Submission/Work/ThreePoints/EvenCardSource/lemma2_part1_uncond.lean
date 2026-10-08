import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.lemma2_part1
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.DoubleTransitivity.Sec4.RpDefs
import Submission.Work.ThreePoints.S4Prop2.sec4_basic
import Submission.Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit
import Submission.Work.ThreePoints.S4Prop2.ncard_involutions_conj
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.DoubleTransitivity
open Work.DoubleTransitivity.Sec4
open scoped Pointwise

namespace Work.ThreePoints.EvenCardSource

/-- **Peterfalvi I Ch. I §4 Lemma 2, part 1 (pp. 155–156), with the unused Brauer–Suzuki
hypothesis removed.**  This is `Work.DoubleTransitivity.Sec4.lemma2_part1` (which is the
`Submission.Blueprint.BrauerSuzukiProp`-indexed form of the same claim) with its parameter
`hBrSz : Submission.Blueprint.BrauerSuzukiProp` deleted: that parameter is **not used anywhere** in
the proof of `Work.DoubleTransitivity.Sec4.lemma2_part1`, so this is a verbatim transcription of
that proof with the parameter removed from the signature.  Do not re-derive anything: copy the
proof text of `Work.DoubleTransitivity.Sec4.lemma2_part1`
(`Submission/Work/DoubleTransitivity/Sec4/lemma2_part1.lean`) and delete `hBrSz` from the binders.

The claim (`Work.DoubleTransitivity.Sec4.Sec4Lemma2Part1 p H`, see
`Submission/Work/DoubleTransitivity/Sec4/RpDefs.lean`): if `Q` is maximal among the `p`-subgroups of
`G` with at least three fixed points of `Ω = G ⧸ H`, `Q` contains a `p`-Sylow of a two-point
stabiliser, and two distinct fixed points `ω₁, ω₂` of `Q` satisfy
`Even (|N_G(Q) ⊓ Stab_G(ω₁)|)`, then `Q` is a `p`-Sylow subgroup of `Stab_G(ω₁) ⊓ Stab_G(ω₂)`.

All the auxiliary results it uses are `hole`-free and listed in `depends_on`; in particular the
`card_conjOrbit_sylow_eq_pPart`, `even_normalizer_of_isRegularIntersection_sylow` and
`odd_card_of_isPGroup_of_odd_prime` helpers in the same source file, and
`Work.ThreePoints.S4Prop2.isRegularIntersection_of_invariant` in
`Submission/Work/ThreePoints/S4Prop2/even_card_normalizer_of_maximal_p_subgroup_gen.lean` (use that
module only for those `hole`-free helpers; do **not** use its `sec3_prop1_exists`,
`even_card_normalizer_of_maximal_p_subgroup_gen` or any other declaration from a module containing a
`hole`, in particular nothing from `Work.BrauerSuzuki.Q8/`, `Q8U/`, `Arith/`, and not
`Work.ThreePoints.brauerSuzukiProp_from_cases`, `Work.ThreePoints.involution_commutator_mem_oddCore`,
`Work.ThreePoints.S4Prop2.no_two_fixed_pts`). -/
theorem lemma2_part1_uncond {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Work.DoubleTransitivity.Sec4.Sec4Lemma2Part1 p H := by
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

end Work.ThreePoints.EvenCardSource
