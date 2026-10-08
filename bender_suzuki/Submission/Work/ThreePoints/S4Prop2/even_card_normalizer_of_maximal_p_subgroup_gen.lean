import Mathlib
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.App1.Defs
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.DoubleTransitivity.App2.app2_1
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.DoubleTransitivity.App2.app2_4
import Submission.Work.DoubleTransitivity.App1.app1_2
import Submission.Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.ThreePoints.S4Prop2.ncard_involutions_conj
import Submission.Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour
import Submission.Work.DoubleTransitivity.Sec4.RpDefs
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.DoubleTransitivity.Sec4.not_rp_twoTransitive
import Submission.Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts
import Submission.Work.ThreePoints.S4Prop2.sec4_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Ch. I §4 Prop. 2 without the `2`-rank hypothesis

Peterfalvi I Ch. I §4 Prop. 2 (p. 156) states: for `H ∈ Ω`, `P` maximal among the `p`-subgroups of
`H` fixing at least three points of `Ω = G ⧸ H`, the subgroup `P` is maximal among the
`p`-subgroups of `G` fixing three points and `|N_H(P)|` is even.  The workspace theorem
`Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup` proves the evenness under the extra
hypotheses `HasFourGroup F` and `ThmAProp` (which it uses to obtain 2-transitivity of `F` on `Ω`);
the present file removes both, following the source's own Case 1/Case 2 analysis and introducing
the `p`-regular intersections of §4.
-/

namespace Work.ThreePoints.S4Prop2

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary Sylow facts -/

/-- A proper subgroup `R` of a finite `p`-group `S`, with `S ≤ X`, has `p`-divisible index in `X`. -/
theorem dvd_index_of_lt_of_isPGroup {p : ℕ} (hp : p.Prime)
    {R S X : Subgroup G} (hRp : IsPGroup p R) (hSp : IsPGroup p S) (hRS : R < S) (hSX : S ≤ X) :
    p ∣ (R.subgroupOf X).index := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hRX : R ≤ X := hRS.le.trans hSX
  have e1 : Nat.card ↥R * (R.subgroupOf X).index = Nat.card ↥X := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv]
    exact Subgroup.card_mul_index _
  have e2 : Nat.card ↥R * (R.subgroupOf S).index = Nat.card ↥S := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS.le).toEquiv]
    exact Subgroup.card_mul_index _
  have e3 : Nat.card ↥S * (S.subgroupOf X).index = Nat.card ↥X := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv]
    exact Subgroup.card_mul_index _
  have hmul : (R.subgroupOf X).index = (R.subgroupOf S).index * (S.subgroupOf X).index := by
    refine Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card ↥R from Nat.card_pos) ?_
    calc Nat.card ↥R * (R.subgroupOf X).index
        = Nat.card ↥X := e1
      _ = Nat.card ↥S * (S.subgroupOf X).index := e3.symm
      _ = (Nat.card ↥R * (R.subgroupOf S).index) * (S.subgroupOf X).index := by rw [e2]
      _ = Nat.card ↥R * ((R.subgroupOf S).index * (S.subgroupOf X).index) := by ring
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hRp
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hSp
  have hcardlt : Nat.card ↥R < Nat.card ↥S := by
    have hdvd : Nat.card ↥R ∣ Nat.card ↥S := Subgroup.card_dvd_of_le hRS.le
    refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) ?_
    intro h
    exact hRS.ne (Subgroup.eq_of_le_of_card_ge hRS.le (le_of_eq h.symm))
  have hab : a < b := by
    rw [← Nat.pow_lt_pow_iff_right hp.one_lt, ← ha, ← hb]; exact hcardlt
  have hidx : (R.subgroupOf S).index = p ^ (b - a) := by
    have h := e2
    rw [ha, hb] at h
    have h' : p ^ a * p ^ (b - a) = p ^ b := by rw [← pow_add, Nat.add_sub_cancel' hab.le]
    rw [← h'] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a) h
  have hdvd : p ∣ p ^ (b - a) := by
    have h : p ^ 1 ∣ p ^ (b - a) := pow_dvd_pow p (by omega)
    simpa using h
  rw [hmul, hidx]
  exact dvd_mul_of_dvd_left hdvd _

/-- If a `p`-subgroup `P ≤ X` is a `p`-Sylow subgroup of its normaliser inside `X`, then it is a
`p`-Sylow subgroup of `X`.  (If not, some strictly larger `p`-subgroup `S ≤ X` would have
`P < N_S(P) ≤ X ⊓ N_G(P)`, contradicting the hypothesis.) -/
theorem isSylow_of_isSylow_normalizer {p : ℕ} (hp : p.Prime) {P X : Subgroup G}
    (hPX : P ≤ X) (hPp : IsPGroup p P)
    (h : ¬ p ∣ (P.subgroupOf (X ⊓ Subgroup.normalizer (P : Set G))).index) :
    ¬ p ∣ (P.subgroupOf X).index := by
  intro hcon
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSX, hSp, hPS⟩ := Work.ThreePoints.exists_pSubgroup_lt_of_dvd_index hp hPp hPX hcon
  have hlt : P < S ⊓ Subgroup.normalizer (P : Set G) := Work.Coprime.lt_inf_normalizer_of_lt hSp hPS
  have hle : S ⊓ Subgroup.normalizer (P : Set G) ≤ X ⊓ Subgroup.normalizer (P : Set G) :=
    inf_le_inf_right _ hSX
  exact h (dvd_index_of_lt_of_isPGroup hp hPp hSp.to_inf_left hlt hle)

/-! ## Ch. I §3 Prop. 1 in the existence form -/

/-- Auxiliary for `sec3_prop1_exists`, Case 1: the contradiction when all `N_G(Q)`-orbits on `Ω_Q`
have at most two points. -/
theorem sec3_prop1_case1 {K : Subgroup G} (hK : IsStronglyEmbedded K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    {Q : Subgroup G} (hQp : IsPGroup p Q)
    (hQmax : ∀ R : Subgroup G, Q ≤ R → IsPGroup p R → 3 ≤ (fixedPts K R).ncard → R = Q)
    (hsmall : ¬ ∃ ω₀ ∈ fixedPts K Q, ∃ m₁ ∈ Subgroup.normalizer (Q : Set G),
      ∃ m₂ ∈ Subgroup.normalizer (Q : Set G),
        m₁ • ω₀ ≠ ω₀ ∧ m₂ • ω₀ ≠ ω₀ ∧ m₂ • ω₀ ≠ m₁ • ω₀)
    {ω₁ ω₂ ω₃ : G ⧸ K} (hω₁ : ω₁ ∈ fixedPts K Q) (hω₂ : ω₂ ∈ fixedPts K Q)
    (hω₃ : ω₃ ∈ fixedPts K Q)
    (hnot : ¬ ∃ m ∈ Subgroup.normalizer (Q : Set G), m • ω₁ = ω₂)
    (hne₁ : ω₃ ≠ ω₁) (hne₂ : ω₃ ≠ ω₂) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup G := Subgroup.normalizer (Q : Set G) with hN
  have hne : ω₁ ≠ ω₂ := fun h => hnot ⟨1, N.one_mem, by rw [one_smul, h]⟩
  have hQ₁ : Q ≤ MulAction.stabilizer G ω₁ := mem_fixedPts_iff_le_stabilizer.mp hω₁
  have hQ₂ : Q ≤ MulAction.stabilizer G ω₂ := mem_fixedPts_iff_le_stabilizer.mp hω₂
  have hQN : Q ≤ N := Subgroup.le_normalizer
  set D : Subgroup G := MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂ ⊓ N with hD
  have hQD : Q ≤ D := le_inf (le_inf hQ₁ hQ₂) hQN
  -- `Q` is not a `p`-Sylow of `D`
  have hnotsyl : p ∣ (Q.subgroupOf D).index := by
    by_contra hcon
    have hsyl : ¬ p ∣ (Q.subgroupOf (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂)).index :=
      isSylow_of_isSylow_normalizer hp (le_inf hQ₁ hQ₂) hQp hcon
    obtain ⟨u, -, huQ, huω⟩ :=
      sec3_lemma1 hK hp hne ⟨le_inf hQ₁ hQ₂, hQp, hsyl⟩
    exact hnot ⟨u, Subgroup.mem_normalizer_iff_map_conj_eq.mpr huQ, huω⟩
  obtain ⟨R, hRD, hRp, hQR⟩ :=
    Work.ThreePoints.exists_pSubgroup_lt_of_dvd_index hp hQp hQD hnotsyl
  have hR12 : R ≤ MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂ := le_trans hRD inf_le_left
  have hR1 : R ≤ MulAction.stabilizer G ω₁ := le_trans hR12 inf_le_left
  have hR2 : R ≤ MulAction.stabilizer G ω₂ := le_trans hR12 inf_le_right
  have hRN : R ≤ N := le_trans hRD inf_le_right
  have hω₁R : ω₁ ∈ fixedPts K R := mem_fixedPts_iff_le_stabilizer.mpr hR1
  have hω₂R : ω₂ ∈ fixedPts K R := mem_fixedPts_iff_le_stabilizer.mpr hR2
  -- `Ω_R = {ω₁, ω₂}`
  have hRf : fixedPts K R = {ω₁, ω₂} := by
    have hsub : ({ω₁, ω₂} : Set (G ⧸ K)) ⊆ fixedPts K R := by
      intro x hx; rcases hx with h | h <;> rw [h] <;> assumption
    have hnot3 : ¬ 3 ≤ (fixedPts K R).ncard := fun h3 => hQR.ne (hQmax R hQR.le hRp h3).symm
    have hle2 : (fixedPts K R).ncard ≤ 2 := by omega
    refine (Set.eq_of_subset_of_ncard_le hsub ?_).symm
    rw [Set.ncard_pair hne]
    exact hle2
  -- `ω₃ ∉ Ω_R`
  have hω₃not : ω₃ ∉ fixedPts K R := by
    intro h; rw [hRf] at h; rcases h with h | h
    · exact hne₁ h
    · exact hne₂ h
  -- `R ⊓ Stab(ω₃) = Q`
  have hstab : R ⊓ MulAction.stabilizer G ω₃ = Q := by
    refine hQmax (R ⊓ MulAction.stabilizer G ω₃)
      (le_inf hQR.le (mem_fixedPts_iff_le_stabilizer.mp hω₃)) hRp.to_inf_left ?_
    have hsub : ({ω₁, ω₂, ω₃} : Set (G ⧸ K)) ⊆ fixedPts K (R ⊓ MulAction.stabilizer G ω₃) := by
      intro x hx
      rw [mem_fixedPts_iff_le_stabilizer]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h
      · rw [h]; exact le_trans inf_le_left hR1
      · rw [h]; exact le_trans inf_le_left hR2
      · rw [h]; exact inf_le_right
    have hcard : ({ω₁, ω₂, ω₃} : Set (G ⧸ K)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            rintro (h | h)
            · exact hne h
            · exact hne₁ h.symm),
          Set.ncard_insert_of_notMem (by
            simp only [Set.mem_singleton_iff]
            rintro h
            exact hne₂ h.symm)]
      simp
    rw [← hcard]
    exact Set.ncard_le_ncard hsub
  -- a point of `R` outside `Q`
  obtain ⟨r, hrR, hrQ⟩ : ∃ r ∈ R, r ∉ Q := by
    by_contra hc
    push_neg at hc
    exact hQR.ne (le_antisymm hQR.le hc)
  have hrN : r ∈ N := hRN hrR
  have hrstab : r • ω₃ ≠ ω₃ := by
    intro h
    exact hrQ (by rw [← hstab]; exact ⟨hrR, MulAction.mem_stabilizer_iff.mpr h⟩)
  -- every element of `R` is in `Q` or in `r · Q`
  have hcover : ∀ k ∈ R, k ∈ Q ∨ ∃ q ∈ Q, k = r * q := by
    intro k hk
    by_cases hkQ : k ∈ Q
    · exact Or.inl hkQ
    refine Or.inr ?_
    have hkstab : k • ω₃ ≠ ω₃ := by
      intro h
      exact hkQ (by rw [← hstab]; exact ⟨hk, MulAction.mem_stabilizer_iff.mpr h⟩)
    have hEq : k • ω₃ = r • ω₃ := by
      by_contra hc
      exact hsmall ⟨ω₃, hω₃, r, hrN, k, hRN hk, hrstab, hkstab, hc⟩
    have h1 : (r⁻¹ * k) • ω₃ = ω₃ := by
      rw [mul_smul, hEq, ← mul_smul, inv_mul_cancel, one_smul]
    have h2 : r⁻¹ * k ∈ Q := by
      rw [← hstab]
      exact ⟨R.mul_mem (R.inv_mem hrR) hk, MulAction.mem_stabilizer_iff.mpr h1⟩
    exact ⟨r⁻¹ * k, h2, by group⟩
  -- hence `r * r ∈ Q`, and then `r ∈ ⟨r * r⟩ ≤ Q`
  have hr2Q : r * r ∈ Q := by
    rcases hcover (r * r) (R.mul_mem hrR hrR) with h | ⟨q, hq, hqeq⟩
    · exact h
    · have hrQ' : r ∈ Q := mul_left_cancel hqeq ▸ hq
      exact Q.mul_mem hrQ' hrQ'
  have hodd : Odd (orderOf r) := by
    have hdvd : orderOf r ∣ Nat.card ↥R := by
      have h := orderOf_dvd_natCard (⟨r, hrR⟩ : ↥R)
      rwa [Subgroup.orderOf_mk] at h
    have hRodd : Odd (Nat.card ↥R) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hRp
      rw [hn]
      exact (hp.odd_of_ne_two hp2).pow
    exact Odd.of_dvd hdvd hRodd
  obtain ⟨j, hj⟩ := hodd
  have hpow : (r * r) ^ (j + 1) = r := by
    rw [← pow_two, ← pow_mul]
    have h2 : 2 * (j + 1) = orderOf r + 1 := by rw [hj]; ring
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hmem : r ∈ Subgroup.zpowers (r * r) := by
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨(j + 1 : ℕ), by rw [zpow_natCast]; exact hpow⟩
  exact hrQ (Subgroup.zpowers_le.mpr hr2Q hmem)

/-- Auxiliary for `sec3_prop1_exists`, Case 2: the Brauer–Suzuki argument when some
`N_G(Q)`-orbit on `Ω_Q` has at least three points. -/
theorem sec3_prop1_case2 {K : Subgroup G} (hK : IsStronglyEmbedded K)
    (hBrSz : BrauerSuzukiProp) {p : ℕ} (hp : p.Prime) {Q : Subgroup G} (hQp : IsPGroup p Q)
    (hQmax : ∀ R : Subgroup G, Q ≤ R → IsPGroup p R → 3 ≤ (fixedPts K R).ncard → R = Q)
    (hB : ¬ HasFourGroup (Subgroup.normalizer (Q : Set G)))
    {ω₀ : G ⧸ K} (hω₀ : ω₀ ∈ fixedPts K Q)
    {m₁ m₂ : G} (hm₁ : m₁ ∈ Subgroup.normalizer (Q : Set G))
    (hm₂ : m₂ ∈ Subgroup.normalizer (Q : Set G))
    (hne₁ : m₁ • ω₀ ≠ ω₀) (hne₂ : m₂ • ω₀ ≠ ω₀) (hne₁₂ : m₂ • ω₀ ≠ m₁ • ω₀) :
    ∃ ω ∈ fixedPts K Q,
      Even (Nat.card (MulAction.stabilizer G ω ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set M : Subgroup G := Subgroup.normalizer (Q : Set G) with hMdef
  have hω₁ : m₁ • ω₀ ∈ fixedPts K Q :=
    Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hm₁ hω₀
  have hω₂ : m₂ • ω₀ ∈ fixedPts K Q :=
    Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hm₂ hω₀
  obtain ⟨t₁, ht₁M, ht₁2, ht₁⟩ :=
    sec3_lemma3 hK hp hQp hQmax hω₀ hω₁ hne₁.symm ⟨m₁, hm₁, rfl⟩
  obtain ⟨t₂, ht₂M, ht₂2, ht₂⟩ :=
    sec3_lemma3 hK hp hQp hQmax hω₀ hω₂ hne₂.symm ⟨m₂, hm₂, rfl⟩
  have ht₁sq : t₁ * t₁ = 1 := mul_self_eq_one_of_orderOf_eq_two ht₁2
  have ht₂sq : t₂ * t₂ = 1 := mul_self_eq_one_of_orderOf_eq_two ht₂2
  have hprodM : t₁ * t₂ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).mul_mem ht₁M ht₂M
  have hω' : (t₁ * t₂) • ω₀ ∈ fixedPts K Q :=
    Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hprodM hω₀
  have hne' : ω₀ ≠ (t₁ * t₂) • ω₀ := by
    intro hcon
    have h1 : t₁ • ((t₁ * t₂) • ω₀) = m₂ • ω₀ := by
      rw [mul_smul, ← mul_smul, ht₁sq, one_smul, ht₂]
    have h2 : t₁ • ω₀ = t₁ • ((t₁ * t₂) • ω₀) := congrArg (fun y => t₁ • y) hcon
    exact hne₁₂ (ht₁.symm.trans (h2.trans h1)).symm
  obtain ⟨t, htM, ht2, ht⟩ := sec3_lemma3 hK hp hQp hQmax hω₀ hω' hne' ⟨t₁ * t₂, hprodM, rfl⟩
  have htsq : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht2
  have hxmem : t₂ * t₁ * t ∈ M := M.mul_mem (M.mul_mem ht₂M ht₁M) htM
  have hxfix : (t₂ * t₁ * t) • ω₀ = ω₀ := by
    rw [mul_smul, mul_smul, ht, mul_smul]
    have h1 : t₁ • (t₁ • (t₂ • ω₀)) = t₂ • ω₀ := by
      rw [← mul_smul, ht₁sq, one_smul]
    rw [h1, ← mul_smul, ht₂sq, one_smul]
  refine ⟨ω₀, hω₀, ?_⟩
  refine even_iff_two_dvd.mpr ?_
  have hmem : (t₂ * t₁ * t) ∈ (MulAction.stabilizer G ω₀ ⊓ M : Subgroup G) :=
    ⟨MulAction.mem_stabilizer_iff.mpr hxfix, hxmem⟩
  set t₁' : M := ⟨t₁, ht₁M⟩
  set t₂' : M := ⟨t₂, ht₂M⟩
  set t' : M := ⟨t, htM⟩
  have ht₁2' : orderOf t₁' = 2 := by rw [← Subgroup.orderOf_coe t₁']; exact ht₁2
  have ht₂2' : orderOf t₂' = 2 := by rw [← Subgroup.orderOf_coe t₂']; exact ht₂2
  have ht2' : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe t']; exact ht2
  have htsq' : t' * t' = 1 := mul_self_eq_one_of_orderOf_eq_two ht2'
  have hO : (Submission.Blueprint.oddCore M).Normal := Work.BrauerSuzuki.oddCore_normal M
  have hprodO : t₂' * t₁' ∈ Submission.Blueprint.oddCore M :=
    involution_mul_involution_mem_oddCore hBrSz hB ht₂2' ht₁2'
  have htO : t' ∉ Submission.Blueprint.oddCore M := by
    intro hcon
    have hdvd : 2 ∣ Nat.card ↥(Submission.Blueprint.oddCore M) := by
      have h := orderOf_dvd_natCard (⟨t', hcon⟩ : ↥(Submission.Blueprint.oddCore M))
      rwa [Subgroup.orderOf_mk, ht2'] at h
    exact (Nat.not_even_iff_odd.mpr
      (Work.BrauerSuzuki.OddCore.oddCard_oddCore (G := M))) (even_iff_two_dvd.mpr hdvd)
  have hx2O : (t₂' * t₁' * t') * (t₂' * t₁' * t') ∈ Submission.Blueprint.oddCore M := by
    have h : t' * (t₂' * t₁') * t' ∈ Submission.Blueprint.oddCore M := by
      have h' := hO.conj_mem (t₂' * t₁') hprodO t'
      rwa [inv_eq_of_mul_eq_one_right htsq'] at h'
    have h1 : (t₂' * t₁' * t') * (t₂' * t₁' * t') =
        (t₂' * t₁') * (t' * (t₂' * t₁') * t') := by group
    rw [h1]
    exact (Submission.Blueprint.oddCore M).mul_mem hprodO h
  have hxtO : (t₂' * t₁' * t') * t' ∈ Submission.Blueprint.oddCore M := by
    have h1 : (t₂' * t₁' * t') * t' = t₂' * t₁' := by rw [mul_assoc, htsq', mul_one]
    rw [h1]; exact hprodO
  have hxO : (t₂' * t₁' * t') ∉ Submission.Blueprint.oddCore M := by
    intro hcon
    refine htO ?_
    have h1 : (t₂' * t₁' * t')⁻¹ * ((t₂' * t₁' * t') * t') = t' := by group
    rw [← h1]
    exact (Submission.Blueprint.oddCore M).mul_mem
      ((Submission.Blueprint.oddCore M).inv_mem hcon) hxtO
  have hxeven : Even (orderOf (t₂' * t₁' * t')) := by
    by_contra hcon
    have hodd : Odd (orderOf (t₂' * t₁' * t')) := Nat.not_even_iff_odd.mp hcon
    obtain ⟨j, hj⟩ := hodd
    have hpow : (t₂' * t₁' * t') = ((t₂' * t₁' * t') * (t₂' * t₁' * t')) ^ (j + 1) := by
      rw [← pow_two, ← pow_mul]
      have h2 : 2 * (j + 1) = orderOf (t₂' * t₁' * t') + 1 := by rw [hj]; ring
      rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
    exact hxO (hpow ▸ pow_mem hx2O (j + 1))
  have hxevenG : Even (orderOf (t₂ * t₁ * t)) := by
    have hcoee : (((t₂' * t₁' * t') : M) : G) = t₂ * t₁ * t := rfl
    rw [← hcoee, Subgroup.orderOf_coe]
    exact hxeven
  refine dvd_trans (even_iff_two_dvd.mp hxevenG) ?_
  have hord : orderOf (⟨t₂ * t₁ * t, hmem⟩ :
      ↥(MulAction.stabilizer G ω₀ ⊓ M : Subgroup G)) = orderOf (t₂ * t₁ * t) :=
    Subgroup.orderOf_mk _ _
  rw [← hord]
  exact orderOf_dvd_natCard _

/-- **Peterfalvi I Ch. I §3 Prop. 1** (existence form, p. 153).  If `K` is strongly embedded in
the finite group `G` (`Ω = G ⧸ K`), `p ≠ 2` is a prime and `Q` is maximal among the `p`-subgroups
of `G` with at least three fixed points of `Ω`, then some `H ∈ Ω_Q` contains an involution
normalising `Q`, i.e. `|N_H(Q)|` is even.

This is `Work.ThreePoints.sec3_prop1_transitive` with the transitivity hypothesis removed. -/
theorem sec3_prop1_exists {K : Subgroup G} (hK : IsStronglyEmbedded K)
    (hBrSz : BrauerSuzukiProp) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup G} (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup G, Q ≤ R → IsPGroup p R → 3 ≤ (fixedPts K R).ncard → R = Q) :
    ∃ ω ∈ fixedPts K Q,
      Even (Nat.card (MulAction.stabilizer G ω ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set M : Subgroup G := Subgroup.normalizer (Q : Set G) with hMdef
  have hQodd : Odd (Nat.card ↥Q) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    haveI : Fintype ↥Q := Fintype.ofFinite ↥Q
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥Q) 2
      (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hev)
    obtain ⟨n, hn⟩ := hQp x
    have hxG : orderOf ((x : Q) : G) = 2 := (Subgroup.orderOf_coe x).trans hx
    have h2dvd : 2 ∣ p ^ n := by
      rw [← hxG]
      exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg (fun y : Q => (y : G)) hn)
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  by_cases h4 : HasFourGroup M
  · -- Case A: `N_G(Q)` has `2`-rank `≥ 2`
    obtain ⟨t, ht2⟩ : ∃ t : M, orderOf t = 2 := by
      obtain ⟨t, -, ht2, -, -, -⟩ := h4
      exact ⟨t, ht2⟩
    have htG : orderOf ((t : G)) = 2 := (Subgroup.orderOf_coe t).trans ht2
    obtain ⟨ω, hωfix, -⟩ := existsUnique_fixedPts_of_orderOf_eq_two hK htG
    have hle : Q ≤ MulAction.stabilizer G ω :=
      le_stabilizer_of_involution_mem_normalizer hK hQodd h4 ⟨t.2, htG⟩ hωfix
    refine ⟨ω, mem_fixedPts_iff_le_stabilizer.mpr hle, ?_⟩
    have hmem : (t : G) ∈ (MulAction.stabilizer G ω ⊓ M : Subgroup G) :=
      ⟨MulAction.mem_stabilizer_iff.mpr hωfix, t.2⟩
    refine even_iff_two_dvd.mpr ?_
    have hord : orderOf (⟨(t : G), hmem⟩ :
        ↥(MulAction.stabilizer G ω ⊓ M : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact htG
    exact dvd_trans (by rw [hord]) (orderOf_dvd_natCard _)
  · -- Case B: `N_G(Q)` has `2`-rank `1`
    have hB : ¬ HasFourGroup M := h4
    have hΩne : (fixedPts K Q).Nonempty := by rw [← Set.ncard_pos]; omega
    by_cases hbig : ∃ ω₀ ∈ fixedPts K Q, ∃ m₁ ∈ M, ∃ m₂ ∈ M,
        m₁ • ω₀ ≠ ω₀ ∧ m₂ • ω₀ ≠ ω₀ ∧ m₂ • ω₀ ≠ m₁ • ω₀
    · obtain ⟨ω₀, hω₀, m₁, hm₁, m₂, hm₂, hne₁, hne₂, hne₁₂⟩ := hbig
      exact sec3_prop1_case2 hK hBrSz hp hQp hQmax hB hω₀ hm₁ hm₂ hne₁ hne₂ hne₁₂
    · exfalso
      -- two different points of `Ω_Q` in different `M`-orbits
      have htwo : ∃ ω₁ ∈ fixedPts K Q, ∃ ω₂ ∈ fixedPts K Q,
          ¬ ∃ m ∈ M, m • ω₁ = ω₂ := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨ω₁, hω₁⟩ := hΩne
        obtain ⟨x, hx, hxne⟩ :=
          Set.exists_ne_of_one_lt_ncard (by omega : 1 < (fixedPts K Q).ncard) ω₁
        have h2 : 1 < ((fixedPts K Q) \ {ω₁}).ncard := by
          have h1 := Set.ncard_sdiff_singleton_add_one hω₁
          omega
        obtain ⟨y, hy, hyne⟩ := Set.exists_ne_of_one_lt_ncard h2 x
        obtain ⟨mx, hmx, hmx'⟩ := hcon ω₁ hω₁ x hx
        obtain ⟨my, hmy, hmy'⟩ := hcon ω₁ hω₁ y hy.1
        have hxne' : mx • ω₁ ≠ ω₁ := by rw [hmx']; exact hxne
        have hyne' : my • ω₁ ≠ ω₁ := by rw [hmy']; exact hy.2
        have hEq : mx • ω₁ = my • ω₁ := by
          by_contra hc
          exact hbig ⟨ω₁, hω₁, mx, hmx, my, hmy, hxne', hyne', fun h => hc h.symm⟩
        exact hyne (by rw [← hmx', ← hmy', hEq.symm])
      obtain ⟨ω₁, hω₁, ω₂, hω₂, hnot⟩ := htwo
      have h2 : 1 < ((fixedPts K Q) \ {ω₁}).ncard := by
        have h1 := Set.ncard_sdiff_singleton_add_one hω₁
        omega
      obtain ⟨ω₃, hω₃, hω₃ne⟩ := Set.exists_ne_of_one_lt_ncard h2 ω₂
      exact sec3_prop1_case1 hK hp hp2 hQp hQmax hbig hω₁ hω₂ hω₃.1 hnot hω₃.2 hω₃ne

/-! ## Ch. I §4: the `p`-regular intersection calculus -/

/-- Orbit–stabiliser for the conjugation action, in the form used in Appendix I (1)(a):
`|u^X| · |C_X(u)| = |X|` — no normalisation hypothesis on `X`. -/
theorem mul_ncard_conjOrbit_ncard_centralizer (X : Subgroup G) (u : G) :
    (Work.DoubleTransitivity.conjOrbit X u).ncard *
      Nat.card ↥(X ⊓ Subgroup.centralizer ({u} : Set G)) = Nat.card ↥X := by
  classical
  letI : MulAction ↥X G :=
    { smul := fun x g => (x : G) * g * (x : G)⁻¹
      one_smul := fun g => by
        show (1 : G) * g * (1 : G)⁻¹ = g
        group
      mul_smul := fun x y g => by
        show ((x : G) * (y : G)) * g * ((x : G) * (y : G))⁻¹ =
          (x : G) * ((y : G) * g * (y : G)⁻¹) * (x : G)⁻¹
        group }
  have horb : MulAction.orbit ↥X u = Work.DoubleTransitivity.conjOrbit X u := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G)⁻¹, X.inv_mem x.2, by
        show (x : G)⁻¹⁻¹ * u * (x : G)⁻¹ = (x : G) * u * (x : G)⁻¹
        rw [inv_inv]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x⁻¹, X.inv_mem hx⟩, by
        show (x⁻¹ : G) * u * (x⁻¹ : G)⁻¹ = x⁻¹ * u * x
        rw [inv_inv]⟩
  have hstab : MulAction.stabilizer ↥X u =
      (X ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf X := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : (x : G) * u * (x : G)⁻¹ = u := h
      refine ⟨x.2, ?_⟩
      calc (x : G) * u = ((x : G) * u * (x : G)⁻¹) * (x : G) := by group
        _ = u * (x : G) := by rw [h']
    · rintro ⟨-, h⟩
      show (x : G) * u * (x : G)⁻¹ = u
      rw [show (x : G) * u * (x : G)⁻¹ = u * ((x : G) * (x : G)⁻¹) by rw [h]; group]
      simp
  have hcard : Nat.card ↥(MulAction.stabilizer ↥X u) =
      Nat.card ↥(X ⊓ Subgroup.centralizer ({u} : Set G)) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer ↥X u)
  rw [MulAction.index_stabilizer, horb, hcard] at h2
  calc (Work.DoubleTransitivity.conjOrbit X u).ncard *
        Nat.card ↥(X ⊓ Subgroup.centralizer ({u} : Set G))
      = Nat.card ↥(X ⊓ Subgroup.centralizer ({u} : Set G)) *
        (Work.DoubleTransitivity.conjOrbit X u).ncard := mul_comm _ _
    _ = Nat.card ↥X := h2

/-- `N(Z) ∩ N(Q) ⊆ N(Z ⊓ N(Q))`. -/
theorem mem_normalizer_inf_normalizer {u : G} {Z Q : Subgroup G}
    (hZ : u ∈ Subgroup.normalizer (Z : Set G)) (hQ : u ∈ Subgroup.normalizer (Q : Set G)) :
    u ∈ Subgroup.normalizer (Z ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) := by
  have key : ∀ (g : G), g ∈ Subgroup.normalizer (Z : Set G) →
      g ∈ Subgroup.normalizer (Q : Set G) → ∀ z : G,
      z ∈ Z ⊓ Subgroup.normalizer (Q : Set G) →
      g * z * g⁻¹ ∈ Z ⊓ Subgroup.normalizer (Q : Set G) := by
    intro g hgZ hgQ z hz
    have hgQ' : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.normalizer (Q : Set G)).inv_mem hgQ
    refine ⟨(Subgroup.mem_normalizer_iff.mp hgZ z).mp hz.1, Subgroup.mem_normalizer_iff.mpr ?_⟩
    intro y
    have hxN : ∀ y, y ∈ Q ↔ z * y * z⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hz.2
    have hgy : ∀ y, y ∈ Q ↔ g * y * g⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hgQ
    have hgy' : ∀ y, y ∈ Q ↔ g⁻¹ * y * g⁻¹⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hgQ'
    rw [show g * z * g⁻¹ * y * (g * z * g⁻¹)⁻¹ =
        g * (z * (g⁻¹ * y * g) * z⁻¹) * g⁻¹ by group,
      ← hgy (z * (g⁻¹ * y * g) * z⁻¹), ← hxN (g⁻¹ * y * g)]
    simpa using hgy' y
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key u hZ hQ x
  · intro hx
    have h1 : u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x := by rw [inv_inv]; group
    exact h1 ▸ key u⁻¹ ((Subgroup.normalizer (Z : Set G)).inv_mem hZ)
      ((Subgroup.normalizer (Q : Set G)).inv_mem hQ) (u * x * u⁻¹) hx

/-- Monotonicity of the order of a subgroup. -/
theorem card_le_card_of_le {H K : Subgroup G} (h : H ≤ K) : Nat.card ↥H ≤ Nat.card ↥K := by
  haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h)

/-- A `p`-Sylow subgroup of `Y` has order the `p`-part of `|Y|`. -/
theorem card_of_isSylowSubgroupOf {p : ℕ} [Fact p.Prime] {R Y : Subgroup G}
    (hR : Work.DoubleTransitivity.IsSylowSubgroupOf p R Y) :
    Nat.card ↥R = p ^ (Nat.card ↥Y).factorization p := by
  obtain ⟨hRY, hRp, hidx⟩ := hR
  haveI : Nonempty ↥R := ⟨⟨1, R.one_mem⟩⟩
  haveI : Nonempty ↥Y := ⟨⟨1, Y.one_mem⟩⟩
  have hne : Nat.card ↥R ≠ 0 := Nat.card_pos.ne'
  have hidxne : (R.subgroupOf Y).index ≠ 0 := fun h => by
    have h1 := Subgroup.card_mul_index (R.subgroupOf Y)
    rw [h, mul_zero] at h1
    exact (Nat.card_pos.ne') h1.symm
  have hcard : Nat.card ↥Y = Nat.card ↥R * (R.subgroupOf Y).index := by
    have h := Subgroup.card_mul_index (R.subgroupOf Y)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRY).toEquiv] at h
    exact h.symm
  have hfac : (Nat.card ↥Y).factorization p = (Nat.card ↥R).factorization p := by
    rw [hcard, Nat.factorization_mul hne hidxne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  have hpow : Nat.card ↥R = p ^ (Nat.card ↥R).factorization p := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    rw [hk]
    congr 1
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.Prime.factorization (Fact.out : p.Prime), Finsupp.single_eq_same, mul_one]
  exact hfac.symm ▸ hpow

/-- **Appendix I (2)**, containment clause.  If `Z` is a `u`-invariant subgroup of odd order and
`P ≤ Z` is a `u`-invariant `p`-subgroup, then `P` is contained in a `u`-invariant `p`-Sylow of
`Z`. -/
theorem exists_invariant_sylow_ge {p : ℕ} (hp : p.Prime) {u : G} (hu : orderOf u = 2)
    {Z : Subgroup G} (hZodd : Odd (Nat.card ↥Z))
    (hZu : u ∈ Subgroup.normalizer (Z : Set G))
    {P : Subgroup G} (hPZ : P ≤ Z) (hPp : IsPGroup p P)
    (hPu : u ∈ Subgroup.normalizer (P : Set G)) :
    ∃ Q : Subgroup G, P ≤ Q ∧ Q ≤ Z ∧ IsPGroup p Q ∧ ¬ p ∣ (Q.subgroupOf Z).index ∧
      u ∈ Subgroup.normalizer (Q : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set φ : ℕ → Prop := fun m => ∃ Q : Subgroup G, P ≤ Q ∧ Q ≤ Z ∧ IsPGroup p Q ∧
      u ∈ Subgroup.normalizer (Q : Set G) ∧ Nat.card ↥Q = m with hφ
  have hex : ∃ m, φ m ∧ m ≤ Nat.card ↥Z :=
    ⟨Nat.card ↥P, ⟨⟨P, le_rfl, hPZ, hPp, hPu, rfl⟩,
      card_le_card_of_le hPZ⟩⟩
  obtain ⟨m₀, hm₀φ, hm₀le⟩ := hex
  obtain ⟨Q, hPQ, hQZ, hQp, hQu, hQcard⟩ := Nat.findGreatest_spec hm₀le hm₀φ
  have hQmax : ∀ Q' : Subgroup G, P ≤ Q' → Q' ≤ Z → IsPGroup p Q' →
      u ∈ Subgroup.normalizer (Q' : Set G) → Nat.card ↥Q' ≤ Nat.card ↥Q := by
    intro Q' h1 h2 h3 h4
    have h5 : Nat.card ↥Q' ≤ Nat.card ↥Z := card_le_card_of_le h2
    have h6 : ¬ (Nat.findGreatest φ (Nat.card ↥Z) < Nat.card ↥Q') :=
      fun hlt => Nat.findGreatest_is_greatest hlt h5 ⟨Q', h1, h2, h3, h4, rfl⟩
    have h7 : Nat.card ↥Q' ≤ Nat.findGreatest φ (Nat.card ↥Z) := not_lt.mp h6
    rwa [← hQcard] at h7
  set W : Subgroup G := Z ⊓ Subgroup.normalizer (Q : Set G) with hW
  have hWodd : Odd (Nat.card ↥W) := Odd.of_dvd (Subgroup.card_dvd_of_le inf_le_left) hZodd
  have hQW : Q ≤ W := le_inf hQZ Subgroup.le_normalizer
  have hWu : u ∈ Subgroup.normalizer (W : Set G) := mem_normalizer_inf_normalizer hZu hQu
  obtain ⟨R, hRsyl, hRu, _⟩ :=
    Work.DoubleTransitivity.App1.app1_2 (X := W) (t := u) (d := 2) Nat.prime_two hu
      (Nat.coprime_two_left.mpr hWodd) hWu hp
  have hle : Q ≤ R := by
    have hQw : IsPGroup p ↥(Q.subgroupOf W) :=
      hQp.comap_of_injective W.subtype Subtype.coe_injective
    obtain ⟨R'w, hQR'w⟩ := IsPGroup.exists_le_sylow hQw
    have hR'syl : Work.DoubleTransitivity.IsSylowSubgroupOf p
        (Subgroup.map W.subtype (R'w : Subgroup ↥W)) W :=
      Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype hp R'w
    have hQR' : Q ≤ Subgroup.map W.subtype (R'w : Subgroup ↥W) := by
      have h1 : (Q.subgroupOf W) ≤ (R'w : Subgroup ↥W) := hQR'w
      calc Q = Subgroup.map W.subtype (Q.subgroupOf W) :=
            (Subgroup.map_subgroupOf_eq_of_le hQW).symm
        _ ≤ Subgroup.map W.subtype (R'w : Subgroup ↥W) := Subgroup.map_mono h1
    obtain ⟨d, hdW, hd⟩ :=
      exists_conj_of_isSylowSubgroupOf hp hR'syl.1 hR'syl.2.1 hR'syl.2.2 hRsyl.1 hRsyl.2.1
        hRsyl.2.2
    have hWle : W ≤ Subgroup.normalizer (Q : Set G) := inf_le_right
    have hQconj : Submission.Blueprint.conj d Q = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWle hdW)
    rw [← hd, ← hQconj]
    exact Subgroup.map_mono hQR'
  have hQsylW : ¬ p ∣ (Q.subgroupOf W).index := by
    have heq : R = Q := (Subgroup.eq_of_le_of_card_ge hle
      (hQmax R (le_trans hPQ hle) (le_trans hRsyl.1 inf_le_left) hRsyl.2.1 hRu)).symm
    rw [← heq]
    exact hRsyl.2.2
  exact ⟨Q, hPQ, hQZ, hQp, isSylow_of_isSylow_normalizer hp hQZ hQp hQsylW, hQu⟩

/-- **Appendix I (3)(a)**.  For a `u`-invariant `p`-Sylow `P` of the `u`-invariant group `Z` of
odd order, `|C_P(u)|` is the `p`-part of `|C_Z(u)|`. -/
theorem card_centralizer_in_invariant_sylow {p : ℕ} (hp : p.Prime) {u : G} (hu : orderOf u = 2)
    {Z P : Subgroup G} (hZodd : Odd (Nat.card ↥Z)) (hZu : u ∈ Subgroup.normalizer (Z : Set G))
    (hPZ : P ≤ Z) (hPp : IsPGroup p P) (hPu : u ∈ Subgroup.normalizer (P : Set G))
    (hsyl : ¬ p ∣ (P.subgroupOf Z).index) :
    Nat.card ↥(P ⊓ Subgroup.centralizer ({u} : Set G)) =
      p ^ (Nat.card ↥(Z ⊓ Subgroup.centralizer ({u} : Set G))).factorization p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  have hCPp : IsPGroup p ↥((P ⊓ C).subgroupOf (Z ⊓ C)) :=
    (hPp.to_inf_left).comap_of_injective (Z ⊓ C).subtype Subtype.coe_injective
  obtain ⟨Rw, hCPRw⟩ := IsPGroup.exists_le_sylow hCPp
  set Q : Subgroup G := Subgroup.map (Z ⊓ C).subtype (Rw : Subgroup ↥(Z ⊓ C)) with hQ
  have hQsyl : Work.DoubleTransitivity.IsSylowSubgroupOf p Q (Z ⊓ C) :=
    Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype hp Rw
  have hCPQ : P ⊓ C ≤ Q := by
    have h1 : (P ⊓ C).subgroupOf (Z ⊓ C) ≤ (Rw : Subgroup ↥(Z ⊓ C)) := hCPRw
    calc P ⊓ C = Subgroup.map (Z ⊓ C).subtype ((P ⊓ C).subgroupOf (Z ⊓ C)) :=
          (Subgroup.map_subgroupOf_eq_of_le (inf_le_inf_right _ hPZ)).symm
      _ ≤ Subgroup.map (Z ⊓ C).subtype (Rw : Subgroup ↥(Z ⊓ C)) := Subgroup.map_mono h1
  have hQZ : Q ≤ Z := le_trans hQsyl.1 inf_le_left
  have hQC : Q ≤ C := le_trans hQsyl.1 inf_le_right
  have hQu : u ∈ Subgroup.normalizer (Q : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro x
    constructor
    · intro hx
      have hxC : u * x = x * u := (Subgroup.mem_centralizer_iff.mp (hQC hx)) u (by simp)
      rw [show u * x * u⁻¹ = x by rw [hxC]; group]
      exact hx
    · intro hx
      have hxC : u * (u * x * u⁻¹) = (u * x * u⁻¹) * u :=
        (Subgroup.mem_centralizer_iff.mp (hQC hx)) u (by simp)
      have h1 : u⁻¹ * (u * x * u⁻¹) * u = u * x * u⁻¹ := by
        calc u⁻¹ * (u * x * u⁻¹) * u = u⁻¹ * (u * (u * x * u⁻¹)) := by rw [hxC]; group
          _ = u * x * u⁻¹ := by group
      have h2 : x = u * x * u⁻¹ := by rw [← h1]; group
      rw [h2]
      exact hx
  obtain ⟨Q', hQQ', hQ'Z, hQ'p, hQ'syl, hQ'u⟩ :=
    exists_invariant_sylow_ge hp hu hZodd hZu hQZ hQsyl.2.1 hQu
  obtain ⟨P₀, _hP₀syl, _hP₀u, hP₀conj⟩ :=
    Work.DoubleTransitivity.App1.app1_2 (X := Z) (t := u) (d := 2) Nat.prime_two hu
      (Nat.coprime_two_left.mpr hZodd) hZu hp
  obtain ⟨v, hv, hvconj⟩ := hP₀conj P ⟨hPZ, hPp, hsyl⟩ hPu
  obtain ⟨w, hw, hwconj⟩ := hP₀conj Q' ⟨hQ'Z, hQ'p, hQ'syl⟩ hQ'u
  have hvw : P₀ = Submission.Blueprint.conj v⁻¹ P := by
    rw [← hvconj, ← conj_mul, inv_mul_cancel, conj_one]
  have hconj : Q' = Submission.Blueprint.conj (w * v⁻¹) P := by
    rw [← hwconj, Work.ThreePoints.conj_mul, hvw]
  have hwC : w * v⁻¹ ∈ C := C.mul_mem hw.2 (C.inv_mem hv.2)
  have hconjC : Submission.Blueprint.conj (w * v⁻¹) C = C :=
    Work.ThreePoints.conj_eq_self_of_mem hwC
  have hcard : Nat.card ↥(Q' ⊓ C) = Nat.card ↥(P ⊓ C) := by
    conv_lhs => rw [hconj, ← hconjC, ← Work.ThreePoints.conj_inf]
    exact Subgroup.card_map_of_injective
      (f := (MulAut.conj (w * v⁻¹)).toMonoidHom) (MulAut.conj (w * v⁻¹)).injective
  have hle1 : Nat.card ↥(P ⊓ C) ≤ Nat.card ↥Q := card_le_card_of_le hCPQ
  have hle2 : Nat.card ↥Q ≤ Nat.card ↥(P ⊓ C) := by
    rw [← hcard]
    exact card_le_card_of_le (le_inf hQQ' (le_trans hQsyl.1 inf_le_right))
  exact (le_antisymm hle1 hle2).trans (card_of_isSylowSubgroupOf hQsyl)

/-- The `p`-adic valuation of `p ^ k`. -/
theorem factorization_pow_self {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ k).factorization p = k := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.Prime.factorization hp, Finsupp.single_eq_same, mul_one]

/-- For a `p`-subgroup `X` normalised by `t`, the orbit `t^X` has order
`p ^ (v_p |X| - v_p |C_X(t)|)`. -/
theorem card_conjOrbit_eq_pow_sub {p : ℕ} (hp : p.Prime) {X : Subgroup G} {t : G}
    (hXp : IsPGroup p X) (ht : t ∈ Subgroup.normalizer (X : Set G)) :
    (Work.DoubleTransitivity.conjOrbit X t).ncard =
      p ^ ((Nat.card ↥X).factorization p -
        (Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G))).factorization p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hXp
  obtain ⟨v, hv⟩ := IsPGroup.iff_card.mp hXp.to_inf_left
  have hmain : (Work.DoubleTransitivity.conjOrbit X t).ncard *
      Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) = Nat.card ↥X :=
    mul_ncard_conjOrbit_ncard_centralizer X t
  rw [hv, ha] at hmain
  have hfacX : (Nat.card ↥X).factorization p = a := by
    rw [ha]; exact factorization_pow_self hp a
  have hfacV : (Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G))).factorization p = v := by
    rw [hv]; exact factorization_pow_self hp v
  have hva : v ≤ a := by
    have hdvd : p ^ v ∣ p ^ a :=
      ⟨_, by rw [mul_comm]; exact hmain.symm⟩
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  have hk : (Work.DoubleTransitivity.conjOrbit X t).ncard = p ^ (a - v) := by
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos v) ?_
    rw [hmain, ← pow_add, Nat.sub_add_cancel hva]
  rw [hk, hfacX, hfacV]

/-- Appendix I (3)(d), `(iii) ⇒ (i)`: an invariant `p`-subgroup `P ≤ D = K ⊓ K^t` whose orbit
`|u^P|` has `p`-part at least that of `|Inv K|` gives a `p`-regular intersection for `D` relative
to `K`. -/
theorem isRegularIntersection_of_invariant {K : Subgroup G} (hK : IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) {t : G} (ht : orderOf t = 2) (htK : t ∉ K)
    (h : ∃ P : Subgroup G, P ≤ twoPoint K t ∧ IsPGroup p P ∧
      ∃ u ∈ Submission.Blueprint.involutions (K : Set G),
        u ∈ Subgroup.normalizer (P : Set G) ∧
        (Submission.Blueprint.involutions (K : Set G)).ncard.factorization p ≤
          (Work.DoubleTransitivity.conjOrbit P u).ncard.factorization p) :
    Work.DoubleTransitivity.IsRegularIntersection p (twoPoint K t) K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPD, hPp, u, hu, hPu, hle⟩ := h
  set D : Subgroup G := twoPoint K t with hD
  have hu2 : orderOf u = 2 := hu.2
  have huK : u ∈ K := hu.1
  have huu : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have huu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hDodd : Odd (Nat.card ↥D) := by
    have hne : Submission.Blueprint.conj (1 : G) K ≠ Submission.Blueprint.conj t K := by
      rw [conj_one]
      intro hc
      have htm : t ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hc.symm
      rw [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hK] at htm
      exact htK htm
    have h1 := card_inf_conj_odd hK (g := 1) (g' := t) hne
    simpa [hD, Submission.Blueprint.twoPoint, conj_one] using h1
  have hB : Work.DoubleTransitivity.IsBender K :=
    ((Work.DoubleTransitivity.isStronglyEmbedded_iff K).mp hK).2
  have hKne : K ≠ ⊤ := ((Work.DoubleTransitivity.isStronglyEmbedded_iff K).mp hK).1
  have huo : (Work.DoubleTransitivity.conjOrbit D u).ncard =
      (Submission.Blueprint.involutions (K : Set G)).ncard := by
    have h1 := (Work.DoubleTransitivity.Sec2.prop2 hB hKne ht htK).2.2 u hu
    simpa [hD, Submission.Blueprint.twoPoint] using h1
  -- `Z = D ⊓ D^u` is `u`-invariant of odd order
  set Z : Subgroup G := D ⊓ Submission.Blueprint.conj u D with hZ
  have hZu : u ∈ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Submission.Blueprint.conj u (D ⊓ Submission.Blueprint.conj u D) =
      D ⊓ Submission.Blueprint.conj u D
    rw [conj_inf, ← conj_mul, huu, conj_one, inf_comm]
  have hZodd : Odd (Nat.card ↥Z) := Odd.of_dvd (Subgroup.card_dvd_of_le inf_le_left) hDodd
  have hPZ : P ≤ Z := by
    refine le_inf hPD ?_
    intro x hx
    have h1 : u * x * u⁻¹ ∈ D := hPD ((Subgroup.mem_normalizer_iff.mp hPu x).mp hx)
    refine Work.ThreePoints.mem_conj_iff.mpr ?_
    rw [huu'] at h1 ⊢
    exact h1
  -- extension to a `u`-invariant `p`-Sylow of `Z`
  obtain ⟨Q, hPQ, hQZ, hQp, hQsyl, hQu⟩ :=
    exists_invariant_sylow_ge hp hu2 hZodd hZu hPZ hPp hPu
  have hQD : Q ≤ D := le_trans hQZ inf_le_left
  -- centralisers
  have hCZ : Z ⊓ Subgroup.centralizer ({u} : Set G) =
      D ⊓ Subgroup.centralizer ({u} : Set G) := by
    rw [hZ]
    ext x
    simp only [Subgroup.mem_inf, mem_conj_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨hxD, -⟩, hx⟩; exact ⟨hxD, hx⟩
    · rintro ⟨hxD, hx⟩
      refine ⟨⟨hxD, ?_⟩, hx⟩
      have h1 : u⁻¹ * x * u = x := by
        calc u⁻¹ * x * u = u⁻¹ * (x * u) := by group
          _ = u⁻¹ * (u * x) := by rw [hx]
          _ = x := by group
      rw [h1]
      exact hxD
  have hcent := card_centralizer_in_invariant_sylow hp hu2 hZodd hZu hQZ hQp hQu hQsyl
  rw [hCZ] at hcent
  -- order computations
  have hDne : Nat.card ↥D ≠ 0 := by
    haveI : Nonempty ↥D := ⟨⟨1, D.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hCne : Nat.card ↥(D ⊓ Subgroup.centralizer ({u} : Set G)) ≠ 0 := by
    haveI : Nonempty ↥(D ⊓ Subgroup.centralizer ({u} : Set G)) :=
      ⟨⟨1, ⟨D.one_mem, Subgroup.one_mem _⟩⟩⟩
    exact Nat.card_pos.ne'
  have hQne : Nat.card ↥Q ≠ 0 := by
    haveI : Nonempty ↥Q := ⟨⟨1, Q.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hCQne : Nat.card ↥(Q ⊓ Subgroup.centralizer ({u} : Set G)) ≠ 0 := by
    haveI : Nonempty ↥(Q ⊓ Subgroup.centralizer ({u} : Set G)) :=
      ⟨⟨1, ⟨Q.one_mem, Subgroup.one_mem _⟩⟩⟩
    exact Nat.card_pos.ne'
  have hUQne : (Work.DoubleTransitivity.conjOrbit Q u).ncard ≠ 0 := by
    have hne : (Work.DoubleTransitivity.conjOrbit Q u).Nonempty :=
      ⟨u, Work.DoubleTransitivity.t_mem_conjOrbit⟩
    exact ((Set.ncard_pos (s := Work.DoubleTransitivity.conjOrbit Q u)).mpr hne).ne'
  have hUDne : (Work.DoubleTransitivity.conjOrbit D u).ncard ≠ 0 := by
    have hne : (Work.DoubleTransitivity.conjOrbit D u).Nonempty :=
      ⟨u, Work.DoubleTransitivity.t_mem_conjOrbit⟩
    exact ((Set.ncard_pos (s := Work.DoubleTransitivity.conjOrbit D u)).mpr hne).ne'
  -- `|u^P| ≤ |u^Q|`, and both are powers of `p`
  have hcardPQ : (Work.DoubleTransitivity.conjOrbit P u).ncard ≤
      (Work.DoubleTransitivity.conjOrbit Q u).ncard :=
    Set.ncard_le_ncard (by rintro y ⟨x, hx, rfl⟩; exact ⟨x, hPQ hx, rfl⟩)
  have horb_le : (Work.DoubleTransitivity.conjOrbit P u).ncard.factorization p ≤
      (Work.DoubleTransitivity.conjOrbit Q u).ncard.factorization p := by
    obtain ⟨eP, heP⟩ : ∃ k, (Work.DoubleTransitivity.conjOrbit P u).ncard = p ^ k :=
      ⟨_, card_conjOrbit_eq_pow_sub hp hPp hPu⟩
    obtain ⟨eQ, heQ⟩ : ∃ k, (Work.DoubleTransitivity.conjOrbit Q u).ncard = p ^ k :=
      ⟨_, card_conjOrbit_eq_pow_sub hp hQp hQu⟩
    have h1 : (Work.DoubleTransitivity.conjOrbit P u).ncard =
        p ^ (Work.DoubleTransitivity.conjOrbit P u).ncard.factorization p := by
      rw [heP, factorization_pow_self hp]
    have h2 : (Work.DoubleTransitivity.conjOrbit Q u).ncard =
        p ^ (Work.DoubleTransitivity.conjOrbit Q u).ncard.factorization p := by
      rw [heQ, factorization_pow_self hp]
    rw [h1, h2] at hcardPQ
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcardPQ
  -- `(|Q|)_p = (|D|)_p`
  have hQeqD : (Nat.card ↥Q).factorization p = (Nat.card ↥D).factorization p := by
    have h3 : (Nat.card ↥(Q ⊓ Subgroup.centralizer ({u} : Set G))).factorization p =
        (Nat.card ↥(D ⊓ Subgroup.centralizer ({u} : Set G))).factorization p := by
      rw [hcent, factorization_pow_self hp]
    have hQf : (Nat.card ↥Q).factorization p =
        (Work.DoubleTransitivity.conjOrbit Q u).ncard.factorization p +
        (Nat.card ↥(Q ⊓ Subgroup.centralizer ({u} : Set G))).factorization p := by
      rw [← mul_ncard_conjOrbit_ncard_centralizer Q u, Nat.factorization_mul hUQne hCQne,
        Finsupp.add_apply]
    have hDf : (Nat.card ↥D).factorization p =
        (Work.DoubleTransitivity.conjOrbit D u).ncard.factorization p +
        (Nat.card ↥(D ⊓ Subgroup.centralizer ({u} : Set G))).factorization p := by
      rw [← mul_ncard_conjOrbit_ncard_centralizer D u, Nat.factorization_mul hUDne hCne,
        Finsupp.add_apply]
    have h4 : (Work.DoubleTransitivity.conjOrbit D u).ncard.factorization p ≤
        (Work.DoubleTransitivity.conjOrbit Q u).ncard.factorization p := by
      rw [huo]
      exact le_trans hle horb_le
    have h5 : (Nat.card ↥Q).factorization p ≤ (Nat.card ↥D).factorization p :=
      (Nat.factorization_le_iff_dvd hQne hDne).mpr (Subgroup.card_dvd_of_le hQD) p
    omega
  -- `Q` has the order of a `p`-Sylow of `D`
  have hQcard : Nat.card ↥Q = p ^ (Nat.card ↥D).factorization p := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
    have hk' : k = (Nat.card ↥D).factorization p := by
      have h := hQeqD
      rw [hk, factorization_pow_self hp] at h
      exact h
    rw [hk, hk']
  -- `Q` is a `p`-Sylow of `D`, and `u ∈ N(Q) ⊓ K` is an involution
  refine ⟨Q, ⟨hQD, hQp, ?_⟩, ?_⟩
  · intro hd
    have hindne : (Q.subgroupOf D).index ≠ 0 := fun hh => by
      have h1 := Subgroup.card_mul_index (Q.subgroupOf D)
      rw [hh, mul_zero] at h1
      exact hDne h1.symm
    have h1 : Nat.card ↥D = Nat.card ↥Q * (Q.subgroupOf D).index := by
      have h2 := Subgroup.card_mul_index (Q.subgroupOf D)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQD).toEquiv] at h2
      exact h2.symm
    have h2 : (Nat.card ↥D).factorization p = (Nat.card ↥Q).factorization p +
        (Q.subgroupOf D).index.factorization p := by
      rw [h1, Nat.factorization_mul hQne hindne, Finsupp.add_apply]
    have h3 : (Nat.card ↥Q).factorization p = (Nat.card ↥D).factorization p := by
      rw [hQcard, factorization_pow_self hp]
    have h4 : (Q.subgroupOf D).index.factorization p = 0 := by omega
    obtain ⟨m, hm⟩ := hd
    have hm0 : m ≠ 0 := fun h0 => hindne (by rw [hm, h0, mul_zero])
    rw [hm, Nat.factorization_mul ((Fact.out : p.Prime).pos.ne') hm0, Finsupp.add_apply,
      Nat.Prime.factorization (Fact.out : p.Prime), Finsupp.single_eq_same] at h4
    omega
  · have hm : u ∈ (Subgroup.normalizer (Q : Set G) ⊓ K : Subgroup G) := ⟨hQu, huK⟩
    refine even_iff_two_dvd.mpr ?_
    have hord : orderOf (⟨u, hm⟩ :
        ↥(Subgroup.normalizer (Q : Set G) ⊓ K : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hu2
    exact dvd_trans (by rw [hord]) (orderOf_dvd_natCard _)

theorem card_conjOrbit_sylow {p : ℕ} (hp : p.Prime) {t : G} (ht : orderOf t = 2)
    {D : Subgroup G} (hDodd : Odd (Nat.card ↥D))
    (htD : t ∈ Subgroup.normalizer (D : Set G))
    {P : Subgroup G} (hPD : P ≤ D) (hPp : IsPGroup p P)
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hsyl : ¬ p ∣ (P.subgroupOf D).index) :
    (Work.DoubleTransitivity.conjOrbit P t).ncard =
      p ^ (Work.DoubleTransitivity.conjOrbit D t).ncard.factorization p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥D).factorization p :=
    card_of_isSylowSubgroupOf ⟨hPD, hPp, hsyl⟩
  have hcent := card_centralizer_in_invariant_sylow hp ht hDodd htD hPD hPp htP hsyl
  have hPfac : (Nat.card ↥P).factorization p = (Nat.card ↥D).factorization p := by
    rw [hPcard]; exact factorization_pow_self hp _
  have hCfac : (Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set G))).factorization p =
      (Nat.card ↥(D ⊓ Subgroup.centralizer ({t} : Set G))).factorization p := by
    rw [hcent]; exact factorization_pow_self hp _
  have hDne : Nat.card ↥D ≠ 0 := by
    haveI : Nonempty ↥D := ⟨⟨1, D.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hCDne : Nat.card ↥(D ⊓ Subgroup.centralizer ({t} : Set G)) ≠ 0 := by
    haveI : Nonempty ↥(D ⊓ Subgroup.centralizer ({t} : Set G)) :=
      ⟨⟨1, ⟨D.one_mem, Subgroup.one_mem _⟩⟩⟩
    exact Nat.card_pos.ne'
  have hUDne : (Work.DoubleTransitivity.conjOrbit D t).ncard ≠ 0 := by
    have hne : (Work.DoubleTransitivity.conjOrbit D t).Nonempty :=
      ⟨t, Work.DoubleTransitivity.t_mem_conjOrbit⟩
    exact ((Set.ncard_pos (s := Work.DoubleTransitivity.conjOrbit D t)).mpr hne).ne'
  have hDfac : (Nat.card ↥D).factorization p =
      (Work.DoubleTransitivity.conjOrbit D t).ncard.factorization p +
      (Nat.card ↥(D ⊓ Subgroup.centralizer ({t} : Set G))).factorization p := by
    rw [← mul_ncard_conjOrbit_ncard_centralizer D t, Nat.factorization_mul hUDne hCDne,
      Finsupp.add_apply]
  rw [card_conjOrbit_eq_pow_sub hp hPp htP, hPfac, hCfac]
  congr 1
  omega

/-! ## Conjugation invariance of the number of fixed points -/

/-- The `MulAut`-smul on subgroups is conjugation. -/
theorem mulAut_conj_smul_eq_conj (g : G) (H : Subgroup G) :
    MulAut.conj g • H = Submission.Blueprint.conj g H := by
  rw [Subgroup.pointwise_smul_def]
  congr 1

/-- The number of fixed points of a subgroup is invariant under conjugation. -/
theorem ncard_fixedPts_smul {K : Subgroup G} (g : G) (Q : Subgroup G) :
    (fixedPts K (MulAut.conj g • Q)).ncard = (fixedPts K Q).ncard := by
  rw [mulAut_conj_smul_eq_conj, Work.ThreePoints.fixedPts_conj, Set.ncard_smul_set]

/-! ## Ch. I §4 Lemma 2, part 1

The workspace's `Work.DoubleTransitivity.Sec4.lemma2_part1` proves `Sec4Lemma2Part1 p H`, but its
module imports the present one (it uses the Appendix I / §4 Lemma 1 ingredients
`isRegularIntersection_of_invariant`, `card_conjOrbit_sylow` proved here).  Importing it would be a
cycle, so its proof is transcribed below in this module, with the same ingredients. -/

/-- A `p`-group with `p` odd has odd order. -/
theorem odd_card_of_isPGroup_of_odd_prime {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Q : Subgroup G} (hQp : IsPGroup p Q) : Odd (Nat.card ↥Q) := by
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
theorem card_conjOrbit_sylow_eq_pPart {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {p : ℕ} (hp : p.Prime) {t : G} (ht : orderOf t = 2)
    {ω₁ ω₂ : G ⧸ H} (hω₂₁ : ω₂ ≠ ω₁) (htω : t • ω₁ = ω₂) {Q₀ : Subgroup G}
    (hQ₀syl : Work.DoubleTransitivity.IsSylowSubgroupOf p Q₀
      (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂))
    (htQ₀ : Submission.Blueprint.conj t Q₀ = Q₀) :
    (Work.DoubleTransitivity.conjOrbit Q₀ t).ncard =
      p ^ ((Submission.Blueprint.involutions (H : Set G)).ncard.factorization p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup G := MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂ with hD
  have hKss : IsStronglyEmbedded (MulAction.stabilizer G ω₁) :=
    isStronglyEmbedded_stabilizer hH ω₁
  have hKB : Work.DoubleTransitivity.IsBender (MulAction.stabilizer G ω₁) :=
    (Work.DoubleTransitivity.isStronglyEmbedded_iff _).mp hKss |>.2
  have hKne : MulAction.stabilizer G ω₁ ≠ ⊤ :=
    ((Work.DoubleTransitivity.isStronglyEmbedded_iff _).mp hKss).1
  have htK : t ∉ MulAction.stabilizer G ω₁ := by
    intro hcon
    have h1 : t • ω₁ = ω₁ := MulAction.mem_stabilizer_iff.mp hcon
    exact hω₂₁ (h1.symm.trans htω).symm
  have htwo : Submission.Blueprint.twoPoint (MulAction.stabilizer G ω₁) t = D := by
    rw [Submission.Blueprint.twoPoint, hD,
      ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t ω₁, htω]
  have hDodd : Odd (Nat.card ↥D) := by
    rw [hD]
    exact odd_card_stabilizer_inf hH (fun h => hω₂₁ h.symm)
  have htD : t ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Submission.Blueprint.conj t
      (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂) = D
    have htω' : t • ω₂ = ω₁ := by
      have h1 : t • (t • ω₁) = t • ω₂ := by rw [htω]
      rw [← mul_smul, Work.DoubleTransitivity.App1.mul_self_eq_one_of_orderOf_eq_two ht,
        one_smul] at h1
      exact h1.symm
    rw [hD, Work.ThreePoints.conj_inf,
      ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t ω₁,
      ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t ω₂, htω, htω', inf_comm]
  have hDinv : (Work.DoubleTransitivity.conjOrbit D t).ncard =
      (Submission.Blueprint.involutions (H : Set G)).ncard := by
    have h1 : (Submission.Blueprint.invertedBy D t).ncard =
        (Submission.Blueprint.involutions (MulAction.stabilizer G ω₁ : Set G)).ncard := by
      have := (Work.DoubleTransitivity.Sec2.prop2 hKB hKne ht htK).2.1
      rwa [htwo] at this
    have h2 : (Submission.Blueprint.invertedBy D t).ncard =
        (Work.DoubleTransitivity.conjOrbit D t).ncard :=
      ncard_invertedBy_eq_ncard_conjOrbit ht hDodd htD
    have h3 : (Submission.Blueprint.involutions (MulAction.stabilizer G ω₁ : Set G)).ncard =
        (Submission.Blueprint.involutions (H : Set G)).ncard := by
      have h := ncard_involutions_stabilizer_eq (K := H) ω₁ (Work.DoubleTransitivity.pt H)
      rwa [Work.DoubleTransitivity.Sec4.stabilizer_pt_eq] at h
    rw [← h2, h1, h3]
  rw [card_conjOrbit_sylow hp ht hDodd htD hQ₀syl.1 hQ₀syl.2.1
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr htQ₀) hQ₀syl.2.2, hDinv]

/-- If `(D,K)` is a `p`-regular intersection with `D ≤ K`, then *every* `p`-Sylow of `D` has an
even-order normaliser in `K` (Ch. I §4 Lemma 1, (c) ⇒ (d), via Sylow conjugacy inside `D`). -/
theorem even_normalizer_of_isRegularIntersection_sylow {G : Type} [Group G] [Finite G]
    {D K : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hreg : Work.DoubleTransitivity.IsRegularIntersection p D K) (hDK : D ≤ K) {R : Subgroup G}
    (hRsyl : Work.DoubleTransitivity.IsSylowSubgroupOf p R D) :
    Even (Nat.card ↥(Subgroup.normalizer (R : Set G) ⊓ K)) := by
  obtain ⟨P, hPsyl, hPeven⟩ := hreg
  obtain ⟨d, hdD, hd⟩ := Work.ThreePoints.exists_conj_of_isSylowSubgroupOf hp
    hPsyl.1 hPsyl.2.1 hPsyl.2.2 hRsyl.1 hRsyl.2.1 hRsyl.2.2
  have hconjN : Submission.Blueprint.conj d (Subgroup.normalizer (P : Set G)) =
      Subgroup.normalizer (Submission.Blueprint.conj d P : Set G) := by
    have hmap := Subgroup.map_normalizer_eq_of_bijective (P : Subgroup G)
      (f := (MulAut.conj d).toMonoidHom) (MulAut.conj d).bijective
    rw [show Submission.Blueprint.conj d (Subgroup.normalizer (P : Set G)) =
          (Subgroup.normalizer (P : Set G)).map (MulAut.conj d).toMonoidHom from rfl, hmap]
  have hstep : Subgroup.normalizer (R : Set G) ⊓ K =
      Submission.Blueprint.conj d (Subgroup.normalizer (P : Set G) ⊓ K) := by
    rw [← hd, Work.ThreePoints.conj_inf, hconjN,
      Work.ThreePoints.conj_eq_self_of_mem (hDK hdD)]
  rw [hstep]
  have hcard : Nat.card ↥(Submission.Blueprint.conj d (Subgroup.normalizer (P : Set G) ⊓ K)) =
      Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ K) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj d).toMonoidHom) (MulAut.conj d).injective
  rw [hcard]
  exact hPeven

/-- **Peterfalvi I, Ch. I §4 Lemma 2, part 1** (pp. 155–156): if `Q` is maximal among the
`p`-subgroups of `G` with at least three fixed points of `Ω = G ⧸ H`, `Q` contains a `p`-Sylow of
a two-point stabiliser, and two distinct fixed points `ω₁, ω₂` of `Q` satisfy
`|N_G(Q) ⊓ Stab ω₁|` even, then `Q` **is** a `p`-Sylow of `Stab ω₁ ⊓ Stab ω₂`. -/
theorem sec4Lemma2Part1_gen {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Work.DoubleTransitivity.Sec4.Sec4Lemma2Part1 p H := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  intro Q hQmax hQinv ω₁' ω₂' hne hQω₁' hQω₂' hEven
  obtain ⟨ω₁, ω₂, hω₂₁, Q₀, hQ₀syl, hQ₀Q⟩ := hQinv
  obtain ⟨t, ht2, htQ₀, htω⟩ :=
    Work.ThreePoints.sec3_lemma1 hH hp (fun h => hω₂₁ h.symm) hQ₀syl
  obtain ⟨t', ht'2, ht'ω⟩ :=
    Work.ThreePoints.exists_involution_smul_eq_of_ne hH (fun h => hne h.symm)
  have ht'K : t' ∉ MulAction.stabilizer G ω₁' := by
    intro hcon
    have h1 : t' • ω₁' = ω₁' := MulAction.mem_stabilizer_iff.mp hcon
    exact hne (h1.symm.trans ht'ω).symm
  have hKss : IsStronglyEmbedded (MulAction.stabilizer G ω₁') :=
    isStronglyEmbedded_stabilizer hH ω₁'
  have hKB : Work.DoubleTransitivity.IsBender (MulAction.stabilizer G ω₁') :=
    (Work.DoubleTransitivity.isStronglyEmbedded_iff _).mp hKss |>.2
  have hKne : MulAction.stabilizer G ω₁' ≠ ⊤ :=
    ((Work.DoubleTransitivity.isStronglyEmbedded_iff _).mp hKss).1
  have hdtp : Submission.Blueprint.twoPoint (MulAction.stabilizer G ω₁') t' =
      MulAction.stabilizer G ω₁' ⊓ MulAction.stabilizer G ω₂' := by
    rw [Submission.Blueprint.twoPoint,
      ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t' ω₁', ht'ω]
  have hKcard : (Submission.Blueprint.involutions (MulAction.stabilizer G ω₁' : Set G)).ncard =
      (Submission.Blueprint.involutions (H : Set G)).ncard := by
    have h := ncard_involutions_stabilizer_eq (K := H) ω₁' (Work.DoubleTransitivity.pt H)
    rwa [Work.DoubleTransitivity.Sec4.stabilizer_pt_eq] at h
  have hkey : ∃ P : Subgroup G,
      P ≤ Submission.Blueprint.twoPoint (MulAction.stabilizer G ω₁') t' ∧ IsPGroup p P ∧
      ∃ u ∈ Submission.Blueprint.involutions (MulAction.stabilizer G ω₁' : Set G),
        u ∈ Subgroup.normalizer (P : Set G) ∧
        (Submission.Blueprint.involutions (MulAction.stabilizer G ω₁' : Set G)).ncard.factorization p
          ≤ (Work.DoubleTransitivity.conjOrbit P u).ncard.factorization p := by
    by_cases htK : t ∈ MulAction.stabilizer G ω₁'
    · refine ⟨Q₀, ?_, hQ₀syl.2.1, t, ⟨htK, ht2⟩,
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr htQ₀, ?_⟩
      · rw [hdtp]; exact le_trans hQ₀Q (le_inf hQω₁' hQω₂')
      · have hnum := card_conjOrbit_sylow_eq_pPart hH hp ht2 hω₂₁ htω hQ₀syl htQ₀
        have h1 : (Work.DoubleTransitivity.conjOrbit Q₀ t).ncard.factorization p =
            (Submission.Blueprint.involutions (H : Set G)).ncard.factorization p := by
          rw [hnum, factorization_pow_self hp]
        rw [hKcard, ← h1]
    · haveI : Fintype ↥(Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω₁') :=
        Fintype.ofFinite _
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G :=
        ↥(Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω₁')) 2
        (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hEven)
      have hu2 : orderOf ((u : G)) = 2 := (Subgroup.orderOf_coe u).trans hu
      have huN : (u : G) ∈ Subgroup.normalizer (Q : Set G) := u.2.1
      have huK : (u : G) ∈ MulAction.stabilizer G ω₁' := u.2.2
      refine ⟨Q, ?_, hQmax.1, u, ⟨huK, hu2⟩, huN, ?_⟩
      · rw [hdtp]; exact le_inf hQω₁' hQω₂'
      · have hnum := card_conjOrbit_sylow_eq_pPart hH hp ht2 hω₂₁ htω hQ₀syl htQ₀
        have hQ₀odd : Odd (Nat.card ↥Q₀) :=
          odd_card_of_isPGroup_of_odd_prime hp hp2 hQ₀syl.2.1
        have htQ₀' : t ∈ Subgroup.normalizer (Q₀ : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr htQ₀
        have h1 : (Submission.Blueprint.invertedBy Q₀ t).ncard =
            p ^ ((Submission.Blueprint.involutions (H : Set G)).ncard.factorization p) := by
          rw [ncard_invertedBy_eq_ncard_conjOrbit ht2 hQ₀odd htQ₀', hnum]
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
          rw [card_conjOrbit_eq_pow_sub hp hQmax.1 huN, factorization_pow_self hp]
        rw [h5] at h4
        have h6 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h4
        rw [hKcard]
        exact h6
  have hreg : Work.DoubleTransitivity.IsRegularIntersection p
      (MulAction.stabilizer G ω₁' ⊓ MulAction.stabilizer G ω₂')
      (MulAction.stabilizer G ω₁') := by
    have h := isRegularIntersection_of_invariant hKss hp ht'2 ht'K hkey
    rwa [hdtp] at h
  have hEvenAll : ∀ R : Subgroup G,
      Work.DoubleTransitivity.IsSylowSubgroupOf p R
        (MulAction.stabilizer G ω₁' ⊓ MulAction.stabilizer G ω₂') →
      Even (Nat.card ↥(Subgroup.normalizer (R : Set G) ⊓ MulAction.stabilizer G ω₁')) :=
    fun R hR => even_normalizer_of_isRegularIntersection_sylow hp hreg inf_le_left hR
  have hQD : Q ≤ MulAction.stabilizer G ω₁' ⊓ MulAction.stabilizer G ω₂' := le_inf hQω₁' hQω₂'
  obtain ⟨R', hQR', hR'syl⟩ := Work.DoubleTransitivity.Sec4.exists_isSylowSubgroupOf_le hQmax.1 hQD
  have hR'3 : 3 ≤ (fixedPts H R').ncard := by
    have h2 : 2 ≤ (fixedPts H R').ncard := by
      have hsub : ({ω₁', ω₂'} : Set (G ⧸ H)) ⊆ fixedPts H R' := by
        intro y hy
        rcases hy with rfl | rfl
        · exact Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mpr
            (le_trans hR'syl.1 inf_le_left)
        · exact Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mpr
            (le_trans hR'syl.1 inf_le_right)
      have hle := Set.ncard_le_ncard hsub
      rwa [Set.ncard_pair (fun h => hne h.symm)] at hle
    exact Work.DoubleTransitivity.Sec4.three_le_fixedPts_of_even_normalizer
      (((Work.DoubleTransitivity.isStronglyEmbedded_iff H).mp hH).2)
      (Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mpr
        (le_trans hR'syl.1 inf_le_left))
      (hEvenAll R' hR'syl) h2
  have hR'Q : R' ≤ Q := hQmax.2.2 R' hR'syl.2.1 hR'3 hQR'
  have hQeq : Q = R' := le_antisymm hQR' hR'Q
  rw [hQeq]
  exact hR'syl

/-- **Peterfalvi I Ch. I §4 Prop. 2** (p. 156), in the general form requested: `F` is a finite
group, `K ≤ F` a strongly embedded subgroup, `p ≠ 2` a prime, and `Q ≤ K` a `p`-subgroup which is
maximal among the `p`-subgroups of `K` with at least three fixed points of `Ω = F ⧸ K`.  Then
`|N_K(Q)|` is even.

Route to the proof (the source's, pp. 156–157, with the §4 `𝓡_p` analysis of the file
`REFS/peterfalvi_I_ch1_2.md`).  Write `𝓡_p ≠ ∅` for "there are distinct `H₀,H₀' ∈ Ω` and a
`p`-Sylow `Q₀` of `H₀ ⊓ H₀'` with `|N(Q₀) ⊓ H₀|` even" — a *`p`-regular intersection*,
`Work.DoubleTransitivity.IsRegularIntersection`.

* **Case 1, `𝓡_p = ∅`.**  Ch. I §4 Prop. 1 (a): `F` acts `2`-transitively on `Ω`; then App. II (6)
  (`Work.ThreePoints.app2_6_general`) makes `Q` maximal among the `p`-subgroups of `F` with `≥ 3`
  fixed points and makes `N_F(Q)` transitive on `Ω_Q`; Ch. I §3 Prop. 1 in transitivity form
  (`Work.ThreePoints.sec3_prop1_transitive`) then supplies a point stabiliser of `N_F(Q)` of even
  order, which transitivity transfers to `K`.  This is verbatim the proof of
  `Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup` with `h2tr` supplied instead of
  `ThmAProp`.
* **Case 2, `𝓡_p ≠ ∅`.**  Ch. I §4 Prop. 1 (b): a `p`-subgroup of `F` has exactly two fixed points
  **iff** `𝓡_p = ∅`; so in this case no `p`-subgroup has exactly two fixed points, and
  `Work.ThreePoints.even_card_normalizer_nofour_of_no_two_fixed` applies with
  `hNO2 := fun P hPp => ...`.

**WARNING on Case 2's hypothesis.**  The alternative hypothesis "there exists a `p`-subgroup with
`≥ 3` fixed points" is *not* enough to conclude "no `p`-subgroup has exactly two fixed points": in
`F = A₅ × C₃`, `K = A₄ × C₃` (strongly embedded), `p = 3`, the subgroup `1 × C₃` fixes all five
points of `Ω` while `⟨(123)⟩ × C₃` fixes exactly two of them.  (In that example `𝓡_p = ∅`, so Case
1 applies and `|N_K(1 × C₃)| = |K| = 36` is even, as the theorem asserts.)  What Case 2 needs is
exactly the source's `𝓡_p ≠ ∅`.

The pieces already proved in this file, which the completion should use:
* `isRegularIntersection_of_invariant` — Ch. I §4 Lemma 1, `(e) ⇒ (c)` (with the Appendix I
  ingredients `exists_invariant_sylow_ge`, `card_centralizer_in_invariant_sylow`);
* `card_conjOrbit_eq_pow_sub`, `card_conjOrbit_sylow` — the `p`-parts of the orbits `t^P` of a
  `p`-Sylow `P` (Appendix I (1)/(3)(b));
* `sec3_prop1_exists` — Ch. I §3 Prop. 1 in existence form;
* `ncard_fixedPts_smul`, `mulAut_conj_smul_eq_conj` — conjugation invariance of `|Ω_X|`;
* from sibling modules: `Work.ThreePoints.S4Prop2.ncard_involutions_conj` and
  `Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit`.

The missing steps are exactly Ch. I §4 Lemma 2 (both conclusions: `(H ⊓ H', H) ∈ 𝓡_p` and `P` is a
`p`-Sylow of `H ⊓ H'`) and Ch. I §4 Prop. 1 (a) and (b).  Case 2 additionally needs
`Sylow`-conjugacy bookkeeping to turn "some `p`-Sylow has `≥ 3` fixed points" into "every `p`-Sylow
does", which is where the source's "`Q = S`" step is used. -/
theorem even_card_normalizer_of_maximal_p_subgroup_gen {F : Type} [Group F] [Finite F]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) {K : Subgroup F}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F} (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) :
    Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  classical
  have h1 : Work.DoubleTransitivity.Sec4.Sec4Lemma2Part1 p K := sec4Lemma2Part1_gen hK hp hp2
  by_cases hRp : Work.DoubleTransitivity.Sec4.Rp p K
  · -- Case `𝓡_p ≠ ∅`: Ch. I §4 Prop. 1 (b) excludes `p`-subgroups with exactly two fixed points.
    have hno2 : ∀ T : Subgroup F, IsPGroup p T →
        (Submission.Blueprint.fixedPts K T).ncard ≠ 2 :=
      Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts hBrSz hK hp hp2 h1 hRp
    exact even_card_normalizer_nofour_of_no_two_fixed hK hp hp2 hQK hQp hQ3 hQmax hno2 hBrSz
  · -- Case `𝓡_p = ∅`: Ch. I §4 Prop. 1 (a) makes `F` `2`-transitive on `Ω = F ⧸ K`, App. II (6)
    -- makes `Q` maximal among the `p`-subgroups of `F` with three fixed points and `N_F(Q)`
    -- transitive on `Ω_Q`, and Ch. I §3 Prop. 1 finishes.
    haveI : Fintype (F ⧸ K) := Fintype.ofFinite _
    have h2tr : MulAction.IsMultiplyPretransitive F (F ⧸ K) 2 :=
      Work.DoubleTransitivity.Sec4.not_rp_twoTransitive hBrSz hK hp hp2 h1 hRp
    set M : Subgroup F := Subgroup.normalizer (Q : Set F) with hMdef
    have hstab : MulAction.stabilizer F (((1 : F)) : F ⧸ K) = K := by
      rw [Work.ThreePoints.stabilizer_mk K 1, conj_one]
    obtain ⟨hQmaxF, htransF⟩ :=
      Work.ThreePoints.app2_6_general (X := F) (E := F ⧸ K) (p := p) hp h2tr
        (P := Q) hQp (by rw [hstab]; exact hQK) hQ3
        (fun R hRg hRa hR3 hQR => by
          have hRK : R ≤ K := by rw [← hstab]; exact hRa
          rw [hQmax R hQR hRK hRg hR3])
    obtain ⟨ω, hω, heven⟩ := Work.ThreePoints.sec3_prop1_transitive hK hBrSz hp hp2 hQp hQ3
      (fun R hQR hRg hR3 => hQmaxF R hQR hRg hR3) htransF
    have hωK : (((1 : F)) : F ⧸ K) ∈ Submission.Blueprint.fixedPts K Q := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, hstab]
      exact hQK
    obtain ⟨n, hnM, hn⟩ := htransF (((1 : F)) : F ⧸ K) hωK ω hω
    -- all point stabilisers of `N_F(Q)` on `Ω_Q` have the same order
    have hcard_eq : Nat.card (MulAction.stabilizer F ω ⊓ M : Subgroup F) =
        Nat.card (MulAction.stabilizer F (((1 : F)) : F ⧸ K) ⊓ M : Subgroup F) := by
      have hMconj : conj n M = M := by
        have hstep : ∀ u ∈ M, conj u M ≤ M := by
          intro u hu m hm
          rw [Work.ThreePoints.mem_conj_iff] at hm
          have h := M.mul_mem (M.mul_mem hu hm) (M.inv_mem hu)
          rwa [show u * (u⁻¹ * m * u) * u⁻¹ = m from by group] at h
        refine le_antisymm (hstep n hnM) ?_
        calc M = conj n (conj n⁻¹ M) := by
              rw [← Work.ThreePoints.conj_mul, mul_inv_cancel, conj_one]
          _ ≤ conj n M := Subgroup.map_mono (hstep n⁻¹ (M.inv_mem hnM))
      have h1' : MulAction.stabilizer F ω =
          conj n (MulAction.stabilizer F (((1 : F)) : F ⧸ K)) := by
        rw [← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj n (((1 : F)) : F ⧸ K), hn]
      have key2 : MulAction.stabilizer F ω ⊓ M =
          conj n (MulAction.stabilizer F (((1 : F)) : F ⧸ K) ⊓ M) := by
        rw [Work.ThreePoints.conj_inf, ← h1', hMconj]
      rw [key2]
      exact Subgroup.card_map_of_injective (MulAut.conj n).injective
    have hevenK : Even (Nat.card (K ⊓ M : Subgroup F)) := by
      rw [← hstab, ← hcard_eq]
      exact heven
    rw [Work.ThreePoints.card_normalizer_subgroupOf_eq_card_inf hQK]
    exact hevenK

end Work.ThreePoints.S4Prop2
