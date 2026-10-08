import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Sec2.lemma1
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.DoubleTransitivity.Sec4.sec4_lemma2_part1
import Submission.Work.DoubleTransitivity.Sec4.lemma2_part1
import Submission.Work.DoubleTransitivity.Sec4.lemma2_propagation
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec7.Sec4Aux`

Peterfalvi I, Ch. I §4 Lemma 1 (its final "note") plus §4 Lemma 2, in the form needed by the
final assembly of Theorem A: if `P` is maximal among the `p`-subgroups of `G` with at least three
fixed points on `Ω = G ⧸ K` (`K` strongly embedded in `G`), contains a `p`-Sylow of a two-point
stabiliser and lies in `K`, then every involution of `K` has `|u^P| ≥ n_p` (`n = |Inv K|`), and
some involution of `K` normalises `P` without centralising it.

The inequality `|u^P| ≥ n_p` is the source's "`|K| = |u^P| = n_p`" (p.161), obtained here
through Appendix I (3)(b) (`Work.ThreePoints.S4Prop2.L2P1aux.card_conjOrbit_sylow`) and
Ch. I §2 Lemma 1 (`Work.DoubleTransitivity.Sec2.lemma1`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.DoubleTransitivity.Sec7

/-- **Peterfalvi I, Ch. I §4 Lemma 1 (note).**  For every involution `u` of `K`,
`|u^P| ≥ n_p` where `n = |Inv K|`. -/
theorem conjOrbit_ge {G : Type} [Group G] [Finite G]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {K : Subgroup G} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : Work.DoubleTransitivity.MaxFixesThree p K P) (hPK : P ≤ K)
    (hTP : Work.DoubleTransitivity.Sec4.TwoPointSylowData p K P)
    {u : G} (hu : u ∈ Submission.Blueprint.involutions (K : Set G)) :
    p ^ ((Submission.Blueprint.involutions (K : Set G)).ncard.factorization p) ≤
      (Work.DoubleTransitivity.conjOrbit P u).ncard := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Omega K) := Fintype.ofFinite _
  have hB : IsBender K := (isStronglyEmbedded_iff K).mp hK |>.2
  have hne : K ≠ ⊤ := ((isStronglyEmbedded_iff K).mp hK).1
  have hstab : MulAction.stabilizer G (pt K) = K :=
    Work.DoubleTransitivity.Sec4.stabilizer_pt_eq K
  obtain ⟨ω₂, hω₂, hne₂⟩ : ∃ ω₂ : Omega K, ω₂ ∈ fixedPts K P ∧ ω₂ ≠ pt K := by
    have h3 : 3 ≤ (fixedPts K P).ncard := hP.2.1
    have hgt : 1 < (fixedPts K P).ncard := by omega
    obtain ⟨ω, hω, hωne⟩ := Set.exists_ne_of_one_lt_ncard hgt (pt K)
    exact ⟨ω, hω, hωne⟩
  have hQω₁ : P ≤ MulAction.stabilizer G (pt K) := by rw [hstab]; exact hPK
  have hQω₂ : P ≤ MulAction.stabilizer G ω₂ :=
    Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mp hω₂
  have hL2 : Work.DoubleTransitivity.Sec4.Sec4Lemma2 p K :=
    Work.DoubleTransitivity.Sec4.sec4_lemma2_of_part1 hBrSz hK hp hp2
      (Work.DoubleTransitivity.Sec4.lemma2_part1 hBrSz hK hp hp2)
  obtain ⟨hPsyl, P'', hP''syl, hP''even⟩ :=
    hL2 P hP hTP (pt K) ω₂ hne₂ hQω₁ hQω₂
  rw [hstab] at hP''even
  set D : Subgroup G := MulAction.stabilizer G (pt K) ⊓ MulAction.stabilizer G ω₂ with hD
  -- the exchanging involution of `(pt K, ω₂)`
  obtain ⟨t, ht2, htP, htω⟩ :=
    Work.ThreePoints.sec3_lemma1 hK hp (Ne.symm hne₂) hPsyl
  have htK : t ∉ K := by
    intro hcon
    have h1 : t ∈ MulAction.stabilizer G (pt K) := by rw [hstab]; exact hcon
    have h2 : t • (pt K) = pt K := MulAction.mem_stabilizer_iff.mp h1
    exact hne₂ (h2.symm.trans htω).symm
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2] at h; simpa [pow_two] using h
  have htw₂ : t • ω₂ = pt K := by
    have h1 := congrArg (fun x => t • x) htω
    rw [← mul_smul, htt, one_smul] at h1
    exact h1.symm
  have hconjK : Submission.Blueprint.conj t K = MulAction.stabilizer G ω₂ :=
    (congrArg (fun X => X.map (MulAut.conj t).toMonoidHom) hstab).symm.trans
      ((Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t (pt K)).symm.trans
        (congrArg (MulAction.stabilizer G) htω))
  have hDeq : D = Submission.Blueprint.twoPoint K t := by
    have h1 : MulAction.stabilizer G (pt K) ⊓ MulAction.stabilizer G ω₂ =
        K ⊓ MulAction.stabilizer G ω₂ := by rw [hstab]
    have h2 : K ⊓ MulAction.stabilizer G ω₂ = K ⊓ Submission.Blueprint.conj t K := by
      rw [hconjK]
    rw [hD, h1, h2, Submission.Blueprint.twoPoint]
  have hDodd : Odd (Nat.card ↥D) := by
    rw [hDeq]
    exact Work.ThreePoints.IsStronglyEmbedded.odd_card_inf_conj hK htK
  have hmap1 : Submission.Blueprint.conj t (MulAction.stabilizer G (pt K)) =
      MulAction.stabilizer G ω₂ :=
    (congrArg (fun X => Submission.Blueprint.conj t X) hstab).trans hconjK
  have hmap2 : Submission.Blueprint.conj t (MulAction.stabilizer G ω₂) =
      MulAction.stabilizer G (pt K) :=
    (Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj t ω₂).symm.trans
      (congrArg (MulAction.stabilizer G) htw₂)
  have htD : t ∈ Subgroup.normalizer (D : Set G) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show Submission.Blueprint.conj t D = D
    rw [hD, Work.ThreePoints.conj_inf, hmap1, hmap2]
    exact inf_comm _ _
  have hDinv : (Submission.Blueprint.invertedBy D t).ncard =
      (Submission.Blueprint.involutions (K : Set G)).ncard := by
    rw [hDeq]
    exact (Sec2.prop2 hB hne ht2 htK).2.1
  have hDorb : (Work.DoubleTransitivity.conjOrbit D t).ncard =
      (Submission.Blueprint.involutions (K : Set G)).ncard := by
    rw [← Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit ht2 hDodd htD, hDinv]
  have hPD : P ≤ D := le_inf hQω₁ hQω₂
  have hPsylD : ¬ p ∣ (P.subgroupOf D).index := hPsyl.2.2
  have htP' : t ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr htP
  have hPodd : Odd (Nat.card ↥P) :=
    Work.DoubleTransitivity.Sec4.l2p1_odd_card_of_isPGroup_of_odd_prime hp hp2 hP.1
  have hconjOrbitP : (Work.DoubleTransitivity.conjOrbit P t).ncard =
      p ^ ((Submission.Blueprint.involutions (K : Set G)).ncard.factorization p) := by
    rw [Work.ThreePoints.S4Prop2.L2P1aux.card_conjOrbit_sylow hp ht2 hDodd htD
      hPD hP.1 htP' hPsylD, hDorb]
  have hinvP : (Submission.Blueprint.invertedBy P t).ncard =
      p ^ ((Submission.Blueprint.involutions (K : Set G)).ncard.factorization p) := by
    rw [Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit ht2 hPodd htP',
      hconjOrbitP]
  rw [← hinvP]
  exact Sec2.lemma1 hB hne hPK hPodd hu ht2 htK

/-- **Peterfalvi I, Ch. I §4 Lemma 1 (note)** in the quantitative form needed below: some
involution of `K` normalises `P` and has `|u^P| ≥ n_p`. -/
theorem exists_involution_normalizer_bound {G : Type} [Group G] [Finite G]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {K : Subgroup G} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ (Submission.Blueprint.involutions (K : Set G)).ncard)
    {P : Subgroup G} (hP : Work.DoubleTransitivity.MaxFixesThree p K P) (hPK : P ≤ K)
    (hTP : Work.DoubleTransitivity.Sec4.TwoPointSylowData p K P) :
    ∃ u : G, u ∈ Submission.Blueprint.involutions (K : Set G) ∧
      u ∈ Subgroup.normalizer (P : Set G) ∧
      p ^ ((Submission.Blueprint.involutions (K : Set G)).ncard.factorization p) ≤
        (Work.DoubleTransitivity.conjOrbit P u).ncard := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Omega K) := Fintype.ofFinite _
  have hstab : MulAction.stabilizer G (pt K) = K :=
    Work.DoubleTransitivity.Sec4.stabilizer_pt_eq K
  obtain ⟨ω₂, hω₂, hne₂⟩ : ∃ ω₂ : Omega K, ω₂ ∈ fixedPts K P ∧ ω₂ ≠ pt K := by
    have h3 : 3 ≤ (fixedPts K P).ncard := hP.2.1
    have hgt : 1 < (fixedPts K P).ncard := by omega
    obtain ⟨ω, hω, hωne⟩ := Set.exists_ne_of_one_lt_ncard hgt (pt K)
    exact ⟨ω, hω, hωne⟩
  have hQω₁ : P ≤ MulAction.stabilizer G (pt K) := by rw [hstab]; exact hPK
  have hQω₂ : P ≤ MulAction.stabilizer G ω₂ :=
    Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mp hω₂
  have hL2 : Work.DoubleTransitivity.Sec4.Sec4Lemma2 p K :=
    Work.DoubleTransitivity.Sec4.sec4_lemma2_of_part1 hBrSz hK hp hp2
      (Work.DoubleTransitivity.Sec4.lemma2_part1 hBrSz hK hp hp2)
  obtain ⟨hPsyl, P'', hP''syl, hP''even⟩ :=
    hL2 P hP hTP (pt K) ω₂ hne₂ hQω₁ hQω₂
  rw [hstab] at hP''even
  set D : Subgroup G := MulAction.stabilizer G (pt K) ⊓ MulAction.stabilizer G ω₂ with hD
  obtain ⟨d, hdD, hd⟩ := Work.ThreePoints.exists_conj_of_isSylowSubgroupOf hp
    hP''syl.1 hP''syl.2.1 hP''syl.2.2 hPsyl.1 hPsyl.2.1 hPsyl.2.2
  have hdK : d ∈ K := by rw [← hstab]; exact hdD.1
  have hEvenP : Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ K)) := by
    have hconjN : conj d (Subgroup.normalizer (P'' : Set G)) =
        Subgroup.normalizer (P : Set G) := by
      rw [← hd]
      exact Subgroup.map_normalizer_eq_of_bijective P''
        (f := (MulAut.conj d).toMonoidHom) (MulAut.conj d).bijective
    have hdK' : conj d K = K := by
      have h1 : d ∈ Subgroup.normalizer (K : Set G) := by
        rw [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hK]; exact hdK
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp h1
    have hstep : Subgroup.normalizer (P : Set G) ⊓ K =
        conj d (Subgroup.normalizer (P'' : Set G) ⊓ K) := by
      rw [Work.ThreePoints.conj_inf, hconjN, hdK']
    rw [hstep, Subgroup.card_map_of_injective (MulAut.conj d).injective]
    exact hP''even
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.normalizer (P : Set G) ⊓ K)) 2 (even_iff_two_dvd.mp hEvenP)
  have hu2 : orderOf ((u : G)) = 2 := (Subgroup.orderOf_coe u).trans hu
  have huN : (u : G) ∈ Subgroup.normalizer (P : Set G) := u.2.1
  have huK : (u : G) ∈ K := u.2.2
  exact ⟨u, ⟨huK, hu2⟩, huN, conjOrbit_ge hBrSz hK hp hp2 hP hPK hTP ⟨huK, hu2⟩⟩

/-- **Peterfalvi I, Ch. I §4 Lemma 1 (note) + §4 Lemma 2, final assembly.**  Some involution of
`K` normalises `P` without centralising it. -/
theorem exists_involution_normalizer_noncent {G : Type} [Group G] [Finite G]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {K : Subgroup G} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ (Submission.Blueprint.involutions (K : Set G)).ncard)
    {P : Subgroup G} (hP : Work.DoubleTransitivity.MaxFixesThree p K P) (hPK : P ≤ K)
    (hTP : Work.DoubleTransitivity.Sec4.TwoPointSylowData p K P) :
    ∃ u : G, u ∈ Submission.Blueprint.involutions (K : Set G) ∧
      u ∈ Subgroup.normalizer (P : Set G) ∧ ¬ ∀ x ∈ P, u * x * u⁻¹ = x := by
  classical
  have hB : IsBender K := (isStronglyEmbedded_iff K).mp hK |>.2
  obtain ⟨u, hu, huN, hbound⟩ :=
    exists_involution_normalizer_bound hBrSz hK hp hp2 hpdvd hP hPK hTP
  refine ⟨u, hu, huN, ?_⟩
  intro hcent
  have horb1 : (Work.DoubleTransitivity.conjOrbit P u).ncard = 1 := by
    rw [Set.ncard_eq_one]
    refine ⟨u, ?_⟩
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff]
      calc x⁻¹ * u * x = x⁻¹ * (u * x * u⁻¹) * u := by group
        _ = x⁻¹ * x * u := by rw [hcent x hx]
        _ = u := by group
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Work.DoubleTransitivity.t_mem_conjOrbit
  have hle1 : p ^ ((Submission.Blueprint.involutions (K : Set G)).ncard.factorization p) ≤ 1 :=
    hbound.trans (le_of_eq horb1)
  have hnne : (Submission.Blueprint.involutions (K : Set G)).ncard ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 hB.1
    have hv2 : orderOf ((v : ↥K) : G) = 2 := (Subgroup.orderOf_coe v).trans hv
    intro h0
    have hsub : ({((v : ↥K) : G)} : Set G) ⊆ Submission.Blueprint.involutions (K : Set G) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨v.2, hv2⟩
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_singleton] at this
    omega
  have hpos : 1 ≤ (Submission.Blueprint.involutions (K : Set G)).ncard.factorization p :=
    (hp.dvd_iff_one_le_factorization hnne).mp hpdvd
  have hgt1 : 1 < p ^ ((Submission.Blueprint.involutions (K : Set G)).ncard.factorization p) := by
    calc 1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ ((Submission.Blueprint.involutions (K : Set G)).ncard.factorization p) :=
          Nat.pow_le_pow_right hp.pos hpos
  omega

end Work.DoubleTransitivity.Sec7
