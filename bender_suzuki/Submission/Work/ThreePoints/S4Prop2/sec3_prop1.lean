import Mathlib
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.App2.fix_pair_of_not_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **Peterfalvi I Ch. I §3 Prop. 1** (p. 153): if `P` is maximal among the `p`-subgroups of a
finite group `G` with at least three fixed points of `Ω = G ⧸ H` (`H` strongly embedded), then
some point stabiliser `N_{Stab(ω)}(P) = N_G(P) ⊓ Stab(ω)` has even order, and `P` is contained in
that stabiliser. -/
theorem sec3_prop1 {G : Type} [Group G] [Finite G] (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : Work.DoubleTransitivity.MaxFixesThree p H P) :
    ∃ ω : Work.DoubleTransitivity.Omega H, P ≤ MulAction.stabilizer G ω ∧
      Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ MulAction.stabilizer G ω)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set M : Subgroup G := Subgroup.normalizer (P : Set G) with hMdef
  have hQp : IsPGroup p P := hP.1
  have hQ3 : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard := hP.2.1
  have hQmax : ∀ R : Subgroup G, P ≤ R → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts H R).ncard → R = P :=
    fun R hPR hRg hR3 => le_antisymm (hP.2.2 R hRg hR3 hPR) hPR
  have hQodd : Odd (Nat.card P) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    haveI : Fintype ↥P := Fintype.ofFinite ↥P
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥P) 2
      (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hev)
    obtain ⟨n, hn⟩ := hQp x
    have hxG : orderOf ((x : P) : G) = 2 := (Subgroup.orderOf_coe x).trans hx
    have h2dvd : 2 ∣ p ^ n := by
      rw [← hxG]
      exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg (fun y : P => (y : G)) hn)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  by_cases hA4 : Submission.Blueprint.HasFourGroup M
  · -- Case A: `N_G(P)` has `2`-rank `≥ 2`
    obtain ⟨t, ht2⟩ : ∃ t : M, orderOf t = 2 := by
      obtain ⟨t, -, ht2, -, -, -⟩ := hA4
      exact ⟨t, ht2⟩
    have htG : orderOf ((t : G)) = 2 := (Subgroup.orderOf_coe t).trans ht2
    obtain ⟨ω, hωfix, -⟩ := existsUnique_fixedPts_of_orderOf_eq_two hH htG
    have hle : P ≤ MulAction.stabilizer G ω :=
      le_stabilizer_of_involution_mem_normalizer hH hQodd hA4 ⟨t.2, htG⟩ hωfix
    refine ⟨ω, mem_fixedPts_iff_le_stabilizer.mpr hle, ?_⟩
    have hmem : (t : G) ∈ (M ⊓ MulAction.stabilizer G ω : Subgroup G) :=
      ⟨t.2, MulAction.mem_stabilizer_iff.mpr hωfix⟩
    refine even_iff_two_dvd.mpr ?_
    have hord : orderOf (⟨(t : G), hmem⟩ :
        ↥(M ⊓ MulAction.stabilizer G ω : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact htG
    have h2dvd : 2 ∣ orderOf (⟨(t : G), hmem⟩ :
        ↥(M ⊓ MulAction.stabilizer G ω : Subgroup G)) := by
      rw [hord]
    exact dvd_trans h2dvd (orderOf_dvd_natCard
      (⟨(t : G), hmem⟩ : ↥(M ⊓ MulAction.stabilizer G ω : Subgroup G)))
  · -- Case B: `N_G(P)` has `2`-rank `1`
    have hB : ¬ Submission.Blueprint.HasFourGroup M := hA4
    have hne : (Submission.Blueprint.fixedPts H P).Nonempty := by
      rw [← Set.ncard_pos]; omega
    by_cases hex : ∃ ω ∈ Submission.Blueprint.fixedPts H P,
        3 ≤ (MulAction.orbit M ω).ncard
    · -- Case 2: an `M`-orbit of size `≥ 3`
      obtain ⟨ω₀, hω₀, hω₀orb⟩ := hex
      obtain ⟨ω₁, hω₁, hω₁ne⟩ :=
        Set.exists_ne_of_one_lt_ncard (s := MulAction.orbit M ω₀) (by omega) ω₀
      have h2s : 2 ≤ ((MulAction.orbit M ω₀) \ {ω₀}).ncard := by
        have h1 := Set.ncard_sdiff_singleton_add_one (MulAction.mem_orbit_self (M := ↥M) ω₀)
        omega
      obtain ⟨ω₂, hω₂, hω₂ne⟩ := Set.exists_ne_of_one_lt_ncard (s := (MulAction.orbit M ω₀) \ {ω₀})
        (by omega) ω₁
      have hω₂mem : ω₂ ∈ MulAction.orbit M ω₀ := hω₂.1
      have hω₂ne₀ : ω₂ ≠ ω₀ := hω₂.2
      obtain ⟨x₁, hx₁⟩ := MulAction.mem_orbit_iff.mp hω₁
      obtain ⟨x₂, hx₂⟩ := MulAction.mem_orbit_iff.mp hω₂mem
      have horb₁ : ∃ x : G, x ∈ Subgroup.normalizer (P : Set G) ∧ x • ω₀ = ω₁ :=
        ⟨(x₁ : G), x₁.2, hx₁⟩
      have horb₂ : ∃ x : G, x ∈ Subgroup.normalizer (P : Set G) ∧ x • ω₀ = ω₂ :=
        ⟨(x₂ : G), x₂.2, hx₂⟩
      have hfix₁ : ω₁ ∈ Submission.Blueprint.fixedPts H P := by
        rw [← horb₁.choose_spec.2]
        exact Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer
          horb₁.choose_spec.1 hω₀
      have hfix₂ : ω₂ ∈ Submission.Blueprint.fixedPts H P := by
        rw [← horb₂.choose_spec.2]
        exact Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer
          horb₂.choose_spec.1 hω₀
      obtain ⟨t₁, ht₁M, ht₁2, ht₁⟩ := sec3_lemma3 hH hp hQp hQmax hω₀ hfix₁ hω₁ne.symm horb₁
      obtain ⟨t₂, ht₂M, ht₂2, ht₂⟩ := sec3_lemma3 hH hp hQp hQmax hω₀ hfix₂ hω₂ne₀.symm horb₂
      have hprodM : t₁ * t₂ ∈ Subgroup.normalizer (P : Set G) := M.mul_mem ht₁M ht₂M
      have hω' : (t₁ * t₂) • ω₀ ∈ Submission.Blueprint.fixedPts H P :=
        Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hprodM hω₀
      have ht₁sq : t₁ * t₁ = 1 := mul_self_eq_one_of_orderOf_eq_two ht₁2
      have ht₂sq : t₂ * t₂ = 1 := mul_self_eq_one_of_orderOf_eq_two ht₂2
      have hne' : ω₀ ≠ (t₁ * t₂) • ω₀ := by
        intro hcon
        have h1 : t₁ • ((t₁ * t₂) • ω₀) = ω₂ := by
          rw [mul_smul, ← mul_smul, ht₁sq, one_smul, ht₂]
        have h2 : t₁ • ω₀ = t₁ • ((t₁ * t₂) • ω₀) := congrArg (fun y => t₁ • y) hcon
        exact hω₂ne (ht₁.symm.trans (h2.trans h1)).symm
      obtain ⟨t, htM, ht2, ht⟩ := sec3_lemma3 hH hp hQp hQmax hω₀ hω'
        hne' ⟨t₁ * t₂, hprodM, rfl⟩
      have hxmem : t₂ * t₁ * t ∈ M := M.mul_mem (M.mul_mem ht₂M ht₁M) htM
      have htsq : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht2
      have hxfix : (t₂ * t₁ * t) • ω₀ = ω₀ := by
        rw [mul_smul, mul_smul, ht, mul_smul]
        have h1 : t₁ • (t₁ • (t₂ • ω₀)) = t₂ • ω₀ := by
          rw [← mul_smul, ht₁sq, one_smul]
        rw [h1, ← mul_smul, ht₂sq, one_smul]
      refine ⟨ω₀, hω₀, ?_⟩
      refine even_iff_two_dvd.mpr ?_
      have hmem : (t₂ * t₁ * t) ∈ (M ⊓ MulAction.stabilizer G ω₀ : Subgroup G) :=
        ⟨hxmem, MulAction.mem_stabilizer_iff.mpr hxfix⟩
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
          ↥(M ⊓ MulAction.stabilizer G ω₀ : Subgroup G)) = orderOf (t₂ * t₁ * t) :=
        Subgroup.orderOf_mk _ _
      rw [← hord]
      exact orderOf_dvd_natCard _
    · -- Case 1: every `M`-orbit on `Ω_P` has size `≤ 2`; derive a contradiction
      exfalso
      obtain ⟨ω₁, hω₁⟩ := hne
      have hcompl : ∃ ω₂ ∈ Submission.Blueprint.fixedPts H P, ω₂ ∉ MulAction.orbit M ω₁ := by
        by_contra hc
        push Not at hc
        have hle : (Submission.Blueprint.fixedPts H P).ncard ≤ (MulAction.orbit M ω₁).ncard :=
          Set.ncard_le_ncard hc (Set.toFinite _)
        have h2 : (MulAction.orbit M ω₁).ncard ≤ 2 := by
          by_contra hcon
          exact hex ⟨ω₁, hω₁, by omega⟩
        omega
      obtain ⟨ω₂, hω₂, hω₂not⟩ := hcompl
      have hω₂ne : ω₂ ≠ ω₁ := fun h => hω₂not (by rw [h]; exact MulAction.mem_orbit_self (M := ↥M) ω₁)
      -- `P` is not a `p`-Sylow of the two-point stabiliser
      have hnotsyl : ¬ Work.DoubleTransitivity.IsSylowSubgroupOf p P
          (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂) := by
        intro hsy
        obtain ⟨u, -, huP, huω⟩ := sec3_lemma1 hH hp hω₂ne.symm hsy
        have huM : u ∈ M := Subgroup.mem_normalizer_iff_map_conj_eq.mpr huP
        exact hω₂not (MulAction.mem_orbit_iff.mpr ⟨⟨u, huM⟩, huω⟩)
      -- the `p`-subgroup `R ≤ M ⊓ Stab(ω₁)` with fixed point set exactly `{ω₁, ω₂}`
      obtain ⟨R, hRg, hPR, hRN, hRfix⟩ :=
        Work.DoubleTransitivity.App2.fix_pair_of_not_sylow (X := G) (E := G ⧸ H) (p := p)
          hQp hω₁ hω₂ hω₂ne hnotsyl
          (fun Q hQg _ hQ3 hPQ => le_of_eq (hQmax Q hPQ hQg hQ3))
      have hRM : R ≤ M := le_trans hRN inf_le_left
      -- a third fixed point of `P`, moved by `R`
      have hexists3 : ∃ ω₃ ∈ Submission.Blueprint.fixedPts H P,
          ω₃ ∉ ({ω₁, ω₂} : Set (G ⧸ H)) := by
        by_contra hc
        push Not at hc
        have hle : (Submission.Blueprint.fixedPts H P).ncard ≤ ({ω₁, ω₂} : Set (G ⧸ H)).ncard :=
          Set.ncard_le_ncard hc (Set.toFinite _)
        rw [Set.ncard_pair hω₂ne.symm] at hle
        omega
      obtain ⟨ω₃, hω₃, hω₃not⟩ := hexists3
      have hω₃notR : ω₃ ∉ Submission.Blueprint.fixedPts H R := by
        rw [show Submission.Blueprint.fixedPts H R = ({ω₁, ω₂} : Set (G ⧸ H)) from hRfix]
        exact hω₃not
      have hmoves : ∃ r ∈ R, r • ω₃ ≠ ω₃ := by
        by_contra hc
        push Not at hc
        exact hω₃notR (Work.ThreePoints.mem_fixedPts.mpr (fun r hr => hc r hr))
      obtain ⟨r, hrR, hrω⟩ := hmoves
      -- the `M`-orbit of `ω₃` has size `≤ 2`; the `R`-orbit is contained in it and has size `2`
      have hMorb : (MulAction.orbit M ω₃).ncard ≤ 2 := by
        by_contra hcon
        exact hex ⟨ω₃, hω₃, by omega⟩
      have hsub : MulAction.orbit R ω₃ ⊆ MulAction.orbit M ω₃ := by
        intro y hy
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
        exact MulAction.mem_orbit_iff.mpr ⟨⟨g, hRM g.2⟩, hg⟩
      have hleR : (MulAction.orbit R ω₃).ncard ≤ 2 :=
        le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hMorb
      have hgeR : 2 ≤ (MulAction.orbit R ω₃).ncard := by
        have hmem : r • ω₃ ∈ MulAction.orbit R ω₃ :=
          MulAction.mem_orbit_iff.mpr ⟨⟨r, hrR⟩, rfl⟩
        have h1 : 1 < (MulAction.orbit R ω₃).ncard :=
          (Set.one_lt_ncard (Set.toFinite _)).mpr
            ⟨ω₃, MulAction.mem_orbit_self (M := ↥R) ω₃, r • ω₃, hmem, hrω.symm⟩
        omega
      have horb2 : (MulAction.orbit R ω₃).ncard = 2 := le_antisymm hleR hgeR
      -- but `2 ∣ |orbit| ∣ |R|` while `|R|` is odd
      have hdvd : (MulAction.orbit R ω₃).ncard ∣ Nat.card R := by
        refine ⟨Nat.card ↥(MulAction.stabilizer R ω₃), ?_⟩
        rw [mul_comm, ← MulAction.index_stabilizer, Subgroup.card_mul_index]
      have h2R : 2 ∣ Nat.card R := by
        rw [horb2] at hdvd; exact hdvd
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := ↥R)).mp hRg
      rw [hk] at h2R
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2R)).symm

end Work.ThreePoints
