import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.DoubleTransitivity.App2.fix_pair_of_not_sylow
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec3.prop1` — Peterfalvi I, Ch. I §3 Proposition 1 (p. 153)

Let `H` be a strongly embedded subgroup of the finite group `G` (so `Ω = G ⧸ H` is the class of
conjugates of `H`, with `G` acting on the left), `p` an odd prime, and `P` a `p`-subgroup of `G`
which is *maximal* among the `p`-subgroups of `G` having at least three fixed points of `Ω`
(`Work.DoubleTransitivity.MaxFixesThree p H P`).  Then some fixed point `ω` of `P` has
`|N_G(P) ⊓ Stab_G(ω)| = |N_{Stab(ω)}(P)|` even, i.e. some point stabiliser `H' ⊇ P` contains an
involution normalising `P`.

This is `REFS/peterfalvi_I_ch1_2.md`, §3 Prop. 1.  The proof is the source's `N_G(P)`-orbit
analysis of `Ω_P = fixedPts H P`, with `M = N_G(P)`:

* **Case A: `HasFourGroup M`.**  Ch. I §3 Lemma 2
  (`Work.ThreePoints.le_stabilizer_of_involution_mem_normalizer`): `P` has odd order, so the
  unique fixed point `ω` of any involution `t ∈ M` satisfies `P ≤ Stab_G(ω)`; that involution
  then lies in `M ⊓ Stab_G(ω)`, giving even order.
* **Case B: `¬ HasFourGroup M`.**  `M/O(M)` has at most one involution, so the product of any two
  involutions of `M` lies in `O(M)` (`Work.ThreePoints.involution_mul_involution_mem_oddCore`,
  the Brauer–Suzuki consequence), whence the product of *three* involutions has even order.
  * If some `M`-orbit on `Ω_P` has `≥ 3` points, pick `ω₀` with `ω₁ = m₁ • ω₀`, `ω₂ = m₂ • ω₀`
    distinct from `ω₀` and each other.  Ch. I §3 Lemma 3 (`Work.ThreePoints.sec3_lemma3`) replaces
    `m₁`, `m₂` by involutions `t₁, t₂ ∈ M`, and likewise once more for the point `(t₁t₂) • ω₀`;
    then `t₂t₁t ∈ M ⊓ Stab_G(ω₀)` has even order.
  * Otherwise every `M`-orbit on `Ω_P` has at most two points, and the source's Case 1 derives a
    contradiction: two fixed points `ω₁, ω₂` in different `M`-orbits force `P` to be a `p`-Sylow
    of `Stab(ω₁) ⊓ Stab(ω₂)` (otherwise `Work.DoubleTransitivity.App2.fix_pair_of_not_sylow`
    produces a `p`-subgroup `R ⊇ P` with fixed point set exactly `{ω₁, ω₂}`; Lemma 1
    (`Work.ThreePoints.sec3_lemma1`) then yields an involution of `M` exchanging `ω₁` and `ω₂`,
    and `R` moves a third point `ω₃ ∈ Ω_P` so that the `R`-orbit of `ω₃` has `2` points — but
    `2 ∣ |R| ∣ p^k` with `p ≠ 2`).

The statement is also available verbatim, in the parallel `ThreePoints` development (see
`Work.DoubleTransitivity.STATUS.md` §2, "do not rebuild"), as
`Work.ThreePoints.sec3_prop1` (`Submission/Work/ThreePoints/S4Prop2/sec3_prop1.lean`); the proof
below is written out here so that this module is self-contained with respect to that statement.
-/

set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.DoubleTransitivity.Sec3

theorem prop1 {G : Type} [Group G] [Finite G] (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : Work.DoubleTransitivity.MaxFixesThree p H P) :
    ∃ ω : Work.DoubleTransitivity.Omega H, P ≤ MulAction.stabilizer G ω ∧
      Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ MulAction.stabilizer G ω)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨hPp, hP3, hPmaxw⟩ := hP
  have hP3' : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard := hP3
  have hPmax : ∀ R : Subgroup G, P ≤ R → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts H R).ncard → R = P :=
    fun R hPR hRg hR3 => le_antisymm (hPmaxw R hRg hR3 hPR) hPR
  -- `P` is a `p`-subgroup of odd order (`p ≠ 2` is a prime)
  have hPodd : Odd (Nat.card P) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    haveI : Fintype ↥P := Fintype.ofFinite ↥P
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥P) 2
      (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hev)
    obtain ⟨n, hn⟩ := hPp x
    have hxG : orderOf ((x : P) : G) = 2 := (Subgroup.orderOf_coe x).trans hx
    have h2dvd : 2 ∣ p ^ n := by
      rw [← hxG]
      exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg (fun y : P => (y : G)) hn)
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  set M : Subgroup G := Subgroup.normalizer (P : Set G) with hMdef
  by_cases hA4 : HasFourGroup M
  · -- ## Case A: `N_G(P)` has 2-rank `≥ 2`  (Ch. I §3 Lemma 2)
    obtain ⟨a, ha⟩ : ∃ a : M, orderOf a = 2 := by
      obtain ⟨a, -, ha, -⟩ := hA4
      exact ⟨a, ha⟩
    have haG : orderOf ((a : G)) = 2 := (Subgroup.orderOf_coe a).trans ha
    obtain ⟨ω, hωfix, -⟩ := Work.ThreePoints.existsUnique_fixedPts_of_orderOf_eq_two hH haG
    have hle : P ≤ MulAction.stabilizer G ω :=
      Work.ThreePoints.le_stabilizer_of_involution_mem_normalizer hH hPodd hA4 ⟨a.2, haG⟩ hωfix
    refine ⟨ω, hle, ?_⟩
    have hmem : (a : G) ∈ (M ⊓ MulAction.stabilizer G ω : Subgroup G) :=
      ⟨a.2, MulAction.mem_stabilizer_iff.mpr hωfix⟩
    have hord : orderOf (⟨(a : G), hmem⟩ :
        ↥(M ⊓ MulAction.stabilizer G ω : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact haG
    exact even_iff_two_dvd.mpr (dvd_trans ⟨1, hord⟩ (orderOf_dvd_natCard _))
  · -- ## Case B: `N_G(P)` has 2-rank `1`
    have hB : ¬ HasFourGroup M := hA4
    have hne : (Submission.Blueprint.fixedPts H P).Nonempty := by
      rw [← Set.ncard_pos]; omega
    by_cases hex : ∃ ω ∈ Submission.Blueprint.fixedPts H P, 3 ≤ (MulAction.orbit M ω).ncard
    · -- ## Case 2: some `M`-orbit on `Ω_P` has at least three points
      obtain ⟨ω₀, hω₀, hω₀orb⟩ := hex
      obtain ⟨ω₁, hω₁, hω₁ne⟩ :=
        Set.exists_ne_of_one_lt_ncard (s := MulAction.orbit M ω₀) (by omega) ω₀
      have h2s : 2 ≤ ((MulAction.orbit M ω₀) \ {ω₀}).ncard := by
        have h1 := Set.ncard_sdiff_singleton_add_one (MulAction.mem_orbit_self (M := ↥M) ω₀)
        omega
      obtain ⟨ω₂, hω₂, hω₂ne⟩ :=
        Set.exists_ne_of_one_lt_ncard (s := (MulAction.orbit M ω₀) \ {ω₀}) (by omega) ω₁
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
      -- Ch. I §3 Lemma 3: involutions of `M` realising the two orbit steps
      obtain ⟨t₁, ht₁M, ht₁2, ht₁⟩ :=
        Work.ThreePoints.sec3_lemma3 hH hp hPp hPmax hω₀ hfix₁ hω₁ne.symm horb₁
      obtain ⟨t₂, ht₂M, ht₂2, ht₂⟩ :=
        Work.ThreePoints.sec3_lemma3 hH hp hPp hPmax hω₀ hfix₂ hω₂ne₀.symm horb₂
      have ht₁sq : t₁ * t₁ = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two ht₁2
      have ht₂sq : t₂ * t₂ = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two ht₂2
      have hprodM : t₁ * t₂ ∈ Subgroup.normalizer (P : Set G) :=
        (Subgroup.normalizer (P : Set G)).mul_mem ht₁M ht₂M
      have hω' : (t₁ * t₂) • ω₀ ∈ Submission.Blueprint.fixedPts H P :=
        Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hprodM hω₀
      have hne' : ω₀ ≠ (t₁ * t₂) • ω₀ := by
        intro hcon
        have h1 : t₁ • ((t₁ * t₂) • ω₀) = ω₂ := by
          rw [mul_smul, ← mul_smul, ht₁sq, one_smul, ht₂]
        have h2 : t₁ • ω₀ = t₁ • ((t₁ * t₂) • ω₀) := congrArg (fun y => t₁ • y) hcon
        exact hω₂ne (ht₁.symm.trans (h2.trans h1)).symm
      obtain ⟨t, htM, ht2, ht⟩ :=
        Work.ThreePoints.sec3_lemma3 hH hp hPp hPmax hω₀ hω' hne' ⟨t₁ * t₂, hprodM, rfl⟩
      have htsq : t * t = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two ht2
      have hxmem : t₂ * t₁ * t ∈ M := M.mul_mem (M.mul_mem ht₂M ht₁M) htM
      have hxfix : (t₂ * t₁ * t) • ω₀ = ω₀ := by
        rw [mul_smul, mul_smul, ht, mul_smul]
        have h1 : t₁ • (t₁ • (t₂ • ω₀)) = t₂ • ω₀ := by
          rw [← mul_smul, ht₁sq, one_smul]
        rw [h1, ← mul_smul, ht₂sq, one_smul]
      refine ⟨ω₀, (Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω₀), ?_⟩
      refine even_iff_two_dvd.mpr ?_
      have hmem : (t₂ * t₁ * t) ∈ (M ⊓ MulAction.stabilizer G ω₀ : Subgroup G) :=
        ⟨hxmem, MulAction.mem_stabilizer_iff.mpr hxfix⟩
      -- the three involutions `t₂', t₁', t'` of `M`
      set t₁' : M := ⟨t₁, ht₁M⟩ with ht₁'def
      set t₂' : M := ⟨t₂, ht₂M⟩ with ht₂'def
      set t' : M := ⟨t, htM⟩ with ht'def
      have ht₁2' : orderOf t₁' = 2 := by rw [← Subgroup.orderOf_coe t₁']; exact ht₁2
      have ht₂2' : orderOf t₂' = 2 := by rw [← Subgroup.orderOf_coe t₂']; exact ht₂2
      have ht2' : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe t']; exact ht2
      have htsq' : t' * t' = 1 := Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two ht2'
      have hO : (Submission.Blueprint.oddCore M).Normal := Work.BrauerSuzuki.oddCore_normal M
      -- Brauer–Suzuki consequence: `t₂ t₁ ∈ O(M)`, `t ∉ O(M)`
      have hprodO : t₂' * t₁' ∈ Submission.Blueprint.oddCore M :=
        Work.ThreePoints.involution_mul_involution_mem_oddCore hBrSz hB ht₂2' ht₁2'
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
      -- hence `t₂ t₁ t` has even order
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
    · -- ## Case 1: every `M`-orbit on `Ω_P` has at most two points — contradiction
      exfalso
      obtain ⟨ω₁, hω₁⟩ := hne
      have hcompl : ∃ ω₂ ∈ Submission.Blueprint.fixedPts H P,
          ω₂ ∉ MulAction.orbit M ω₁ := by
        by_contra hc
        push_neg at hc
        have hle : (Submission.Blueprint.fixedPts H P).ncard ≤
            (MulAction.orbit M ω₁).ncard :=
          Set.ncard_le_ncard hc (Set.toFinite _)
        have h2 : (MulAction.orbit M ω₁).ncard ≤ 2 := by
          by_contra hcon
          exact hex ⟨ω₁, hω₁, by omega⟩
        omega
      obtain ⟨ω₂, hω₂, hω₂not⟩ := hcompl
      have hω₂ne : ω₂ ≠ ω₁ :=
        fun h => hω₂not (by rw [h]; exact MulAction.mem_orbit_self (M := ↥M) ω₁)
      -- `P` is not a `p`-Sylow of the two-point stabiliser (Ch. I §3 Lemma 1)
      have hnotsyl : ¬ Work.DoubleTransitivity.IsSylowSubgroupOf p P
          (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂) := by
        intro hsy
        obtain ⟨u, -, huP, huω⟩ := Work.ThreePoints.sec3_lemma1 hH hp hω₂ne.symm hsy
        have huM : u ∈ M := Subgroup.mem_normalizer_iff_map_conj_eq.mpr huP
        exact hω₂not (MulAction.mem_orbit_iff.mpr ⟨⟨u, huM⟩, huω⟩)
      -- a `p`-subgroup `R ⊇ P` normalised by `P`-conjugation inside `M`, with `Ω_R = {ω₁, ω₂}`
      obtain ⟨R, hRg, hPR, hRN, hRfix⟩ :=
        Work.DoubleTransitivity.App2.fix_pair_of_not_sylow (X := G) (E := G ⧸ H) (p := p)
          hPp hω₁ hω₂ hω₂ne hnotsyl
          (fun Q hQg _ hQ3 hPQ => hPmaxw Q hQg hQ3 hPQ)
      have hRM : R ≤ M := le_trans hRN inf_le_left
      -- a third fixed point of `P`
      have hexists3 : ∃ ω₃ ∈ Submission.Blueprint.fixedPts H P,
          ω₃ ∉ ({ω₁, ω₂} : Set (G ⧸ H)) := by
        by_contra hc
        push_neg at hc
        have hle : (Submission.Blueprint.fixedPts H P).ncard ≤
            ({ω₁, ω₂} : Set (G ⧸ H)).ncard :=
          Set.ncard_le_ncard hc (Set.toFinite _)
        rw [Set.ncard_pair hω₂ne.symm] at hle
        omega
      obtain ⟨ω₃, hω₃, hω₃not⟩ := hexists3
      have hω₃notR : ω₃ ∉ Submission.Blueprint.fixedPts H R := by
        rw [show Submission.Blueprint.fixedPts H R = ({ω₁, ω₂} : Set (G ⧸ H)) from hRfix]
        exact hω₃not
      have hmoves : ∃ r ∈ R, r • ω₃ ≠ ω₃ := by
        by_contra hc
        push_neg at hc
        exact hω₃notR (Work.ThreePoints.mem_fixedPts.mpr (fun r hr => hc r hr))
      obtain ⟨r, hrR, hrω⟩ := hmoves
      -- the `M`-orbit of `ω₃` has `≤ 2` points; the `R`-orbit is contained in it
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
        have hmem3 : r • ω₃ ∈ MulAction.orbit R ω₃ :=
          MulAction.mem_orbit_iff.mpr ⟨⟨r, hrR⟩, rfl⟩
        have h1 : 1 < (MulAction.orbit R ω₃).ncard :=
          (Set.one_lt_ncard (Set.toFinite _)).mpr
            ⟨ω₃, MulAction.mem_orbit_self (M := ↥R) ω₃, r • ω₃, hmem3, hrω.symm⟩
        omega
      have horb2 : (MulAction.orbit R ω₃).ncard = 2 := le_antisymm hleR hgeR
      -- but `2 ∣ |R| ∣ p ^ k`, while `p` is odd
      have hdvd : (MulAction.orbit R ω₃).ncard ∣ Nat.card R := by
        refine ⟨Nat.card ↥(MulAction.stabilizer R ω₃), ?_⟩
        rw [mul_comm, ← MulAction.index_stabilizer, Subgroup.card_mul_index]
      have h2R : 2 ∣ Nat.card R := by rw [horb2] at hdvd; exact hdvd
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := ↥R)).mp hRg
      rw [hk] at h2R
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2R)).symm

end Work.DoubleTransitivity.Sec3
