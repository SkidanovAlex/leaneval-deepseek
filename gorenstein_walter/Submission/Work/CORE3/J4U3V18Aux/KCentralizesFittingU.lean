import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1aBothInvert

/-!
# CORE3 / J4U3V18Aux: `K = I_U(s)` centralizes `F(U)`

Bender 1981, §3, subcase (1b): `Case1 B` holds and `V = O₂(Ĥ)` is a four-group.  The Hall
subgroup `K = D.K` of `F(U) = fittingIn B.U` is `I_U(s) = invSet B.U s` for every involution
`s ∈ Ĥ ∖ V` (`Case1bData.inv`), and Bender's per-prime step of Theorem 2.10 (his Case (1) route)
says that such an `s` centralizes or inverts every `p`-core `O_p(U)` of `U = O(Ĥ)`.

In the (1b) configuration `Case1 B` *supplies* the Hall property: for `s ∈ S ∖ S₀` the set
`invSet B.U s` is the carrier of a Hall subgroup of `F(U)` (`Case1`'s first conjunct), namely
`D.K` itself.  The all-or-nothing lemma for a normal Hall subgroup
(`Work.CORE3.isPGroup_le_or_inf_eq_bot_of_isHallIn`) then converts the Hall property into the
per-prime dichotomy (`Work.CORE3.Case1aBothInvert`'s `pCoreIn_inverted_or_centralized`), and the
key step of Bender's argument (`Work.CORE2B.invSet_commute_pCore`) turns the dichotomy into the
elementwise commutation `[I_U(s), F(U)] = 1` (via `F(U) = ⨆_p O_p(U)`,
`Work.CORE3.c1aFittingIn_eq_iSup_pCoreIn`).

Everything therefore rests on the CORE3 API of `Submission.Work.CORE3.Case1aSetup` and on the
existence, proved below, of an involution `s ∈ S ∖ (S₀ ∪ V)` — the only configuration input.

Note on imports: this module deliberately stays inside the `Submission.Work.ASM.Defs` lineage of
the shared `Work.GW2` vocabulary.  It must not import any `Submission.Work.CORE2B` module, whose
closure re-declares `Work.GW2` (`Submission.Work.CORE2B.Defs`).
-/

namespace Work.CORE3.J4U3V18Aux

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- A subgroup of type `(2,2)` is not cyclic: every element of a four-group is an involution,
whereas a cyclic group of order `4` has an element of order `4`. -/
private theorem not_isCyclic_of_isFourGroup_local {G : Type} [Group G] {V : Subgroup G}
    (h : Work.GW2.IsFourGroup V) : ¬ IsCyclic V := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := V)
  have hgm : orderOf (g : G) = Nat.card V := by
    simpa using (Subgroup.orderOf_mk (g : G) g.2).symm.trans hg
  have hle : orderOf (g : G) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr (h.2 (g : G) g.2))
  rw [hgm, h.1] at hle
  omega

/-- **The key step of Bender's argument.**  If the involution `s` normalizes `U` and centralizes
or inverts `O_p(U)`, then every element of `I_U(s)` commutes with every element of `O_p(U)`.

Indeed `σ := conj s` and `α := conj x` are automorphisms of `O_p(U)` with `σ α σ⁻¹ = α⁻¹`
(because `s x s⁻¹ = x⁻¹`) and `σ` is the identity or the inversion, so `α² = 1`; as `x` has odd
order, `ord α ∣ ord x` is odd and `α = 1`. -/
private theorem invSet_commute_pCore_local {G : Type} [Group G] [Finite G]
    (U : Subgroup G) (s x y : G) (p : ℕ) [Fact p.Prime]
    (hoddU : Odd (Nat.card U)) (hss : s * s = 1)
    (hsN : s ∈ Subgroup.normalizer (U : Set G))
    (hx : x ∈ Work.GW2.invSet U s) (hy : y ∈ Work.GW2.pCoreIn p U)
    (hact : (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z) ∨
            (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z⁻¹)) :
    x * y = y * x := by
  have hoddx : Odd (orderOf x) :=
    Odd.of_dvd_nat hoddU (Subgroup.orderOf_dvd_natCard U hx.1)
  have hxinv : s * x * s⁻¹ = x⁻¹ := hx.2
  have hsxinv : s * x⁻¹ * s⁻¹ = x := by
    have h' : (s * x * s⁻¹)⁻¹ = s * x⁻¹ * s⁻¹ := by group
    rw [hxinv, inv_inv] at h'
    exact h'.symm
  have hxP : x ∈ Subgroup.normalizer ((Work.GW2.pCoreIn p U : Subgroup G) : Set G) :=
    Work.CORE3.c1aLe_normalizer_pCoreIn p U (Subgroup.le_normalizer hx.1)
  have hsP : s ∈ Subgroup.normalizer ((Work.GW2.pCoreIn p U : Subgroup G) : Set G) :=
    Work.CORE3.c1aLe_normalizer_pCoreIn p U hsN
  have key : ∀ z ∈ Work.GW2.pCoreIn p U, x * z * x⁻¹ = x⁻¹ * z * x := by
    intro z hz
    have hzP : s * z * s⁻¹ ∈ Work.GW2.pCoreIn p U :=
      (Subgroup.mem_normalizer_iff.mp hsP z).mp hz
    have hzP' : x * z * x⁻¹ ∈ Work.GW2.pCoreIn p U :=
      (Subgroup.mem_normalizer_iff.mp hxP z).mp hz
    rcases hact with hcen | hinv
    · have h1 : s * (x * z * x⁻¹) * s⁻¹ = x⁻¹ * z * x := by
        rw [show s * (x * z * x⁻¹) * s⁻¹
              = (s * x * s⁻¹) * (s * z * s⁻¹) * (s * x⁻¹ * s⁻¹) by group,
            hxinv, hcen z hz, hsxinv]
      have h2 : s * (x * z * x⁻¹) * s⁻¹ = x * z * x⁻¹ := hcen _ hzP'
      exact h2.symm.trans h1
    · have hzinv : z⁻¹ ∈ Work.GW2.pCoreIn p U := inv_mem hz
      have hzP'' : x * z⁻¹ * x⁻¹ ∈ Work.GW2.pCoreIn p U :=
        (Subgroup.mem_normalizer_iff.mp hxP z⁻¹).mp hzinv
      have h1 : s * (x * z⁻¹ * x⁻¹) * s⁻¹ = x⁻¹ * z * x := by
        rw [show s * (x * z⁻¹ * x⁻¹) * s⁻¹
              = (s * x * s⁻¹) * (s * z⁻¹ * s⁻¹) * (s * x⁻¹ * s⁻¹) by group,
            hxinv, hinv z⁻¹ hzinv, hsxinv]
        simp
      have h2 : s * (x * z⁻¹ * x⁻¹) * s⁻¹ = (x * z⁻¹ * x⁻¹)⁻¹ := hinv _ hzP''
      have h3 : (x * z⁻¹ * x⁻¹)⁻¹ = x * z * x⁻¹ := by group
      exact h3.symm.trans (h2.symm.trans h1)
  have hkey2 : ∀ z ∈ Work.GW2.pCoreIn p U, x * x * z = z * (x * x) := by
    intro z hz
    have h := key z hz
    have h2 : x * (x * z * x⁻¹) * x = x * (x⁻¹ * z * x) * x := by rw [h]
    have h3 : x * (x * z * x⁻¹) * x = x * x * z := by group
    have h4 : x * (x⁻¹ * z * x) * x = z * (x * x) := by group
    rw [h3, h4] at h2
    exact h2
  obtain ⟨k, hk⟩ := hoddx
  have hpow : (x * x) ^ (k + 1) = x := by
    have h1 : (x * x) ^ (k + 1) = x ^ (2 * (k + 1)) := by rw [← pow_two, ← pow_mul]
    rw [h1, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ,
      show x ^ (2 * k + 1) = 1 by rw [← hk, pow_orderOf_eq_one], one_mul]
  have hcomm : Commute (x * x) y := hkey2 y hy
  have hxx := (hcomm.pow_left (k + 1)).eq
  rwa [hpow] at hxx

/-- **The result.**  In the (1b) configuration `K = I_U(s)` centralizes the Fitting subgroup
`F(U) = fittingIn B.U`. -/
theorem KCentralizesFittingU {G : Type} [Group G] [Finite G]
    (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) :
    D.K ≤ Subgroup.centralizer (Work.GW2.fittingIn B.U : Set G) := by
  classical
  have hFT : Work.GW2.FeitThompsonProp := I.T.ft
  have h26 : Work.GW2.Thm26Concl B := I.h26 G hFT h B
  have hVleS : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) :=
    Work.CORE2A.thm26Concl_O2_le_S h26
  have hS0card : Nat.card B.S0 = 4 := by
    have hh := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [inf_eq_left.mpr B.S0_le, B.S0_index, D.S8] at hh
    omega
  have hVnc : ¬ IsCyclic (Work.GW2.pCoreIn 2 B.Hhat) :=
    not_isCyclic_of_isFourGroup_local D.four
  -- an involution of `S` outside `S₀` and outside `V = O₂(Ĥ)`
  have hexists : ∃ s ∈ (B.S : Subgroup G), s ∉ B.S0 ∧ s ∉ Work.GW2.pCoreIn 2 B.Hhat := by
    by_contra hcon
    have hSsub : ∀ x ∈ (B.S : Subgroup G), x ∈ B.S0 ∨ x ∈ Work.GW2.pCoreIn 2 B.Hhat := by
      intro x hx
      by_cases hx0 : x ∈ B.S0
      · exact Or.inl hx0
      · exact Or.inr (by
          by_contra hxV
          exact hcon ⟨x, hx, hx0, hxV⟩)
    have hS0notleV : ¬ B.S0 ≤ Work.GW2.pCoreIn 2 B.Hhat := by
      intro hle
      have heq : B.S0 = Work.GW2.pCoreIn 2 B.Hhat :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hS0card, D.four.1])
      exact hVnc (heq ▸ B.S0_cyclic)
    have hVnotleS0 : ¬ Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0 := by
      intro hle
      haveI : IsCyclic ↥B.S0 := B.S0_cyclic
      haveI h1c : IsCyclic ↥((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.S0) := inferInstance
      exact hVnc (isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hle).surjective)
    obtain ⟨a, haS0, haV⟩ := Set.not_subset.mp hS0notleV
    obtain ⟨b, hbV, hbS0⟩ := Set.not_subset.mp hVnotleS0
    have habS : a * b ∈ (B.S : Subgroup G) :=
      (B.S).mul_mem (B.S0_le haS0) (hVleS hbV)
    rcases hSsub (a * b) habS with hh | hh
    · apply hbS0
      have hmem := (B.S0).mul_mem ((B.S0).inv_mem haS0) hh
      rwa [show a⁻¹ * (a * b) = b from by group] at hmem
    · apply haV
      have hmem := (Work.GW2.pCoreIn 2 B.Hhat).mul_mem hh
        ((Work.GW2.pCoreIn 2 B.Hhat).inv_mem hbV)
      rwa [show a * b * b⁻¹ = a from by group] at hmem
  obtain ⟨s, hsS, hs0, hsV⟩ := hexists
  obtain ⟨n, hn2, hdih⟩ := Work.CORE3.SylowDihedral G h B
  have hs2 : orderOf s = 2 := Work.CORE3.OutsideS0OrderTwo G h B n hn2 hdih s hsS hs0
  have hsH : s ∈ B.Hhat := Work.CORE2A.bSetup_S_le_Hhat B hsS
  have hsN : s ∈ Subgroup.normalizer (B.U : Set G) := by
    have hUnorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
      rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
      simpa [Work.GW2.oddCoreIn] using
        Work.CORE3.c1aLe_normalizer_map_subtype (K := B.Hhat)
          (N := Work.GW2.oddCore ↥B.Hhat) (Work.GW2.oddCore_normal ↥B.Hhat)
    exact hUnorm hsH
  have hss : s * s = 1 := by
    have hh := pow_orderOf_eq_one s
    rw [hs2] at hh
    simpa [pow_two] using hh
  have hKset : (D.K : Set G) = Work.GW2.invSet B.U s := D.inv s hsH hs2 hsV
  have hKmem : ∀ y : G, y ∈ D.K ↔ y ∈ Work.GW2.invSet B.U s := by
    intro y
    show y ∈ (D.K : Set G) ↔ y ∈ Work.GW2.invSet B.U s
    rw [hKset]
  -- Bender's per-prime dichotomy for `O_q(U)`
  have hdich : ∀ q : ℕ, Nat.Prime q →
      (∀ x ∈ Work.GW2.pCoreIn q B.U, s * x * s⁻¹ = x⁻¹) ∨
      Work.GW2.pCoreIn q B.U ≤ Subgroup.centralizer ({s} : Set G) := by
    intro q hq
    haveI : Fact q.Prime := ⟨hq⟩
    have hc15 := (I.T.c15 G hFT B.U s hs2 (Work.CORE2A.bSetup_U_odd B) hsN).2.2 D.K hKset
    have hnormU : (D.K.subgroupOf B.U).Normal := hc15.2.1
    have hIhle : D.K ≤ Work.GW2.fittingIn B.U := hc15.2.2
    have hInormF : (D.K.subgroupOf (Work.GW2.fittingIn B.U)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer D.hall.1).mpr
        (le_trans (Work.CORE3.c1aFittingIn_le B.U)
          ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (le_trans D.hall.1 (Work.CORE3.c1aFittingIn_le B.U))).mp hnormU))
    rcases Work.CORE3.isPGroup_le_or_inf_eq_bot_of_isHallIn hq D.hall hInormF
        (Work.CORE3.c1aPcoreIn_le_fittingIn q B.U) (Work.CORE3.c1aIsPGroup_pCoreIn q B.U)
      with hle | hdisj
    · left
      intro x hx
      exact ((hKmem x).mp (hle hx)).2
    · right
      refine Work.CORE3.c1aCentralizer_of_no_inverted (Q := Work.GW2.pCoreIn q B.U) (x := s) hss
        (Work.CORE3.c1aLe_normalizer_pCoreIn q B.U hsN) ?_
      intro y hy hyinv
      have hyU : y ∈ B.U := Work.CORE3.c1aPcoreIn_le_self q B.U hy
      have hyK : y ∈ D.K := (hKmem y).mpr ⟨hyU, hyinv⟩
      have hmem : y ∈ Work.GW2.pCoreIn q B.U ⊓ D.K := ⟨hy, hyK⟩
      rw [hdisj] at hmem
      simpa using hmem
  -- "centralizes or inverts", in the orientation used by `invSet_commute_pCore_local`
  have hact : ∀ q : ℕ, Nat.Prime q →
      (∀ z ∈ Work.GW2.pCoreIn q B.U, s * z * s⁻¹ = z) ∨
      (∀ z ∈ Work.GW2.pCoreIn q B.U, s * z * s⁻¹ = z⁻¹) := by
    intro q hq
    rcases hdich q hq with hinv | hcen
    · exact Or.inr hinv
    · refine Or.inl ?_
      intro z hz
      have hcomm : s * z = z * s :=
        (Subgroup.mem_centralizer_iff.mp (hcen hz)) s (by simp)
      calc s * z * s⁻¹ = s * z * s := by rw [inv_eq_of_mul_eq_one_right hss]
        _ = z * s * s := by rw [hcomm]
        _ = z := by rw [mul_assoc, hss, mul_one]
  -- `I_U(s)` centralizes `F(U)`, since `F(U) = ⨆_q O_q(U)`
  have hcen : ∀ x ∈ Work.GW2.invSet B.U s, ∀ y ∈ Work.GW2.fittingIn B.U, x * y = y * x := by
    intro x hx y hy
    have hle : (⨆ p : Nat.Primes, Work.GW2.pCoreIn p.val B.U) ≤
        Subgroup.centralizer ({x} : Set G) := by
      refine iSup_le fun p => ?_
      haveI : Fact (Nat.Prime p.val) := ⟨p.2⟩
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact invSet_commute_pCore_local B.U s x z p.val
        (Work.CORE2A.bSetup_U_odd B) hss hsN hx hz (hact p.val p.2)
    have hy' : y ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Work.CORE3.c1aFittingIn_eq_iSup_pCoreIn] at hy
      exact hle hy
    rw [Subgroup.mem_centralizer_iff] at hy'
    exact hy' x (by simp)
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hcen k ((hKmem k).mp hk) y hy).symm

end Work.CORE3.J4U3V18Aux
