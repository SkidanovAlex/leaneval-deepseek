/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DSTR area (fundmath3-gorenstein_walter), `Work.DSTR.d16`

# Bender 1.6, case `X/O(X)` a `2`-group (`Work.DSTR.D16Case1Prop`)

See `Submission/Work/DSTR/NOTES_D16_PLAN.md` for the mathematics.  Available here are the
`Work.DSTR`-local universal properties of the `π`-core / `p`-core / odd core (the copies in the
`GLUE` area cannot be imported next to `Submission.Work.DSTR.Defs` — duplicate `Work.GW2` names)
plus the pieces of the two branches.

Branch `O_2(X) = ⊥ ⟹ (a)`: `X` is solvable (`O(X)` is odd, hence solvable by
`FeitThompsonProp`, and `X/O(X)` is a `2`-group), `F(X) = F_{2'}(X)` because the `2`-part of the
nilpotent group `F(X)` is `O_2(F(X)) = O_2(X)`, and then Bender 1.2
(`Work.DSTR.fittingSelfCentralizing`) gives `C_X(F_{2'}(X)) = C_X(F(X)) ≤ F(X) = F_{2'}(X)`.

Branch `O_2(X) ≠ ⊥ ⟹ (b)`: `π(O_2(X)) = O_2(X)·O(X)/O(X) ≅ O_2(X)` (`O_2(X) ⊓ O(X) = ⊥`) is a
nontrivial normal subgroup of the `2`-group `Q = X/O(X)`, hence meets `Z(Q)`; a lifted element
of order `2` is in `Z(X)` (its commutators with `X` lie in `O_2(X) ⊓ O(X) = ⊥`).
-/
import Mathlib
import Submission.Work.DSTR.D16Aux
import Submission.Work.DSTR.D16Basic
import Submission.Work.DSTR.fittingSelfCentralizing
import Submission.Work.ASM.oddCore_odd
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.lemma24

open scoped MatrixGroups

namespace Work.DSTR

open Subgroup

/-- **Universal property of `O_p(X)`** in this area's vocabulary (local copy of the `GLUE`
lemma, which is not importable here).  `private`: the same lemma is also proved in
`Submission/Work/DSTR/fittingPiIn_eq_iSup_pCoreIn_prime.lean` (public, imported by BMAX/CORE3) and
in `Submission/Work/DSTR/d110iOdd.lean`, and the three modules must be importable together. -/
private theorem le_pCore_of_normal_isPGroup' {G : Type*} [Group G] {p : ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p N) : N ≤ Work.GW2.pCore p G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- **Universal property of `O_π(X)`** in this area's vocabulary. -/
theorem le_piCore_of_normal_isPiGroup' {G : Type*} [Group G] {π : Set ℕ} {N : Subgroup G}
    [N.Normal] (hN : Subgroup.IsPiSubgroup π N) : N ≤ Work.GW2.piCore π G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- **Universal property of `O(X)`** in this area's vocabulary. -/
theorem le_oddCore_of_odd_normal' {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ Work.GW2.oddCore G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- `O_p^{Isaacs}(X) ≤` our `pCore`: Isaacs' `opCore` is a normal `p`-subgroup. -/
theorem opCore_le_pCore (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] :
    OddOrder.Isaacs.Ch01.opCore p G ≤ Work.GW2.pCore p G :=
  le_pCore_of_normal_isPGroup' (OddOrder.Isaacs.Ch01.opCore_isPGroup p G)

/-- `F_π(X) ≤ F(X)`. -/
theorem fittingPi_le' (π : Set ℕ) (G : Type*) [Group G] :
    Work.GW2.fittingPi π G ≤ Work.GW2.fitting G :=
  Subgroup.map_subtype_le _


/-- **`O_p(X) ≤ F_{2'}(X)` for an odd prime `p`.**  `O_p(X)` is a normal subgroup of `X` of odd
order contained in `F(X)`; viewed inside `↥F(X)` it is a normal `{2}ᶜ`-subgroup of `F(X)`, hence
lies in `O_{2'}(F(X)) = F_{2'}(X)`. -/
theorem opCore_le_fittingPi_of_ne_two (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) : OddOrder.Isaacs.Ch01.opCore p X ≤ F2p X := by
  have hFle : OddOrder.Isaacs.Ch01.opCore p X ≤ Work.GW2.fitting X := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting]
    exact OddOrder.Isaacs.Ch01.opCore_le_fitting (p := ⟨p, ‹Fact p.Prime›.out⟩) X
  haveI hnorm : (OddOrder.Isaacs.Ch01.opCore p X).Normal :=
    OddOrder.Isaacs.Ch01.opCore.normal p X
  set K : Subgroup ↥(Work.GW2.fitting X) :=
    (OddOrder.Isaacs.Ch01.opCore p X).comap (Work.GW2.fitting X).subtype with hK
  have hKnormal : K.Normal := hnorm.comap (Work.GW2.fitting X).subtype
  have hKcard : Nat.card K = Nat.card (OddOrder.Isaacs.Ch01.opCore p X) := by
    rw [hK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFle).toEquiv
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (OddOrder.Isaacs.Ch01.opCore_isPGroup p X)
    rw [hn]
    exact Odd.pow (Nat.Prime.odd_of_ne_two ‹Fact p.Prime›.out hp)
  have hKpi : K ≤ Work.GW2.piCore ({2}ᶜ : Set ℕ) ↥(Work.GW2.fitting X) :=
    le_piCore_of_normal_isPiGroup' ((Work.ASM.odd_iff_isPiSubgroup_ne_two K).mp hKodd)
  intro x hx
  refine Subgroup.mem_map.mpr ⟨⟨x, hFle hx⟩, hKpi ?_, rfl⟩
  exact (Subgroup.mem_comap (f := (Work.GW2.fitting X).subtype)
    (K := OddOrder.Isaacs.Ch01.opCore p X)).mpr hx

/-- **`O_2(X) = ⊥` forces `F(X) = F_{2'}(X)`.**  Decompose `F(X) = ⨆_p O_p(X)` (Isaacs); the
`2`-core lies in `O_2(X) = ⊥` and the odd prime cores lie in `F_{2'}(X)`. -/
theorem fitting_le_fittingPi_of_pCore_two_eq_bot (X : Type) [Group X] [Finite X]
    (hA : Work.GW2.pCore 2 X = ⊥) : Work.GW2.fitting X ≤ F2p X := by
  rw [Work.CORE2A.fitting_eq_isaacsFitting]
  refine iSup_le fun p => ?_
  haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  by_cases hp : (p : ℕ) = 2
  · refine le_trans (le_of_le_of_eq (opCore_le_pCore (p : ℕ) X) ?_) bot_le
    rw [hp]; exact hA
  · exact opCore_le_fittingPi_of_ne_two X (p : ℕ) hp

/-- **Bender 1.6, case `X/O(X)` a `2`-group, branch `O_2(X) = ⊥`.**  Then `F(X) = F_{2'}(X)`,
`X` is solvable (`O(X)` is odd, and `X/O(X)` is a `2`-group), and Bender 1.2 gives clause (a). -/
theorem d16a_of_pCore_two_eq_bot (X : Type) [Group X] [Finite X]
    (hFT : Work.GW2.FeitThompsonProp) (hP : IsPGroup 2 (X ⧸ Work.GW2.oddCore X))
    (hA : Work.GW2.pCore 2 X = ⊥) : d16a X := by
  have hF : F2p X = Work.GW2.fitting X :=
    le_antisymm (fittingPi_le' ({2}ᶜ : Set ℕ) X)
      (fitting_le_fittingPi_of_pCore_two_eq_bot X hA)
  haveI : Group.IsSolvable ↥(Work.GW2.oddCore X) :=
    hFT ↥(Work.GW2.oddCore X) (Work.ASM.oddCore_odd X)
  haveI : Group.IsSolvable (X ⧸ Work.GW2.oddCore X) := by
    haveI : Group.IsNilpotent (X ⧸ Work.GW2.oddCore X) := IsPGroup.isNilpotent (p := 2) hP
    exact IsNilpotent.to_isSolvable
  haveI : Group.IsSolvable X := Group.isSolvable_of_subgroup_quotient (Work.GW2.oddCore X)
  show Subgroup.centralizer ((F2p X : Subgroup X) : Set X) ≤ F2p X
  rw [hF]
  exact fittingSelfCentralizing X inferInstance


/-- **`O_2(X) ⊓ O(X) = ⊥`.**  Every element `x` of the intersection has `2`-power order (it lies in
the `2`-group `O_2(X)`, `Work.CORE2A.pCore_isPGroup'`) and odd order (it lies in `O(X)`,
`Work.ASM.oddCore_odd`), hence order `1`; so `x = 1`.

The proof is `Nat.dvd_prime_pow Nat.prime_two` on `orderOf x ∣ |O_2(X)| = 2 ^ k`, then `hj0 : j = 0`
from `Odd (2 ^ j)` (via `Nat.not_even_iff_odd` and `pow_dvd_pow`), then `orderOf_eq_one_iff`.
Two API lookups remain, both one-liners: the `Fintype` instance needed by `orderOf_dvd_card` has to
be given explicitly (`Fintype.ofFinite (↥(Work.GW2.pCore 2 X))`), and the divisibility of `orderOf x`
by `Nat.card ↥(oddCore X)` for `x ∈ oddCore X` goes through `Subgroup.orderOf_coe` (or
`Subgroup.orderOf_dvd_card`) applied to `⟨x, hx.2⟩ : ↥(oddCore X)`. -/
theorem pCore_two_inf_oddCore_eq_bot (X : Type) [Group X] [Finite X] :
    Work.GW2.pCore 2 X ⊓ Work.GW2.oddCore X = ⊥ := by
  rw [← le_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Work.CORE2A.pCore_isPGroup' (X := X) (p := 2))
  have hdvd : orderOf x ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_dvd_natCard (Work.GW2.pCore 2 X) hx.1
  obtain ⟨j, _hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hodd2 : Odd (2 ^ j) := by
    rw [← hjeq]
    exact Odd.of_dvd_nat (Work.ASM.oddCore_odd X)
      (Subgroup.orderOf_dvd_natCard (Work.GW2.oddCore X) hx.2)
  have hj0 : j = 0 := by
    by_contra hjne
    have hge : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hjne
    have hdvd2 : 2 ∣ 2 ^ j := ⟨2 ^ (j - 1), by rw [← pow_succ', Nat.sub_add_cancel hge]⟩
    exact absurd (even_iff_two_dvd.mpr hdvd2) (Nat.not_even_iff_odd.mpr hodd2)
  rw [hj0, pow_zero] at hjeq
  exact orderOf_eq_one_iff.mp hjeq


/-- **`π(O_2(X)) = O_2(X)·O(X)/O(X) ≠ ⊥` when `O_2(X) ≠ ⊥`.**  Since `O_2(X) ⊓ O(X) = ⊥`
(`pCore_two_inf_oddCore_eq_bot`), the quotient map is injective on `O_2(X)`, so a nontrivial
`O_2(X)` has nontrivial image — the image is a normal `2`-subgroup of `X/O(X)`, which is what
feeds `Group.IsNilpotent.inf_center_ne_bot_of_normal` in the central-involution argument. -/
theorem map_pCore_two_ne_bot (X : Type) [Group X] [Finite X]
    (hA : Work.GW2.pCore 2 X ≠ ⊥) :
    (Work.GW2.pCore 2 X).map (QuotientGroup.mk' (Work.GW2.oddCore X)) ≠ ⊥ := by
  intro h
  apply hA
  rw [eq_bot_iff]
  intro a ha
  have hmem : QuotientGroup.mk' (Work.GW2.oddCore X) a ∈
      (Work.GW2.pCore 2 X).map (QuotientGroup.mk' (Work.GW2.oddCore X)) := ⟨a, ha, rfl⟩
  rw [h] at hmem
  have haO : a ∈ Work.GW2.oddCore X :=
    (QuotientGroup.eq_one_iff a).mp (by simpa using hmem)
  have hinf : a ∈ Work.GW2.pCore 2 X ⊓ Work.GW2.oddCore X := ⟨ha, haO⟩
  rw [pCore_two_inf_oddCore_eq_bot] at hinf
  simpa using hinf


/-- **An involution in `π(O_2(X)) ⊓ Z(X/O(X))`.**  `π(O_2(X))` is a nontrivial normal subgroup of
the nilpotent group `X/O(X)` (`map_pCore_two_ne_bot`), so it meets the centre
(`Group.IsNilpotent.inf_center_ne_bot_of_normal`); the intersection is a nontrivial `2`-group, so
Cauchy (`exists_prime_orderOf_dvd_card'`) supplies an element of order `2`. -/
theorem exists_involution_mem_map_pCore_two_inf_center (X : Type) [Group X] [Finite X]
    (hP : IsPGroup 2 (X ⧸ Work.GW2.oddCore X)) (hA : Work.GW2.pCore 2 X ≠ ⊥) :
    ∃ w ∈ (Work.GW2.pCore 2 X).map (QuotientGroup.mk' (Work.GW2.oddCore X)) ⊓
        Subgroup.center (X ⧸ Work.GW2.oddCore X), orderOf w = 2 := by
  haveI : Group.IsNilpotent (X ⧸ Work.GW2.oddCore X) := IsPGroup.isNilpotent (p := 2) hP
  set N : Subgroup (X ⧸ Work.GW2.oddCore X) :=
    (Work.GW2.pCore 2 X).map (QuotientGroup.mk' (Work.GW2.oddCore X)) with hN
  have hNne : N ≠ ⊥ := map_pCore_two_ne_bot X hA
  have hcenter : N ⊓ Subgroup.center (X ⧸ Work.GW2.oddCore X) ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hNne
  have hN2 : IsPGroup 2 ↥N := by
    rw [hN]
    exact (Work.CORE2A.pCore_isPGroup' (X := X) (p := 2)).map _
  obtain ⟨x, hxK, hxne⟩ : ∃ x ∈ (N ⊓ Subgroup.center (X ⧸ Work.GW2.oddCore X)), x ≠ 1 := by
    by_contra h
    exact hcenter (eq_bot_iff.mpr fun y hy => by
      by_contra hyne
      exact h ⟨y, hy, hyne⟩)
  have hlt : 1 < Nat.card ↥(N ⊓ Subgroup.center (X ⧸ Work.GW2.oddCore X)) :=
    Finite.one_lt_card_iff_nontrivial.mpr
      ⟨⟨⟨x, hxK⟩, ⟨1, ⟨N.one_mem, (Subgroup.center _).one_mem⟩⟩, fun hh => hxne (Subtype.ext_iff.mp hh)⟩⟩
  have h2 : 2 ∣ Nat.card ↥(N ⊓ Subgroup.center (X ⧸ Work.GW2.oddCore X)) := by
    refine (hN2.to_le inf_le_left).card_eq_or_dvd.resolve_left ?_
    omega
  obtain ⟨w₀, hworder⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨(w₀ : X ⧸ Work.GW2.oddCore X), Subgroup.mem_inf.mp w₀.2, ?_⟩
  rw [Subgroup.orderOf_coe, hworder]


/-- **Bender 1.6(b) in case 1: `O_2(X) ≠ ⊥` gives a central involution.**  Lift the involution
`w ∈ π(O_2(X)) ⊓ Z(X/O(X))` (`exists_involution_mem_map_pCore_two_inf_center`) to `a ∈ O_2(X)`:
`π (a²) = w² = 1` forces `a² ∈ O_2(X) ⊓ O(X) = ⊥`, so `a² = 1`, and `a ≠ 1`; and for every `x`,
`π ([x,a]) = [πx, w] = 1`, so `[x,a] ∈ O_2(X) ⊓ O(X) = ⊥`, i.e. `a` is central. -/
theorem exists_central_involution_of_pCore_two_ne_bot (X : Type) [Group X] [Finite X]
    (hP : IsPGroup 2 (X ⧸ Work.GW2.oddCore X)) (hA : Work.GW2.pCore 2 X ≠ ⊥) :
    ∃ z : X, z ∈ Subgroup.center X ∧ orderOf z = 2 := by
  obtain ⟨w, hw, hworder⟩ := exists_involution_mem_map_pCore_two_inf_center X hP hA
  obtain ⟨hwN, hwZ⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨a, ha, haw⟩ := Subgroup.mem_map.mp hwN
  have hwne : w ≠ 1 := by rintro rfl; simp at hworder
  have hane : a ≠ 1 := fun h => hwne (by rw [← haw, h]; rfl)
  have hw2 : w ^ 2 = 1 := by rw [← hworder]; exact pow_orderOf_eq_one w
  have ha2O : a ^ 2 ∈ Work.GW2.oddCore X :=
    (QuotientGroup.eq_one_iff (a ^ 2)).mp (by
      calc QuotientGroup.mk' (Work.GW2.oddCore X) (a ^ 2)
          = (QuotientGroup.mk' (Work.GW2.oddCore X) a) ^ 2 := map_pow _ a 2
        _ = w ^ 2 := by rw [haw]
        _ = 1 := hw2)
  have ha2 : a ^ 2 = 1 := by
    have hinf : a ^ 2 ∈ Work.GW2.pCore 2 X ⊓ Work.GW2.oddCore X :=
      ⟨Subgroup.pow_mem (Work.GW2.pCore 2 X) ha 2, ha2O⟩
    rw [pCore_two_inf_oddCore_eq_bot X] at hinf
    simpa using hinf
  have horder : orderOf a = 2 := by
    have hdvd : orderOf a ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; exact ha2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hane
    · exact h
  refine ⟨a, ?_, horder⟩
  rw [Subgroup.mem_center_iff]
  intro x
  have hxa : x * a * x⁻¹ = a := by
    refine mul_inv_eq_one.mp ?_
    have hcw := Subgroup.mem_center_iff.mp hwZ (QuotientGroup.mk' (Work.GW2.oddCore X) x)
    have hO : x * a * x⁻¹ * a⁻¹ ∈ Work.GW2.oddCore X :=
      (QuotientGroup.eq_one_iff _).mp (by
        calc QuotientGroup.mk' (Work.GW2.oddCore X) (x * a * x⁻¹ * a⁻¹)
            = ((QuotientGroup.mk' (Work.GW2.oddCore X) x) * w *
               (QuotientGroup.mk' (Work.GW2.oddCore X) x)⁻¹) * w⁻¹ := by
              simp only [map_mul, map_inv, haw]
          _ = 1 := by rw [hcw]; group)
    have hAcore : x * a * x⁻¹ * a⁻¹ ∈ Work.GW2.pCore 2 X := by
      haveI : (Work.GW2.pCore 2 X).Normal := inferInstance
      exact mul_mem (‹(Work.GW2.pCore 2 X).Normal›.conj_mem a ha x) (inv_mem ha)
    have hinf : x * a * x⁻¹ * a⁻¹ ∈ Work.GW2.pCore 2 X ⊓ Work.GW2.oddCore X :=
      ⟨hAcore, hO⟩
    rw [pCore_two_inf_oddCore_eq_bot X] at hinf
    simpa using hinf
  have hcomm : x * a = a * x := by
    have hh := congrArg (· * x) hxa
    simpa [mul_assoc] using hh
  exact hcomm

/-- **Bender 1.6, case `X/O(X)` a `2`-group.**  Branch `O_2(X) = ⊥` is
`d16a_of_pCore_two_eq_bot`; branch `O_2(X) ≠ ⊥` is the central-involution argument of the module
docstring. -/
theorem case1 : Work.DSTR.D16Case1Prop := by
  intro X instG instF hFT hD hP
  by_cases hA : Work.GW2.pCore 2 X = ⊥
  · exact Or.inl (d16a_of_pCore_two_eq_bot X hFT hP hA)
  · exact Or.inr (exists_central_involution_of_pCore_two_ne_bot X hP hA)

end Work.DSTR
