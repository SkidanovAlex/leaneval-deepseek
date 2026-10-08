import Mathlib
import Submission.Work.CORE3.Defs

/-!
# CORE3: a quasisimple subgroup centralizes a normal subgroup of odd order

This file proves

* `Work.CORE3.QuasisimpleCentralizesOddNormal` : if `E ◁ X` is quasisimple
  (`⁅E,E⁆ = E` and `E/Z(E)` simple, Bender's convention) and `O ◁ X` has odd order, and moreover
  the simple quotient `E/Z(E)` has even order, then `⁅E, O⁆ = ⊥`, i.e. `E` centralizes `O`.

## Mathematics

Put `M = ⁅E, O⁆ ◁ X`.  Then `M ≤ E` and `M ≤ O`.

*`M` commutes with `E`, or `E ≤ M`.*  `M ◁ E`, so its image in the simple group `E/Z(E)` is
`⊥` or `⊤`; this is the standard components dichotomy (proved here as
`Work.CORE3.le_centralizer_or_eq_of_isQuasisimple`).

* If `M ≤ Z(E)`, i.e. `M` commutes with `E`:  `E` is perfect, so `⁅E,E⁆ = E`, and the Three
  Subgroups Lemma gives `⁅E, O⁆ = ⁅⁅E,E⁆, O⁆ ≤ ⁅⁅E,O⁆,E⁆·⁅⁅O,E⁆,E⁆ = 1`.
* If `E ≤ M`: then `E ≤ M ≤ O` has odd order, so `|E|` is odd; but `|E| = |Z(E)|·|E/Z(E)|`
  with `|E/Z(E)|` even, so `|E|` is even.  Contradiction.

No Feit–Thompson is used: the evenness of `|E/Z(E)|` is exactly what rules out the second case.
-/

set_option linter.style.haveILetI false

namespace Work.CORE3

open Subgroup

/-- **The dichotomy.**  Let `M ◁ X` be a normal subgroup contained in a normal quasisimple
subgroup `E ◁ X`.  Then either `M` centralizes `E`, or `E ≤ M`.

The subgroup `M.subgroupOf E` is normal in `↥E`, so its image in the simple group `E/Z(E)` is
`⊥` or `⊤`.  In the first case `M ≤ Z(E)`, so `M` centralizes `E`.  In the second case
`M ⊔ Z(E) = E`, and `⁅Z(E), E⁆ = ⊥`, so `E = ⁅E,E⁆ ≤ ⁅M ⊔ Z(E), E⁆ = ⁅M,E⁆ ≤ M`. -/
theorem le_centralizer_or_eq_of_isQuasisimple {X : Type*} [Group X] {M E : Subgroup X}
    (hMn : M.Normal) (hME : M ≤ E) (hEn : E.Normal) (hEq : Work.GW2.IsQuasisimple E) :
    M ≤ Subgroup.centralizer (E : Set X) ∨ E ≤ M := by
  haveI := hMn
  haveI := hEn
  set Z : Subgroup ↥E := Subgroup.center ↥E with hZdef
  set ME : Subgroup ↥E := M.subgroupOf E with hMEdef
  have hMEnor : ME.Normal := hMn.subgroupOf E
  haveI := hMEnor
  haveI := hEq.2
  have hmapnor : (ME.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map hMEnor _ (QuotientGroup.mk'_surjective Z)
  haveI := hmapnor
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ME.map (QuotientGroup.mk' Z)) with hbot | htop
  · -- `M` maps into the centre of `E`, hence centralizes `E`
    left
    have hMEleZ : ME ≤ Z := by
      have h := (Subgroup.map_eq_bot_iff ME).mp hbot
      rwa [QuotientGroup.ker_mk' Z] at h
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hmE : m ∈ E := hME hm
    have hz : (⟨m, hmE⟩ : ↥E) ∈ Z := hMEleZ hm
    have hcomm := Subgroup.mem_center_iff.mp hz (⟨e, he⟩ : ↥E)
    simpa using congrArg Subtype.val hcomm
  · -- `M ⊔ Z(E) = E`, and `E` is perfect, so `E ≤ M`
    right
    have hsup : ME ⊔ Z = ⊤ := by
      have h := QuotientGroup.comap_map_mk' Z ME
      rw [htop, Subgroup.comap_top] at h
      rw [sup_comm] at h
      exact h.symm
    have hsupX : M ⊔ Z.map E.subtype = E := by
      have h1 := congrArg (Subgroup.map E.subtype) hsup
      rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h1
      rw [hMEdef, Subgroup.subgroupOf_map_subtype M E, inf_eq_left.mpr hME] at h1
      exact h1
    have hZcen : ⁅Z.map E.subtype, E⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨z', hz', rfl⟩ := hz
      have hcomm := Subgroup.mem_center_iff.mp hz' (⟨e, he⟩ : ↥E)
      simpa using congrArg Subtype.val hcomm
    have hEEleM : ⁅E, E⁆ ≤ M := by
      have hmono : ⁅E, E⁆ ≤ ⁅M ⊔ Z.map E.subtype, E⁆ :=
        Subgroup.commutator_mono (le_of_eq hsupX.symm) le_rfl
      have hsplit : ⁅M ⊔ Z.map E.subtype, E⁆ = ⁅M, E⁆ ⊔ ⁅Z.map E.subtype, E⁆ :=
        Subgroup.commutator_sup_right M (Z.map E.subtype) E
      have hMEleM : ⁅M, E⁆ ≤ M := Subgroup.commutator_le_left M E
      calc ⁅E, E⁆ ≤ ⁅M ⊔ Z.map E.subtype, E⁆ := hmono
        _ = ⁅M, E⁆ ⊔ ⁅Z.map E.subtype, E⁆ := hsplit
        _ = ⁅M, E⁆ := by rw [hZcen, sup_bot_eq]
        _ ≤ M := hMEleM
    rw [hEq.1] at hEEleM
    exact hEEleM

/-- **A quasisimple subgroup centralizes a normal subgroup of odd order.**

`E ◁ X` quasisimple with `|E/Z(E)|` even, `O ◁ X` of odd order, implies `⁅E, O⁆ = ⊥`.

See the module docstring for the two-case argument. -/
theorem QuasisimpleCentralizesOddNormal {X : Type*} [Group X] [Finite X]
    {E O : Subgroup X} (hEn : E.Normal) (hEq : Work.GW2.IsQuasisimple E) (hOn : O.Normal)
    (hOodd : Odd (Nat.card O))
    (hEeven : Even (Nat.card (↥E ⧸ Subgroup.center ↥E))) : ⁅E, O⁆ = ⊥ := by
  haveI := hEn
  haveI := hOn
  set M : Subgroup X := ⁅E, O⁆ with hMdef
  have hME : M ≤ E := Subgroup.commutator_le_left E O
  have hMO : M ≤ O := Subgroup.commutator_le_right E O
  have hMnor : M.Normal := Subgroup.commutator_normal E O
  rcases le_centralizer_or_eq_of_isQuasisimple hMnor hME hEn hEq with hcen | hEM
  · -- `M` centralizes `E`; rotate with `⁅E,E⁆ = E` to get `⁅E,O⁆ = ⊥`
    have hMEbot : ⁅M, E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcen
    have h2 : ⁅⁅O, E⁆, E⁆ = ⊥ := by rw [Subgroup.commutator_comm O E]; exact hMEbot
    have h3 : ⁅⁅E, E⁆, O⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hMEbot h2
    rw [hEq.1] at h3
    rwa [hMdef]
  · -- `E ≤ M ≤ O` forces `|E|` odd; but `|E/Z(E)|` even forces `|E|` even
    exfalso
    have hEO : E ≤ O := le_trans hEM hMO
    have hdvd : Nat.card ↥E ∣ Nat.card O := Subgroup.card_dvd_of_le hEO
    have hoddE : Odd (Nat.card ↥E) := hOodd.of_dvd_nat hdvd
    have hq : Nat.card (↥E ⧸ Subgroup.center ↥E) ∣ Nat.card ↥E :=
      Subgroup.card_quotient_dvd_card (Subgroup.center ↥E)
    have hevenE : Even (Nat.card ↥E) := by
      rw [even_iff_two_dvd] at hEeven ⊢
      exact dvd_trans hEeven hq
    exact (Nat.not_even_iff_odd.mpr hoddE) hevenE

end Work.CORE3
