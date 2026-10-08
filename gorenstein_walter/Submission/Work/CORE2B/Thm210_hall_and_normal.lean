import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.HallAux
import Submission.Work.CORE2B.HallPerPrime
import Submission.Work.CORE2B.InvSetHallStructure

/-!
# AREA CORE2B — Bender's Theorem 2.10, first half: `I_U(s)` is Hall in `F(U)` and normal in `U`

`Work.CORE2B.Thm210_hall_and_normal` is Bender's first half of Theorem 2.10 (p. 222): for
`s ∈ S − S₀` the set `I_U(s) = {x ∈ U | s x s⁻¹ = x⁻¹}` is the carrier of a Hall subgroup of
`F(U)` normal in `U`.

The proof splits into

* `Work.CORE2B.HallPerPrime` (Bender's per-prime argument via 1.1.ii/1.1.iv and Lemma 2.7):
  for every prime `p`, `s` centralizes or acts fixed-point-freely on `O_p(U)`;
* the passage to "centralizes or inverts" (`centralizes_or_inverts_of_dichotomy`,
  `Work.BMAX.InvolutionInverts`);
* `Work.CORE2B.InvSetHallStructure`: the group-theoretic reduction to the Hall/normality
  statement;
* the elementary facts about the configuration (`S_dihedral_iso`,
  `orderOf_eq_two_of_mem_S_notMem_S0`, `odd_card_U_setup`, `mem_normalizer_U_of_mem_S`).
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

theorem Thm210_hall_and_normal (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (h27 : Work.GW2.Lemma27Prop) (h28 : Work.GW2.Lemma28Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (hnot1 : ¬ Work.GW2.Case1 B) (hnot2 : ¬ Work.GW2.Case2 B)
    (s : G) (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) :
    ∃ I : Subgroup G, (I : Set G) = Work.GW2.invSet B.U s ∧
      Work.GW2.IsHallIn I (Work.GW2.fittingIn B.U) ∧ (I.subgroupOf B.U).Normal := by
  have hs2 : orderOf s = 2 := orderOf_eq_two_of_mem_S_notMem_S0 hCtx B hs hs0
  have hsNs : s ∈ Subgroup.normalizer (B.U : Set G) := mem_normalizer_U_of_mem_S B hs
  have hoddU : Odd (Nat.card B.U) := odd_card_U_setup B
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hdich := HallPerPrime T h26 h27 h28 G hFT hCtx B hnot1 hnot2 s hs hs0
  have hH1 : ∀ p : ℕ, Nat.Prime p →
      (∀ z ∈ Work.GW2.pCoreIn p B.U, s * z * s⁻¹ = z) ∨
      (∀ z ∈ Work.GW2.pCoreIn p B.U, s * z * s⁻¹ = z⁻¹) := by
    intro p hp
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    exact centralizes_or_inverts_of_dichotomy (Work.GW2.pCoreIn p B.U) s hss
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_conj_pCoreIn (U := B.U) (p := p) hsNs))
      (hdich p hp)
  exact InvSetHallStructure hFT B.U s hoddU hs2 hsNs hH1

end Work.CORE2B
