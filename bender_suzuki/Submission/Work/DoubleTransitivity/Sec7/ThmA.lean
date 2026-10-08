import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.App1.Defs
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.DoubleTransitivity.App1.app1_2
import Submission.Work.DoubleTransitivity.App2.app2_1
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.DoubleTransitivity.App2.app2_3
import Submission.Work.DoubleTransitivity.App2.app2_4
import Submission.Work.DoubleTransitivity.App2.app2_5
import Submission.Work.DoubleTransitivity.App2.app2_6
import Submission.Work.DoubleTransitivity.App2.app2_7
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Sec1.sylow_of_sylowIn
import Submission.Work.DoubleTransitivity.Sec1.restrict
import Submission.Work.DoubleTransitivity.Sec1.normalizer_eq
import Submission.Work.DoubleTransitivity.Sec2.prop1a_odd
import Submission.Work.DoubleTransitivity.Sec2.prop1a_exists
import Submission.Work.DoubleTransitivity.Sec2.prop1a_unique
import Submission.Work.DoubleTransitivity.Sec2.inv_class
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.DoubleTransitivity.Sec2.lemma1
import Submission.Work.DoubleTransitivity.Sec3.prop1
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.Sec4.prop1
import Submission.Work.DoubleTransitivity.Sec4.prop2
import Submission.Work.DoubleTransitivity.Sec5.Defs
import Submission.Work.DoubleTransitivity.Sec5.lemma1
import Submission.Work.DoubleTransitivity.Sec5.inductionStep
import Submission.Work.DoubleTransitivity.Sec6.Defs
import Submission.Work.DoubleTransitivity.Sec6.lemma1
import Submission.Work.DoubleTransitivity.Sec6.prop1
import Submission.Work.DoubleTransitivity.Sec6.prop2
import Submission.Work.DoubleTransitivity.Alg.exists_involution_conjugating
import Submission.Work.DoubleTransitivity.Sec7.Setup
import Submission.Work.DoubleTransitivity.Sec7.Sec4Aux
import Submission.Work.DoubleTransitivity.Sec7.ConjTransport
import Submission.Work.DoubleTransitivity.Sec7.sec6_final
import Submission.Work.DoubleTransitivity.Sec4.not_rp_twoTransitive
import Submission.Work.DoubleTransitivity.Sec4.lemma2_part1
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.S4Prop2.sec4_basic
import Submission.Work.ThreePoints.S4Prop2.ncard_involutions_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec7.ThmA`

Théorème A (Peterfalvi I, Ch. I, pp. 147–162): a finite group of `2`-rank `≥ 2` with a strongly
embedded subgroup `H` acts doubly transitively on the conjugates of `H`.

Strong induction on `|G|` (the induction hypothesis is the source's (A2), `ThmAForBelow`).  For
the step one chooses a prime divisor `p` of `n = |Inv H|`: if `𝓡_p = ∅`, Ch. I §4 Prop. 1
(`not_rp_twoTransitive`) gives the conclusion; otherwise the §6 argument (`sec6_final`) applies,
with the base change to a point of `Ω_P` handled by `ConjTransport`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.DoubleTransitivity.Sec7

/-- The induction step of Theorem A. -/
theorem ThmA_step {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (h4 : Submission.Blueprint.HasFourGroup G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (hInd : Work.DoubleTransitivity.ThmAForBelow (Nat.card G)) :
    Submission.Blueprint.IsTwoTransitiveOn H := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hodd : Odd (Submission.Blueprint.involutions (H : Set G)).ncard := inv_card_odd hH
  have hge2 : 2 ≤ (Submission.Blueprint.involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardInvGeTwo hH h4
  have hn1 : (Submission.Blueprint.involutions (H : Set G)).ncard ≠ 1 := by omega
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
  have hp2 : p ≠ 2 := by
    intro hp2
    rw [hp2] at hpdvd
    exact (odd_iff_not_two_dvd _).mp hodd hpdvd
  have h1 : Work.DoubleTransitivity.Sec4.Sec4Lemma2Part1 p H :=
    Work.DoubleTransitivity.Sec4.lemma2_part1 hBrSz hH hpp hp2
  by_cases hRp : Work.DoubleTransitivity.Sec4.Rp p H
  · -- ## The `𝓡_p ≠ ∅` case
    obtain ⟨P, hPmax, hTPS⟩ := rp_to_maxFixesThree hBrSz hH h4 hpp hp2 hRp
    have hpos : 0 < (Submission.Blueprint.fixedPts H P).ncard := by
      have h3 : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard := hPmax.2.1
      omega
    obtain ⟨ω, hω⟩ := (Set.ncard_pos).mp hpos
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ω
    have hPK : P ≤ MulAction.stabilizer G (QuotientGroup.mk x : G ⧸ H) :=
      Work.DoubleTransitivity.Sec4.mem_fixedPts_iff_le_stabilizer_aux.mp hω
    have hKse : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
        (MulAction.stabilizer G (QuotientGroup.mk x : G ⧸ H)) := by
      rw [Work.ThreePoints.stabilizer_mk]
      exact Work.ThreePoints.conj_stronglyEmbedded hH x
    have hPmaxK : Work.DoubleTransitivity.MaxFixesThree p
        (MulAction.stabilizer G (QuotientGroup.mk x : G ⧸ H)) P := by
      rw [Work.ThreePoints.stabilizer_mk]
      exact MaxFixesThree.conj x hPmax
    have hTPSK : Work.DoubleTransitivity.Sec4.TwoPointSylowData p
        (MulAction.stabilizer G (QuotientGroup.mk x : G ⧸ H)) P := by
      rw [Work.ThreePoints.stabilizer_mk]
      exact TwoPointSylowData.conj x hTPS
    have hpdvdK : p ∣ (Submission.Blueprint.involutions
        (MulAction.stabilizer G (QuotientGroup.mk x : G ⧸ H) : Set G)).ncard := by
      rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.S4Prop2.ncard_involutions_conj]
      exact hpdvd
    obtain ⟨u, hu, huN, hnc⟩ :=
      exists_involution_normalizer_noncent hBrSz hKse hpp hp2 hpdvdK hPmaxK hPK hTPSK
    have hres : Submission.Blueprint.IsTwoTransitiveOn (Submission.Blueprint.conj x H) := by
      have hh := sec6_final hFT hZJ hBrSz hKse h4 hInd hpp hp2 hPmaxK hPK hTPSK hu huN hnc
      rwa [Work.ThreePoints.stabilizer_mk] at hh
    exact conj_IsTwoTransitiveOn x hres
  · -- ## The `𝓡_p = ∅` case (Ch. I §4 Prop. 1)
    exact Work.DoubleTransitivity.Sec4.not_rp_twoTransitive hBrSz hH hpp hp2 h1 hRp

/-- **Théorème A** (Peterfalvi I, Ch. I, p. 157), in the form of `Submission.Blueprint.ThmAProp`. -/
theorem ThmA (hFT : Submission.Blueprint.FeitThompsonProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp) :
    Submission.Blueprint.ThmAProp := by
  intro G _ _ h4 H hH
  suffices h : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n →
      Submission.Blueprint.HasFourGroup G → ∀ H : Subgroup G,
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded H → Submission.Blueprint.IsTwoTransitiveOn H by
    exact h (Nat.card G) G rfl h4 H hH
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ hcard h4 H hH
    have hInd : Work.DoubleTransitivity.ThmAForBelow (Nat.card G) :=
      fun F _ _ hF h4F K hK =>
        ih (Nat.card F) (by rw [← hcard]; exact hF) F rfl h4F K hK
    exact ThmA_step hFT hZJ hBrSz h4 hH hInd

end Work.DoubleTransitivity.Sec7
