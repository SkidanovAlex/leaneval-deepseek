import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.lemma2a
import Submission.Work.ThmF.ChV12.lemma2a_Q_regular
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.ChV3.step6aux_count
import Submission.Work.PSU3.StageA.coarseFrame_defs
import Submission.Work.DoubleTransitivity.App2.app2_7
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3.StageA

/-- In the split rank-one datum `H = Q ⋊ D` of `PSU3Hyp H Q t` (`D = H ⊓ Hᵗ`), for a nontrivial
`P ≤ V = centD H t` the fixed points of `P` on `Ω = G ⧸ H` are `H` together with the regular
`C_Q(P)`-orbit of `Hᵗ`; consequently `|C_G(P)| = |C_H(P)| · |fixedPts H P|` and this index is odd. -/
theorem fixedPts_card_and_centralizer_index {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPne : P ≠ ⊥) :
    (Submission.Blueprint.fixedPts H P).ncard =
        Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) + 1 ∧
      Nat.card ↥(Subgroup.centralizer (P : Set G)) =
        Nat.card ↥(H ⊓ Subgroup.centralizer (P : Set G)) *
          (Submission.Blueprint.fixedPts H P).ncard ∧
      Odd ((Submission.Blueprint.fixedPts H P).ncard) := by
  classical
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hcard1 : (fixedPts H P).ncard =
      Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) + 1 :=
    Work.ThmF.ChV3.ncard_fixedPts_eq_card_inf_centralizer hsplit hPV
  refine ⟨hcard1, ?_, ?_⟩
  · set C : Subgroup G := Subgroup.centralizer (P : Set G) with hCdef
    set M : Subgroup ↥C := (H ⊓ C).subgroupOf C with hMdef
    letI : MulAction ↥C (G ⧸ H) :=
      { smul := fun c x => (c : G) • x
        one_smul := fun x => by simp
        mul_smul := fun a b x => by simp [mul_smul] }
    have horb : (MulAction.orbit ↥C (Work.RankOneUniqueness.pt H) : Set (G ⧸ H)) =
        (fixedPts H P : Set (G ⧸ H)) := by
      ext ω
      constructor
      · rintro ⟨c, rfl⟩
        rw [Work.ThreePoints.mem_fixedPts]
        intro x hx
        have hcx : x * (c : G) = (c : G) * x := Subgroup.mem_centralizer_iff.mp c.2 x hx
        have hxH : x ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hPV hx)).1).1
        have hxpt : x • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
          rw [← MulAction.mem_stabilizer_iff, Work.ThmF.ChV12.stabilizer_one]
          exact hxH
        calc x • ((c : G) • ((1 : G) : G ⧸ H))
            = (x * (c : G)) • ((1 : G) : G ⧸ H) := (mul_smul x (c : G) _).symm
          _ = ((c : G) * x) • ((1 : G) : G ⧸ H) := by rw [hcx]
          _ = (c : G) • (x • ((1 : G) : G ⧸ H)) := mul_smul (c : G) x _
          _ = (c : G) • ((1 : G) : G ⧸ H) := by rw [hxpt]
      · intro hω
        obtain ⟨c, hc⟩ := Work.ThmF.ChV12.centralizer_transitive_fixedPts hsplit hPV ω hω
        exact ⟨c, hc⟩
    have hmems : ∀ c : ↥C, (c : G) ∈ MulAction.stabilizer G ((1 : G) : G ⧸ H) ↔
        (c : G) ∈ H := by
      intro c
      rw [Work.ThmF.ChV12.stabilizer_one H]
    have hstab : MulAction.stabilizer ↥C (Work.RankOneUniqueness.pt H) = M := by
      ext c
      rw [MulAction.mem_stabilizer_iff, hMdef, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        refine ⟨?_, c.2⟩
        have h1 : (c : G) ∈ MulAction.stabilizer G (Work.RankOneUniqueness.pt H) :=
          MulAction.mem_stabilizer_iff.mpr h
        have h2 : (c : G) ∈ MulAction.stabilizer G ((1 : G) : G ⧸ H) := by
          simpa [Work.RankOneUniqueness.pt] using h1
        exact (hmems c).mp h2
      · rintro ⟨hcH, -⟩
        have h2 : (c : G) ∈ MulAction.stabilizer G ((1 : G) : G ⧸ H) := (hmems c).mpr hcH
        have h1 : (c : G) ∈ MulAction.stabilizer G (Work.RankOneUniqueness.pt H) := by
          simpa [Work.RankOneUniqueness.pt] using h2
        exact MulAction.mem_stabilizer_iff.mp h1
    have horbcard : Nat.card ↥(MulAction.orbit ↥C (Work.RankOneUniqueness.pt H)) =
        (fixedPts H P).ncard := by
      have : (MulAction.orbit ↥C (Work.RankOneUniqueness.pt H)).ncard =
          (fixedPts H P).ncard := by rw [horb]
      simpa using this
    have hstabcard : Nat.card ↥(MulAction.stabilizer ↥C (Work.RankOneUniqueness.pt H)) =
        Nat.card ↥(H ⊓ C) := by
      rw [hstab, hMdef]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hidx : (MulAction.stabilizer ↥C (Work.RankOneUniqueness.pt H)).index =
        (fixedPts H P).ncard := by
      rw [Subgroup.index_eq_card,
        (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥C
          (Work.RankOneUniqueness.pt H))).symm]
      exact horbcard
    have hmain : Nat.card ↥C = Nat.card ↥(MulAction.stabilizer ↥C
        (Work.RankOneUniqueness.pt H)) *
        (MulAction.stabilizer ↥C (Work.RankOneUniqueness.pt H)).index :=
      (Subgroup.card_mul_index (MulAction.stabilizer ↥C (Work.RankOneUniqueness.pt H))).symm
    rw [hstabcard, hidx] at hmain
    exact hmain
  · have h3 : 3 ≤ (fixedPts H P).ncard :=
      le_trans (Work.ThreePoints.three_le_ncard_fixedPts_centD hsplit.stronglyEmbedded
        hsplit.invol hsplit.not_mem)
        (Set.ncard_le_ncard (Work.ThreePoints.fixedPts_mono hPV))
    have hQCP : IsPGroup 2 ↥(Q ⊓ Subgroup.centralizer (P : Set G)) :=
      hS.two.to_le inf_le_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQCP
    have hk2 : 2 ≤ 2 ^ k := by
      rw [← hk]
      omega
    have hk1 : 1 ≤ k := by
      by_contra hc
      have h0 : k = 0 := by omega
      rw [h0] at hk2
      norm_num at hk2
    rw [hcard1, hk]
    refine ⟨2 ^ (k - 1), ?_⟩
    have hexp : 2 ^ k = 2 ^ (k - 1) * 2 := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ]
    rw [hexp]
    ring

end Work.PSU3.StageA
