import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.Prop2h2t
import Submission.Work.ThreePoints.ThmC.ch2_sec2_lem1_maxP3
import Submission.Work.ThreePoints.ThmC.ch2_sec2_lem1_partB
import Submission.Work.ThreePoints.ThmC.ch2_sec2_lem1_partC
import Submission.Work.ThreePoints.ThmC.ch2_sec2_lem1_partD

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

open LeanEval.GroupTheory.Defs

open Submission.Blueprint

/-- **Peterfalvi I Ch. II §2, first numbered item (p. 164).**  Let `H` be strongly embedded in the
finite group `G` (so `G` acts on `Ω = G ⧸ H`), `g ∉ H`, `D = twoPoint H g = H ∩ H^g`, and let `u` be an
involution of `H` (`u ∈ Inv(H)`) and `P` a `p`-Sylow (`p` odd) of `D ∩ D^u` normalised by `u`
(`D^u = conj u D`).  Then:

* `P` is maximal among the `p`-subgroups of `G` fixing at least three points of `Ω` (`IsMaxP3 H p P`);
* `M = N_G(P)` acts `2`-transitively on the set of fixed points of `P`, and for every fixed point
  `H₁ = conj g₁ H` of `P`, `M ∩ H₁` is a strongly embedded subgroup of `M`;
* if `M` has 2-rank `1`, then `P` is a `p`-Sylow of `D`;
* if `P` is not a `p`-Sylow of `P·C_D(P) = P ⊔ (C_G(P) ⊓ D)`, then `u` centralises `P`.

(`IsTwoTransitiveOn H` is the hypothesis of Theorem A; `BrauerSuzukiProp` and `FeitThompsonProp` are
consumed in the 2-rank-`1` case; `P ⊔ (C_G(P) ⊓ D)` equals `P C_G(P) ∩ D` because `P ≤ D`.)

Ingredients available in the workspace: `Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup`
(Ch. I §4 Prop. 2, which also gives `IsMaxP3`-type maximality), `Work.ThreePoints.app2_6_general`
(App. II (6)), `Work.ThreePoints.twoPoint_transitive_on_involutions`, and
`Work.ThreePoints.ThmC.ch1_sec6_cor1` (Ch. I §6 Cor. 1, proved in
`Submission/Work/ThreePoints/ThmC/ch1_sec6_cor1.lean`).  Part (c) needs Peterfalvi Appendix III (1),
stated as `Work.ThreePoints.ThmC.app3_1` in `Submission/Work/ThreePoints/ThmC/app3_1.lean` (being
proved in parallel; if that file does not exist yet, prove the needed 2-rank-1 input yourself). -/
theorem ch2_sec2_lem1 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (h2t : Submission.Blueprint.IsTwoTransitiveOn H)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    {g : G} (hg : g ∉ H) {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsSylowOf p P
      (Submission.Blueprint.twoPoint H g ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)))
    (huP : u ∈ Subgroup.normalizer (P : Set G)) :
    (Work.ThreePoints.ThmC.IsMaxP3 H p P) ∧
    (Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
      (Submission.Blueprint.fixedPts H P) ∧
      ∀ g₁ : G, P ≤ Submission.Blueprint.conj g₁ H →
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded
          ((Subgroup.normalizer (P : Set G) ⊓ Submission.Blueprint.conj g₁ H).subgroupOf
            (Subgroup.normalizer (P : Set G)))) ∧
    (¬ Submission.Blueprint.HasFourGroup (Subgroup.normalizer (P : Set G)) →
      Work.ThreePoints.ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H g)) ∧
    (¬ Work.ThreePoints.ThmC.IsSylowOf p P
        (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H g)) →
      ∀ x ∈ P, u * x = x * u) := by
  have hA : Work.ThreePoints.ThmC.IsMaxP3 H p P :=
    ch2_sec2_lem1_maxP3 hH h2t hBrSz hg hu hp hpodd hP huP
  have hB := ch2_sec2_lem1_partB hH h2t hBrSz hg hu hp hpodd hP huP hA
  exact ⟨hA, hB,
    ch2_sec2_lem1_partC hH h2t hBrSz hFT hg hu hp hpodd hP huP hA hB,
    ch2_sec2_lem1_partD hH h2t hBrSz hg hu hp hpodd hP huP hA hB⟩

end Work.ThreePoints.ThmC
