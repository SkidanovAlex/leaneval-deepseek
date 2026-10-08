import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.lemma2a_factor_unique`

In the split rank-one situation `H = Q ⋊ D` with `D = H ∩ H^t` (`IsSplitRankOne H Q t`), every
element `m` of `H` has a *unique* factorisation `m = q · d` with `q ∈ Q` and `d ∈ D`.

Here `H = MulAction.stabilizer G (pt H)` and `D = MulAction.stabilizer G (pt H) ⊓
MulAction.stabilizer G (t • pt H)`, so the statement is the translation of the abstract
`Work.RankOneUniqueness.fact_exists` / `fact_unique` into the stabiliser vocabulary.

The proof is elementary: identify the two stabilisers with `H` and `H^t`, apply `fact_exists`
for the existence of a factorisation, and `fact_unique` (which uses `Q ⊓ D = ⊥`) for the
uniqueness of the `Q`-component.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint (conj twoPoint)

variable {G : Type} [Group G]

/-- The stabiliser of the base point `pt H = H` in `Ω = G ⧸ H` is exactly `H`. -/
lemma mem_stabilizer_pt_iff {H : Subgroup G} {g : G} :
    g ∈ MulAction.stabilizer G (Work.DoubleTransitivity.pt H) ↔ g ∈ H := by
  rw [MulAction.mem_stabilizer_iff, Work.DoubleTransitivity.smul_pt]
  exact Work.DoubleTransitivity.mk_one_eq_iff

/-- The stabiliser of the point `t • pt H = tH` is `H^t = conj t H`. -/
lemma mem_stabilizer_smul_pt_iff {H : Subgroup G} {t g : G} :
    g ∈ MulAction.stabilizer G (t • Work.DoubleTransitivity.pt H) ↔ g ∈ conj t H := by
  rw [MulAction.mem_stabilizer_iff, Work.DoubleTransitivity.smul_pt,
    ← Work.DoubleTransitivity.mem_conj_iff_smul_fixed]

/-- Membership in `D = H ∩ H^t`, read off the two stabilisers. -/
lemma mem_stabilizer_inf_iff {H : Subgroup G} {t g : G} :
    g ∈ MulAction.stabilizer G (Work.DoubleTransitivity.pt H) ⊓
        MulAction.stabilizer G (t • Work.DoubleTransitivity.pt H) ↔
      g ∈ twoPoint H t := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_stabilizer_pt_iff, mem_stabilizer_smul_pt_iff]

theorem lemma2a_factor_unique {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t) : ∀ m ∈ MulAction.stabilizer G (Work.DoubleTransitivity.pt H), ∃! q : Q, ∃ d ∈ MulAction.stabilizer G (Work.DoubleTransitivity.pt H) ⊓ MulAction.stabilizer G (t • Work.DoubleTransitivity.pt H), (q : G) * d = m := by
  intro m hm
  have hmH : m ∈ H := mem_stabilizer_pt_iff.mp hm
  obtain ⟨q, hqQ, d, hdD, hqd⟩ := Work.RankOneUniqueness.fact_exists h hmH
  have hdD' : d ∈ MulAction.stabilizer G (Work.DoubleTransitivity.pt H) ⊓
      MulAction.stabilizer G (t • Work.DoubleTransitivity.pt H) :=
    mem_stabilizer_inf_iff.mpr hdD
  refine ⟨⟨q, hqQ⟩, ⟨d, hdD', hqd.symm⟩, ?_⟩
  rintro ⟨q', hq'Q⟩ ⟨d', hd'D', hq'd'⟩
  have hd'D : d' ∈ twoPoint H t := mem_stabilizer_inf_iff.mp hd'D'
  obtain ⟨hqq, -⟩ := Work.RankOneUniqueness.fact_unique h hq'Q hqQ hd'D hdD
    (by rw [hq'd', hqd])
  exact Subtype.ext hqq

end Work.ThmF.ChV12
