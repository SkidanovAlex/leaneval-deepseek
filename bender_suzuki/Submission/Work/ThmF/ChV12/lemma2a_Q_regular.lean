import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.stabilizer_transitive_on_complement
import Submission.Work.RankOneUniqueness.qPt_surjective
import Submission.Work.RankOneUniqueness.qPt_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- **`Q` is regular on `Ω ∖ {∞}`** (Peterfalvi II, Ch. VII §1; the `Q`-half of the split
rank-one Bruhat decomposition).

The map `x ↦ qPt H t x = x • (t • ∞)`, `Q → Ω ∖ {∞}`, is a bijection
(`RankOneUniqueness.qPt_surjective`, `RankOneUniqueness.qPt_injective`):
`H` is transitive on `Ω ∖ {∞}` by two-transitivity, so every point of `Ω ∖ {∞}` is some
`q • (t • ∞)` with `q ∈ Q`, and `x t H = y t H` together with `Q ∩ D = 1` forces `x = y`.
Hence `Q` is sharply transitive on `Ω ∖ {∞}` — with no use of the cardinality hypothesis
`hcard`, which is in fact a *consequence* of `IsSplitRankOne` (`lemma2a_card_omega`). -/
theorem lemma2a_Q_regular {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t) (hcard : Nat.card (Work.DoubleTransitivity.Omega H) = Nat.card Q + 1) : Work.DoubleTransitivity.IsRegularOnSub Q ({Work.DoubleTransitivity.pt H}ᶜ : Set (Work.DoubleTransitivity.Omega H)) := by
  have _ := hcard
  constructor
  · -- transitivity: every point of `Ω ∖ {∞}` is `q • (t • ∞)` for some `q ∈ Q`
    intro c hc d hd
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc hd
    obtain ⟨x, hx, hxc⟩ := Work.RankOneUniqueness.qPt_surjective h hc
    obtain ⟨y, hy, hyd⟩ := Work.RankOneUniqueness.qPt_surjective h hd
    refine ⟨y * x⁻¹, Q.mul_mem hy (Q.inv_mem hx), ?_⟩
    rw [← hxc, ← hyd, Work.RankOneUniqueness.qPt_eq_smul H t x,
      Work.RankOneUniqueness.qPt_eq_smul H t y, mul_smul, inv_smul_smul]
  · -- freeness: only `1 ∈ Q` fixes `t • ∞`
    intro y hy hfix
    have hmem : t • Work.RankOneUniqueness.pt H ∈
        ({Work.DoubleTransitivity.pt H}ᶜ : Set (Work.DoubleTransitivity.Omega H)) := by
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact Work.RankOneUniqueness.t_smul_pt_ne h
    have h1 : y • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H :=
      hfix _ hmem
    refine Work.RankOneUniqueness.qPt_injective h hy Q.one_mem ?_
    rw [Work.RankOneUniqueness.qPt_eq_smul H t y, Work.RankOneUniqueness.qPt_eq_smul H t (1 : G),
      one_smul]
    exact h1

end Work.ThmF.ChV12
