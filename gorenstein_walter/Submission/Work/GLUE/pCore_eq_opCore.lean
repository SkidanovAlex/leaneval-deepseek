import Mathlib
import Submission.Work.GLUE.Defs

namespace Work.GLUE

/-- The join of the normal `p`-subgroups of `G` is the `p`-core `O_p(G)`, i.e. it agrees with
the intersection of all Sylow `p`-subgroups (Isaacs, Problem 1B.2). -/
theorem sSup_normal_isPGroup_eq_opCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] :
    sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}
      = OddOrder.Isaacs.Ch01.opCore p G := by
  refine le_antisymm (sSup_le ?_) (le_sSup ?_)
  · -- every normal `p`-subgroup is contained in `O_p(G)`
    rintro N ⟨hN, hpN⟩
    exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore (N := N) hpN
  · -- `O_p(G)` is itself a normal `p`-subgroup
    exact ⟨OddOrder.Isaacs.Ch01.opCore.normal p G,
      OddOrder.Isaacs.Ch01.opCore_isPGroup p G⟩

theorem pCore_eq_opCore {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.GW2.pCore p G = OddOrder.Isaacs.Ch01.opCore p G := by
  rw [Work.GW2.pCore, sSup_normal_isPGroup_eq_opCore]
  exact Subgroup.normalCore_eq_self _

end Work.GLUE
