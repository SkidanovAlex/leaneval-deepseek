import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A group whose derived subgroup lies in its centre is nilpotent

If `⁅G, G⁆ ≤ Z(G)` then the lower central series of `G` reaches `⊥` after two steps:
`γ₂(G) = ⁅G, G⁆ ≤ Z(G)` and `γ₃(G) = ⁅γ₂(G), G⁆ ≤ ⁅Z(G), G⁆ = ⊥`.
Hence `G` is nilpotent (of class at most two).

This is the elementary fact used when a group acts on a nilpotent section and one
wants to conclude nilpotency from centrality of the commutator (e.g. for the
Fitting subgroup of a group with `G/Z(G)` abelian).
-/

namespace Work.Fitting

theorem isNilpotent_of_commutator_le_center (G : Type*) [Group G]
    (h : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) : Group.IsNilpotent G := by
  rw [Subgroup.nilpotent_iff_lowerCentralSeries]
  refine ⟨2, ?_⟩
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
      Subgroup.lowerCentralSeries_zero]
  exact le_bot_iff.mp ((Subgroup.commutator_mono_left h).trans
    (le_of_eq (Subgroup.commutator_center_left (⊤ : Subgroup G))))

end Work.Fitting
