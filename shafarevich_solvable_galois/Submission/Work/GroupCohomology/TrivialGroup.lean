/-
Copyright (c) 2025. All rights reserved.

# Cohomology of the trivial group

For the trivial group (any group `G` with `Subsingleton G`), every `1`-cocycle is zero and every
`2`-cocycle is a coboundary, so `H¹(G, A) = H²(G, A) = 0` for every coefficient module `A`.
This is the `U = 1` vertex of Shapiro's lemma (`H^n(1, A) = 0` for `n ≥ 1`), in the additive
inhomogeneous setting.

## Main results

* `Work.GroupCohomology.Z1_eq_bot_of_subsingleton`
* `Work.GroupCohomology.Z2_le_B2_of_subsingleton`
* `Work.GroupCohomology.H1_subsingleton_of_subsingleton`,
  `Work.GroupCohomology.H2_subsingleton_of_subsingleton`
-/
import Submission.InducedModules
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- A `1`-cocycle of the trivial group is zero. -/
theorem Z1_eq_bot_of_subsingleton [Subsingleton G] : Z1 G A = ⊥ := by
  rw [AddSubgroup.eq_bot_iff_forall]
  intro f hf
  funext g
  rw [Subsingleton.elim g 1, Z1.map_one G A hf]
  rfl

/-- A `2`-cocycle of the trivial group is a coboundary (the constant cochain at `c (1,1)`). -/
theorem Z2_le_B2_of_subsingleton [Subsingleton G] : Z2 G A ≤ B2 G A := by
  intro c hc
  rw [mem_B2_iff]
  refine ⟨fun _ => c (1, 1), ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  rw [Subsingleton.elim g 1, Subsingleton.elim h 1, d1_apply]
  simp

/-- `H¹` of the trivial group vanishes. -/
theorem H1_subsingleton_of_subsingleton [Subsingleton G] : Subsingleton (H1 G A) :=
  Submission.subsingleton_H1_of_le (by rw [Z1_eq_bot_of_subsingleton]; exact bot_le)

/-- `H²` of the trivial group vanishes. -/
theorem H2_subsingleton_of_subsingleton [Subsingleton G] : Subsingleton (H2 G A) :=
  Submission.subsingleton_H2_of_le Z2_le_B2_of_subsingleton

end Work.GroupCohomology
