import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A0 — Skeleton: the minimal-counterexample framework for Feit–Thompson

This module starts Area A0 of the Feit–Thompson (odd order theorem) drive: the
*minimal counterexample* framework which every other area of the project sits above.

A `MinSimpleOdd G` is a finite group `G` of odd order which is simple, nonabelian, and
all of whose proper subgroups are solvable.  The reduction
`Work.Skeleton.feit_thompson_of_no_min` (in `Submission.Work.Skeleton.Reduction`) shows
that the odd order theorem follows from the non-existence of such a `G`.

## Main definitions

* `Work.Skeleton.MinSimpleOdd` — the minimal-counterexample hypothesis.

## Main results

* `Work.Skeleton.MinSimpleOdd.nontrivial`, `…not_isMulCommutative`, `…not_solvable`,
  `…normal_eq_bot_or_eq_top`, `…solvable_of_lt_top`, `…center_eq_bot` — elementary API
  of the hypothesis.
-/

namespace Work.Skeleton

/-- A **minimal counterexample** to the Feit–Thompson odd order theorem: a finite group
`G` of odd order which is simple, nonabelian, and all of whose proper subgroups are
solvable.  Feit–Thompson is the statement that no such `G` exists. -/
structure MinSimpleOdd (G : Type*) [Group G] [Finite G] : Prop where
  /-- `G` has odd order. -/
  odd : Odd (Nat.card G)
  /-- `G` is simple. -/
  simple : IsSimpleGroup G
  /-- `G` is not abelian. -/
  nonabelian : ∃ a b : G, a * b ≠ b * a
  /-- every proper subgroup of `G` is solvable. -/
  proper_solvable : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H

variable {G : Type*} [Group G] [Finite G]

/-- A minimal counterexample is nontrivial. -/
theorem MinSimpleOdd.nontrivial (h : MinSimpleOdd G) : Nontrivial G :=
  h.simple.toNontrivial

/-- A minimal counterexample is not commutative. -/
theorem MinSimpleOdd.not_isMulCommutative (h : MinSimpleOdd G) : ¬ IsMulCommutative G := by
  rintro ⟨hcomm⟩
  obtain ⟨a, b, hab⟩ := h.nonabelian
  exact hab (hcomm.comm a b)

/-- A minimal counterexample is not solvable. -/
theorem MinSimpleOdd.not_solvable (h : MinSimpleOdd G) : ¬ Group.IsSolvable G := by
  have : IsSimpleGroup G := h.simple
  intro hs
  refine h.not_isMulCommutative ⟨⟨fun a b => ?_⟩⟩
  exact (IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr hs a b

/-- Every normal subgroup of a minimal counterexample is trivial or the whole group. -/
theorem MinSimpleOdd.normal_eq_bot_or_eq_top (h : MinSimpleOdd G) (N : Subgroup G) [N.Normal] :
    N = ⊥ ∨ N = ⊤ := by
  have : IsSimpleGroup G := h.simple
  exact @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ N inferInstance

/-- A nontrivial normal subgroup of a minimal counterexample is the whole group. -/
theorem MinSimpleOdd.normal_eq_top_of_ne_bot (h : MinSimpleOdd G) {N : Subgroup G}
    [N.Normal] (hN : N ≠ ⊥) : N = ⊤ :=
  (h.normal_eq_bot_or_eq_top N).resolve_left hN

/-- Restatement of the defining property of a minimal counterexample: every proper
subgroup is solvable. -/
theorem MinSimpleOdd.solvable_of_lt_top (h : MinSimpleOdd G) {H : Subgroup G} (hH : H < ⊤) :
    Group.IsSolvable H :=
  h.proper_solvable H hH.ne

/-- A subgroup of a proper subgroup of a minimal counterexample is solvable. -/
theorem MinSimpleOdd.solvable_of_le_of_lt_top (h : MinSimpleOdd G) {H K : Subgroup G}
    (hH : H < ⊤) (hK : K ≤ H) : Group.IsSolvable K :=
  have : Group.IsSolvable H := h.solvable_of_lt_top hH
  Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hK)

/-- The center of a minimal counterexample is trivial. -/
theorem MinSimpleOdd.center_eq_bot (h : MinSimpleOdd G) : Subgroup.center G = ⊥ := by
  have : (Subgroup.center G).Normal := inferInstance
  rcases h.normal_eq_bot_or_eq_top (Subgroup.center G) with hc | hc
  · exact hc
  · exact absurd (Subgroup.center_eq_top_iff.mp hc) h.not_isMulCommutative

end Work.Skeleton
