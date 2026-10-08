import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.App1.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec4.Defs` — vocabulary for Peterfalvi I Ch. I §3–§4

Chapter I §3 studies `p`-subgroups maximal among those fixing at least three points of
`Ω = G ⧸ H`.  Chapter I §4 studies *`p`-regular intersections*: pairs `(D,H)` with
`D = H ∩ H'` for `H, H' ∈ Ω`, `H ≠ H'`, such that some `p`-Sylow `P` of `D` has `N_H(P)` of even
order (Peterfalvi I §4 Lemma 1 (c), taken here as the definition).

The module provides the vocabulary; the numbered results live in sibling modules.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.DoubleTransitivity

open Submission.Blueprint

variable {G : Type} [Group G]

/-- `X` fixes at least three points of `Ω = G ⧸ H` (`|Ω_X| ≥ 3`). -/
def FixesThree (H X : Subgroup G) : Prop := 3 ≤ (fixedPts H X).ncard

/-- `P` is maximal among the `p`-subgroups of `H` fixing at least three points of `Ω = G ⧸ H`
(Peterfalvi I Ch. I §3, §4). -/
def MaxFixesThreeIn (p : ℕ) (H P : Subgroup G) : Prop :=
  IsPGroup p P ∧ P ≤ H ∧ FixesThree H P ∧
    ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ H → FixesThree H Q → P ≤ Q → Q ≤ P

/-- `P` is maximal among the `p`-subgroups of `G` fixing at least three points of `Ω = G ⧸ H`. -/
def MaxFixesThree (p : ℕ) (H P : Subgroup G) : Prop :=
  IsPGroup p P ∧ FixesThree H P ∧
    ∀ Q : Subgroup G, IsPGroup p Q → FixesThree H Q → P ≤ Q → Q ≤ P

/-- `D` is a **`p`-regular intersection relative to `H`** (Peterfalvi I Ch. I §4): some `p`-Sylow
`P` of `D` has `N_H(P)` of even order (condition (c) of §4 Lemma 1). -/
def IsRegularIntersection (p : ℕ) (D H : Subgroup G) : Prop :=
  ∃ P : Subgroup G, IsSylowSubgroupOf p P D ∧
    Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ H))

/-- `D` has a `p`-Sylow with a `u`-invariant ... : condition (e) of Peterfalvi I §4 Lemma 1:
there are `u ∈ Inv(H)` and a `p`-subgroup `P ≤ D` normalised by `u` with
`|u^P| ≥ n_p`, where `n = |Inv(H)|`. -/
def HasInvariantSylowCondition (p : ℕ) (D H : Subgroup G) : Prop :=
  ∃ P : Subgroup G, IsSylowSubgroupOf p P D ∧
    ∃ u ∈ involutions (H : Set G), u ∈ Subgroup.normalizer (P : Set G) ∧
      (involutions (H : Set G)).ncard ≤ (conjOrbit P u).ncard

theorem FixesThree_iff (H X : Subgroup G) :
    FixesThree H X ↔ 3 ≤ (fixedPts H X).ncard := Iff.rfl

end Work.DoubleTransitivity
