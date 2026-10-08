import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Action` — vocabulary for group actions

Peterfalvi I, Appendix II, is stated for a group `X` acting on a set `E`, with `H = X_a` the
stabiliser of a point and `D = X_a ∩ X_b` a two-point stabiliser.  Bisecting the action on `Ω`
(§3, §4) uses `N_G(P)` acting on the set `Ω_P` of fixed points of `P`, so the general setting
is unavoidable.

The present module provides:

* `fixedBySub P : Set E` — the fixed points of a subgroup `P`;
* `IsTransitiveOnSub`, `IsTwoTransitiveOnSub`, `IsRegularOnSub` — transitivity statements
  restricted to an invariant subset, phrased with explicit quantifiers (no instance plumbing);
* `IsSylowSub`, `IsSylowSubgroupOf` — Sylow subgroups of `X` and of a subgroup `H ≤ X`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.DoubleTransitivity

open Submission.Blueprint

variable {X E : Type} [Group X] [MulAction X E]

/-! ## Fixed points and transitivity on a subset -/

/-- The set of points of `E` fixed by the subgroup `P`. -/
def fixedBySub {E : Type*} [MulAction X E] (P : Subgroup X) : Set E :=
  {a | ∀ m ∈ P, m • a = a}

@[simp] theorem mem_fixedBySub {P : Subgroup X} {a : E} :
    a ∈ fixedBySub P ↔ ∀ m ∈ P, m • a = a := Iff.rfl

theorem fixedBySub_antitone {P Q : Subgroup X} (h : P ≤ Q) :
    (fixedBySub Q : Set E) ⊆ (fixedBySub P : Set E) :=
  fun a ha m hm => ha m (h hm)

/-- `a` is fixed by `P` iff `P` is contained in the stabiliser of `a`. -/
theorem fixedBySub_eq_setOf_stabilizer (P : Subgroup X) :
    (fixedBySub P : Set E) = {a : E | P ≤ MulAction.stabilizer X a} := by
  ext a
  exact Iff.rfl

/-- `Y` acts *transitively* on the set `S` (which it is expected to preserve). -/
def IsTransitiveOnSub (Y : Subgroup X) (S : Set E) : Prop :=
  ∀ c ∈ S, ∀ d ∈ S, ∃ y ∈ Y, y • c = d

/-- `Y` acts *2-transitively* on the set `S` (which it is expected to preserve). -/
def IsTwoTransitiveOnSub (Y : Subgroup X) (S : Set E) : Prop :=
  ∀ c ∈ S, ∀ d ∈ S, c ≠ d → ∀ c' ∈ S, ∀ d' ∈ S, c' ≠ d' →
    ∃ y ∈ Y, y • c = c' ∧ y • d = d'

/-- `Y` acts *regularly* (sharply transitively) on the set `S`. -/
def IsRegularOnSub (Y : Subgroup X) (S : Set E) : Prop :=
  IsTransitiveOnSub Y S ∧ ∀ y ∈ Y, (∀ s ∈ S, y • s = s) → y = 1

theorem IsTwoTransitiveOnSub.isTransitiveOnSub {Y : Subgroup X} {S : Set E}
    (h : IsTwoTransitiveOnSub Y S) : IsTransitiveOnSub Y S := by
  intro c hc d hd
  by_cases hcd : c = d
  · exact ⟨1, Y.one_mem, by rw [one_smul]; exact hcd⟩
  · obtain ⟨y, hy, hyc, _⟩ :=
      h c hc d hd hcd d hd c hc (fun hdc => hcd hdc.symm)
    exact ⟨y, hy, hyc⟩

/-! ## Sylow subgroups -/

/-- `Q` is a Sylow `p`-subgroup of `X`. -/
def IsSylowSub (p : ℕ) (Q : Subgroup X) : Prop := IsPGroup p Q ∧ ¬ p ∣ Q.index

/-- `Q` is a Sylow `p`-subgroup of the subgroup `H ≤ X`. -/
def IsSylowSubgroupOf (p : ℕ) (Q H : Subgroup X) : Prop :=
  Q ≤ H ∧ IsPGroup p Q ∧ ¬ p ∣ (Q.subgroupOf H).index

theorem IsSylowSubgroupOf.isPGroup {p : ℕ} {Q H : Subgroup X} (h : IsSylowSubgroupOf p Q H) :
    IsPGroup p Q := h.2.1

end Work.DoubleTransitivity
