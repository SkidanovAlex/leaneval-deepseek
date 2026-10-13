/-
  WilE5 / Strat — the `k`-fold descendants of a state under the *profile* (level-indexed) test
  order.

  `SysL.levelP` builds the levels of the recursion by iterating `SysL.childrenP`, whose test order
  at a state `τ` is `Ml τ.B.length` (the profile evaluated at the state's own level).  This file
  introduces the iterate `descP X Ml NΦ σ k` of that children map (`k`-fold descendants of `σ`),
  the exact profile analogue of `Work.WilE5.Strat.desc` (which iterates the children map with a
  single global test bound).  The point is the same: a state appears at depth `k` of the global
  recursion exactly when it is a `k`-fold descendant of an initial state, which is what makes the
  covering induction (see `Strat/coverP.lean`) possible.
-/
import Mathlib
import Submission.Work.WilE5.SysL

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-- The `k`-fold children of a state `σ`, with the test-order profile `Ml` evaluated at each
state's own level (`τ.B.length`) — the iterate of `childrenP`. -/
def descP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q X.r) :
    ℕ → List (St p q X.r)
  | 0 => [σ]
  | (k + 1) => (descP X Ml NΦ σ k).flatMap fun τ => childrenP X.c Ml NΦ τ

theorem descP_zero {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q X.r) :
    descP X Ml NΦ σ 0 = [σ] := rfl

theorem descP_succ {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q X.r)
    (k : ℕ) :
    descP X Ml NΦ σ (k + 1)
      = (descP X Ml NΦ σ k).flatMap (fun τ => childrenP X.c Ml NΦ τ) := rfl

/-- Membership in the descendants at depth `k + 1`. -/
theorem mem_descP_succ {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) (k : ℕ) {τ : St p q X.r} :
    τ ∈ descP X Ml NΦ σ (k + 1) ↔
      ∃ ρ ∈ descP X Ml NΦ σ k, τ ∈ childrenP X.c Ml NΦ ρ := by
  rw [descP_succ, List.mem_flatMap]

/-- The descendants at depth one are the children. -/
theorem mem_descP_one {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) {τ : St p q X.r} :
    τ ∈ descP X Ml NΦ σ 1 ↔ τ ∈ childrenP X.c Ml NΦ σ := by
  rw [mem_descP_succ, descP_zero]
  constructor
  · rintro ⟨ρ, hρ, h⟩
    rw [List.mem_singleton] at hρ
    subst hρ
    exact h
  · intro h
    exact ⟨σ, List.mem_singleton.mpr rfl, h⟩

end Work.WilE5.Strat
