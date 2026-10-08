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
# `Work.DoubleTransitivity.Sec5.Defs` — the induction hypothesis of Peterfalvi I §5

Theorem A is proved by strong induction on `|G|`.  Hypothesis (A2) of Peterfalvi I §5 (p.157) is
the statement of the theorem for all groups of smaller order; it is used at exactly one place
(Peterfalvi I §5 Prop. 1, p.158), applied to `N_G(A)/A`.

`ThmAForBelow n` is that induction hypothesis, phrased for groups in `Type` (the final assembly
`theoremA` performs the strong induction with `n = Nat.card G`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.DoubleTransitivity

open Submission.Blueprint

/-- Theorem A for every group of order `< n` (Peterfalvi I §5, hypothesis (A2)). -/
def ThmAForBelow (n : ℕ) : Prop :=
  ∀ (F : Type) [Group F] [Finite F], Nat.card F < n → HasFourGroup F →
    ∀ K : Subgroup F, IsStronglyEmbedded K → IsTwoTransitiveOn K

/-- Theorem A for every group of order `< n`, in the `IsBender` formulation (equivalent by
`isStronglyEmbedded_iff`). -/
theorem ThmAForBelow.iff_isBender {n : ℕ} (h : ThmAForBelow n) :
    ∀ (F : Type) [Group F] [Finite F], Nat.card F < n → HasFourGroup F →
      ∀ K : Subgroup F, K ≠ ⊤ → IsBender K → IsTwoTransitiveOn K := by
  intro F _ _ hF h4 K hK hBK
  exact h F hF h4 K ((isStronglyEmbedded_iff K).mpr ⟨hK, hBK⟩)

end Work.DoubleTransitivity
