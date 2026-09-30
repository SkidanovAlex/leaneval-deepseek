import Mathlib
import Submission.Work.Pi6.SQ.C2.Cup2Setup
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `cobSwap` is an involution

`cobSwap` (defined in `Submission/Work/Pi6/SQM/Cup2CobSetup.lean`) is the explicit
fixed-point-free pairing involution of the disjoint union
`LIdx ⊕ C3Idx ⊕ C4Idx ⊕ T1Idx ⊕ T2Idx` that underlies the classical "interval" proof of the
mod-2 `∪₂` coboundary formula

`δ(u ∪₂ v) = u ∪₁ v + v ∪₁ u + (δu) ∪₂ v + u ∪₂ (δv)`.

This file records that it is an involution, the second index-level input (beside
`Work.Pi6.SQ.C2.cobSwap_ne`) to `Finset.sum_involution`.

## Proof

The proof is a case analysis over the five summands of `cobIdx` and, inside each summand,
over the branch conditions of the `if`-chain of `cobSwap`.  On each summand the first
unfolded `cobSwap` is reduced (via `dif_pos`/`dif_neg` on the scrutinee) to an explicit
constructor of one of the five index families; `cobSwap` is then applied to that constructor,
its `if`-chain is split, and each leaf is closed either by matching the componentwise shape
of the two sides (`cobL_eq`, `cobC3_eq`, `cobC4_eq`, `cobT1_eq`, `cobT2_eq`) with `omega`
settling the arithmetic, or by the contradictoriness of the leaf's hypotheses (which happens
exactly in the degenerate cases `n = 1` or `m = 1`, where some of the index families are
empty).
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ.C2

open Work.Pi6.SQM (F2)

noncomputable section

/-- Arithmetic discharged in the leaves of the case analysis: unfold the `Fin` values and
settle the resulting linear arithmetic, or use a contradictory hypothesis. -/
syntax "cobArith" : tactic
macro_rules
  | `(tactic|cobArith) => `(tactic|
      first
      | omega
      | (simp only [Fin.val_mk] at *; omega)
      | (dsimp only at *; omega)
      | (simp only [Fin.val_mk] at *; simp)
      | (dsimp only at *; simp)
      | simp
      | contradiction
      | (exfalso; omega)
      | (exfalso; simp_all)
      | (exfalso; tauto))

/-- Close a leaf: compare the two sides of the equality componentwise (`cobL_eq` etc.), with
`cobArith` for the arithmetic; contradictory leaves are closed outright. -/
syntax "cobClose" : tactic
macro_rules
  | `(tactic|cobClose) => `(tactic|
      first
      | contradiction
      | (refine cobL_eq ?_ ?_ ?_ <;> cobArith)
      | (refine (cobL_eq ?_ ?_ ?_).symm <;> cobArith)
      | (refine cobC3_eq ?_ ?_ ?_ <;> cobArith)
      | (refine (cobC3_eq ?_ ?_ ?_).symm <;> cobArith)
      | (refine cobC4_eq ?_ ?_ ?_ <;> cobArith)
      | (refine (cobC4_eq ?_ ?_ ?_).symm <;> cobArith)
      | (refine cobT1_eq ?_ <;> cobArith)
      | (refine (cobT1_eq ?_).symm <;> cobArith)
      | (refine cobT2_eq ?_ <;> cobArith)
      | (refine (cobT2_eq ?_).symm <;> cobArith)
      | (exfalso; omega)
      | (exfalso; simp_all))

/-- After the scrutinee has been resolved, unfold the second `cobSwap`, split its `if`-chain
and close every leaf. -/
syntax "cobLeaf" : tactic
macro_rules
  | `(tactic|cobLeaf) => `(tactic| (simp only [cobSwap]; split_ifs <;> cobClose))

/-- `cobSwap` is an involution. -/
theorem cobSwap_involutive (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Function.Involutive (Work.Pi6.SQ.C2.cobSwap n m hn hm) := by
  intro x
  cases x with
  | inl i =>
      obtain ⟨k, a, b⟩ := i
      have hk := k.isLt; have ha := a.isLt; have hb := b.isLt
      simp only [cobSwap]
      by_cases h1 : k.val ≤ a.val
      · rw [dif_pos h1]; cobLeaf
      · rw [dif_neg h1]
        by_cases h2 : k.val ≤ a.val + (b.val + 1)
        · rw [dif_pos h2]; cobLeaf
        · rw [dif_neg h2]
          by_cases h3 : k.val ≤ n - 1 + (b.val + 1)
          · rw [dif_pos h3]; cobLeaf
          · rw [dif_neg h3]; cobLeaf
  | inr y =>
      cases y with
      | inl i =>
          obtain ⟨A, B, j⟩ := i
          have hA := A.isLt; have hB := B.isLt; have hj := j.isLt
          simp only [cobSwap]
          by_cases d1 : j.val + 1 ≤ A.val
          · rw [dif_pos d1]; cobLeaf
          · rw [dif_neg d1]
            by_cases d2 : A.val + 2 ≤ j.val ∧ j.val ≤ n
            · rw [dif_pos d2]; cobLeaf
            · rw [dif_neg d2]
              by_cases d3 : j.val = A.val
              · rw [dif_pos d3]
                by_cases d4 : 1 ≤ A.val
                · rw [dif_pos d4]; cobLeaf
                · rw [dif_neg d4]; cobLeaf
              · rw [dif_neg d3]
                by_cases d5 : j.val = A.val + 1
                · rw [dif_pos d5]
                  by_cases d6 : A.val + 2 ≤ n
                  · rw [dif_pos d6]; cobLeaf
                  · rw [dif_neg d6]
                    by_cases d7 : B.val + 3 ≤ m
                    · rw [dif_pos d7]; cobLeaf
                    · rw [dif_neg d7]; cobLeaf
                · rw [dif_neg d5]
                  by_cases d8 : A.val + 2 ≤ n
                  · rw [dif_pos d8]; cobLeaf
                  · rw [dif_neg d8]
                    by_cases d9 : 2 ≤ B.val + 1
                    · rw [dif_pos d9]; cobLeaf
                    · rw [dif_neg d9]
                      by_cases d10 : 2 ≤ n
                      · rw [dif_pos d10]; cobLeaf
                      · rw [dif_neg d10]; cobLeaf
      | inr y =>
          cases y with
          | inl i =>
              obtain ⟨A, B, j⟩ := i
              have hA := A.isLt; have hB := B.isLt; have hj := j.isLt
              simp only [cobSwap]
              by_cases e1 : 1 ≤ j.val ∧ j.val ≤ B.val
              · rw [dif_pos e1]; cobLeaf
              · rw [dif_neg e1]
                by_cases e2 : B.val + 3 ≤ j.val
                · rw [dif_pos e2]; cobLeaf
                · rw [dif_neg e2]
                  by_cases e3 : j.val = 0
                  · rw [dif_pos e3]
                    by_cases e4 : 2 ≤ B.val + 1
                    · rw [dif_pos e4]; cobLeaf
                    · rw [dif_neg e4]
                      by_cases e5 : A.val + 3 ≤ n
                      · rw [dif_pos e5]; cobLeaf
                      · rw [dif_neg e5]
                        by_cases e6 : 2 ≤ m
                        · rw [dif_pos e6]; cobLeaf
                        · rw [dif_neg e6]; cobLeaf
                  · rw [dif_neg e3]
                    by_cases e7 : j.val = B.val + 1
                    · rw [dif_pos e7]
                      by_cases e8 : 2 ≤ B.val + 1
                      · rw [dif_pos e8]; cobLeaf
                      · rw [dif_neg e8]
                        by_cases e9 : 1 ≤ A.val
                        · rw [dif_pos e9]; cobLeaf
                        · rw [dif_neg e9]; cobLeaf
                    · rw [dif_neg e7]
                      by_cases e11 : B.val + 1 ≤ m - 1
                      · rw [dif_pos e11]; cobLeaf
                      · rw [dif_neg e11]; cobLeaf
          | inr y =>
              cases y with
              | inl s =>
                  have hs := s.isLt
                  simp only [cobSwap]
                  by_cases f1 : s.val + 2 ≤ n
                  · rw [dif_pos f1]; cobLeaf
                  · rw [dif_neg f1]
                    by_cases f2 : 2 ≤ m
                    · rw [dif_pos f2]; cobLeaf
                    · rw [dif_neg f2]
                      by_cases f3 : 2 ≤ n
                      · rw [dif_pos f3]; cobLeaf
                      · rw [dif_neg f3]; cobLeaf
              | inr s =>
                  have hs := s.isLt
                  simp only [cobSwap]
                  by_cases g1 : 1 ≤ s.val
                  · rw [dif_pos g1]; cobLeaf
                  · rw [dif_neg g1]
                    by_cases g2 : 2 ≤ n
                    · rw [dif_pos g2]; cobLeaf
                    · rw [dif_neg g2]
                      by_cases g3 : 2 ≤ m
                      · rw [dif_pos g3]; cobLeaf
                      · rw [dif_neg g3]; cobLeaf

end

end Work.Pi6.SQ.C2
