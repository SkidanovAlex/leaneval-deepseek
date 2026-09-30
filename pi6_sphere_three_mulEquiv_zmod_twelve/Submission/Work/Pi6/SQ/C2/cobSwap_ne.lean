import Mathlib
import Submission.Work.Pi6.SQ.C2.Cup2Setup
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `cobSwap` has no fixed points

`cobSwap` (defined in `Submission/Work/Pi6/SQM/Cup2CobSetup.lean`) is the pairing involution
of the disjoint union `LIdx ⊕ C3Idx ⊕ C4Idx ⊕ T1Idx ⊕ T2Idx`.  This file records that it is
fixed-point free, the index-level input to `Finset.sum_involution` in the proof of the
mod-2 `∪₂` coboundary formula.

The proof is a case analysis over the five summands and the branch structure of `cobSwap`.
In most branches the value of `cobSwap` lands in a *different* summand than the argument, so
the equality is impossible on shape (`simp_all` closes those).  In the remaining branches of
the `C3`/`C4` summands the value has the same shape, and the equality of the two indices
unfolds (via `Fin.ext_iff`) into `ℕ`-equalities which contradict the branch conditions, as
resolved by `omega`.
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ.C2

open Work.Pi6.SQM (F2)

noncomputable section

/-- `cobSwap` has no fixed points. -/
theorem cobSwap_ne (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Work.Pi6.SQ.C2.cobIdx n m) :
    Work.Pi6.SQ.C2.cobSwap n m hn hm x ≠ x := by
  intro h
  cases x with
  | inl i =>
      obtain ⟨k, a, b⟩ := i
      simp only [cobSwap] at h
      split_ifs at h <;> simp_all
  | inr y =>
      cases y with
      | inl i =>
          obtain ⟨A, B, j⟩ := i
          simp only [cobSwap] at h
          split_ifs at h <;> simp_all
          all_goals (simp only [Fin.ext_iff] at *; omega)
      | inr y =>
          cases y with
          | inl i =>
              obtain ⟨A, B, j⟩ := i
              simp only [cobSwap] at h
              split_ifs at h <;> simp_all
              all_goals (simp only [Fin.ext_iff] at *; omega)
          | inr y =>
              cases y with
              | inl s =>
                  simp only [cobSwap] at h
                  split_ifs at h <;> simp_all
              | inr s =>
                  simp only [cobSwap] at h
                  split_ifs at h <;> simp_all

end

end Work.Pi6.SQ.C2
