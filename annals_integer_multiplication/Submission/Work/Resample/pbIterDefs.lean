import Mathlib
import Submission.Work.Resample.pbRoundDefs

/-!
# `Work.Resample.pbIterTight`: shared definitions

The D-fold iteration of `Work.Resample.pbRound` has cost `Kc * Σ_{j<D} PBBracket j`; in the
statement of `Work.Resample.pbIterTight` the sum is evaluated with the global estimates
`(ss.take j).prod * (ts.drop (j+1)).prod * (t_j + 1) ≤ ts.prod` and `Σ_j (t_j + 1) ≤ ts.sum + D`
(so that `ss` disappears), which is the bracket `PBTight` below.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-- The cost bracket of `Work.Resample.pbIterTight` (the B̃ half of Theorem 4.1): `D` times the
per-round bracket with `(ss.take j).prod * (ts.drop (j+1)).prod * (t_j + 1)` bounded by `ts.prod`. -/
def PBTight (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) : ℕ :=
    HvdH.D * (Kb * (ts.sum + 1) * (p + 1) ^ Kb)
  + 4 * HvdH.D * ts.prod *
      (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) + Kb * (p + 1) ^ 2)
  + 4 * HvdH.D * ts.prod *
      ((2 * p + 8) + (ts.prod * 2 ^ (p + 1)).size + 1) * ((ts.prod * 2 ^ (p + 1)).size + 1)
  + HvdH.D * (32 * (ts.prod * (2 * p + 8) + 2))
  + HvdH.D * (800 * (HvdH.D * (p + 1)))
  + HvdH.D * ((2 * Work.Resample.PBTab Kb p ts + 5) * (2 * Work.Resample.PBTab Kb p ts + 5))
  + HvdH.D * 100

/-- The running total of the per-round brackets of `pbRound`, starting at round `m`. -/
def PBSum (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (m n : ℕ) : ℕ :=
  (Finset.range n).sum (fun i => PBBracket Kb Cm p α ss ts (m + i))

/-- Split off the **last** term of a `PBSum`. -/
theorem PBSum_last (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (m n : ℕ) :
    PBSum Kb Cm p α ss ts m (n + 1) =
      PBSum Kb Cm p α ss ts m n + PBBracket Kb Cm p α ss ts (m + n) := by
  simp only [PBSum, Finset.sum_range_succ]

/-- Split off the **first** term of a `PBSum`. -/
theorem PBSum_succ (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (m n : ℕ) :
    PBSum Kb Cm p α ss ts m (n + 1) =
      PBBracket Kb Cm p α ss ts m + PBSum Kb Cm p α ss ts (m + 1) n := by
  unfold PBSum
  rw [Finset.sum_range_succ']
  have h1 : (Finset.range n).sum (fun i => PBBracket Kb Cm p α ss ts (m + (i + 1)))
      = (Finset.range n).sum (fun i => PBBracket Kb Cm p α ss ts (m + 1 + i)) :=
    Finset.sum_congr rfl (fun i _ => by
      rw [show m + (i + 1) = m + 1 + i by omega])
  have h2 : PBBracket Kb Cm p α ss ts (m + 0) = PBBracket Kb Cm p α ss ts m := rfl
  rw [h1, h2]
  exact Nat.add_comm _ _

theorem PBSum_zero (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (m : ℕ) :
    PBSum Kb Cm p α ss ts m 0 = 0 := rfl

theorem PBSum_one (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (m : ℕ) :
    PBSum Kb Cm p α ss ts m 1 = PBBracket Kb Cm p α ss ts m := by
  unfold PBSum
  rw [Finset.sum_range_one]
  rfl

/-- `PBSum` from index `0` is the plain sum of the brackets. -/
theorem PBSum_zero_sum (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (n : ℕ) :
    PBSum Kb Cm p α ss ts 0 n = (Finset.range n).sum (fun i => PBBracket Kb Cm p α ss ts i) := by
  unfold PBSum
  exact Finset.sum_congr rfl (fun i _ => by rw [Nat.zero_add])

end Work.Resample
