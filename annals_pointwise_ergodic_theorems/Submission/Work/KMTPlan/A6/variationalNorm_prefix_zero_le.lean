import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs

/-!
# Prefix-zero padding multiplies the variational norm by at most `2`

For a sequence `z : ℕ → ℂ` and `m : ℕ`, let `a` be the sequence obtained by putting `m` zeros in
front of `z` (i.e. `a n = 0` for `n < m` and `a n = z (n - m)` otherwise).  This file proves

  `‖a‖_{V^r} ≤ 2 ‖z‖_{V^r}`   for `r ≥ 1`.

The constant `2` is optimal (take `z` constant and nonzero, `m ≥ 1`).

The proof writes `a = (n ↦ z (n - m)) + -(n ↦ if n < m then z 0 else 0)` and splits the variational
norm into its two defining pieces `variationalNorm_eq_add`:

* the sup term `⨆ n ‖a n‖ₑ` equals `⨆ n ‖z n‖ₑ` exactly (the padded sequence takes precisely the
  values of `z`, plus the value `0`);
* the variation term is subadditive, the shifted sequence has variation at most that of `z`
  (the chain `N ↦ N i - m` is monotone), and the "left step" `n ↦ if n < m then z 0 else 0` has
  variation at most `‖z 0‖ₑ ≤ ‖z‖_{V^r}` (`varPart_step_le`).

Hence `‖a‖_{V^r} ≤ ‖z‖_{V^r} + ‖z 0‖ₑ ≤ 2 ‖z‖_{V^r}`.
-/

namespace Work.KMTPlan.A6

open scoped ENNReal NNReal

theorem variationalNorm_prefix_zero_le (r : NNReal) (hr : 1 ≤ r) (z : ℕ → ℂ) (m : ℕ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if n < m then (0 : ℂ) else z (n - m))
      ≤ 2 * PointwiseErgodicTheorems.variationalNorm r z := by
  have hsup : (⨆ n, ‖(fun n : ℕ => if n < m then (0 : ℂ) else z (n - m)) n‖ₑ)
      = (⨆ n, ‖z n‖ₑ) := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun n => ?_
      by_cases h : n < m
      · simp [h]
      · simp only [h, if_false]
        exact le_iSup (fun n => ‖z n‖ₑ) (n - m)
    · refine iSup_le fun n => ?_
      have h1 : ‖z n‖ₑ = ‖(fun k : ℕ => if k < m then (0 : ℂ) else z (k - m)) (n + m)‖ₑ := by
        congr 1
        simp [Nat.not_lt.mpr (Nat.le_add_left m n)]
      rw [h1]
      exact le_iSup (fun k => ‖(fun j : ℕ => if j < m then (0 : ℂ) else z (j - m)) k‖ₑ) (n + m)
  have hvar_shift : Submission.PointwiseErgodicTheorems.varPart r (fun n => z (n - m))
      ≤ Submission.PointwiseErgodicTheorems.varPart r z := by
    refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    refine le_iSup_of_le J (le_iSup_of_le (fun i => N i - m) (le_iSup_of_le ?_ le_rfl))
    exact monotone_nat_of_le_succ fun i => Nat.sub_le_sub_right (hN (Nat.le_succ i)) m
  have hneg : Submission.PointwiseErgodicTheorems.varPart r (-(fun n => if n < m then z 0 else 0))
      = Submission.PointwiseErgodicTheorems.varPart r (fun n => if n < m then z 0 else 0) := by
    have h := Submission.PointwiseErgodicTheorems.varPart_smul (r := r) hr (-1 : ℂ)
      (fun n => if n < m then z 0 else 0)
    have hneg1 : (-(fun n => if n < m then z 0 else 0))
        = (-1 : ℂ) • (fun n => if n < m then z 0 else 0) := by
      funext n
      by_cases h' : n < m <;> simp [h']
    rw [hneg1, h]
    norm_num
  have hvar : Submission.PointwiseErgodicTheorems.varPart r
        (fun n : ℕ => if n < m then (0 : ℂ) else z (n - m))
      ≤ Submission.PointwiseErgodicTheorems.varPart r z + ‖z 0‖ₑ := by
    have hde : (fun n : ℕ => if n < m then (0 : ℂ) else z (n - m))
        = (fun n => z (n - m)) + (-(fun n => if n < m then z 0 else 0)) := by
      funext n
      rw [Pi.add_apply, Pi.neg_apply]
      by_cases h : n < m
      · simp [h, Nat.sub_eq_zero_of_le h.le]
      · simp [h]
    rw [hde]
    calc Submission.PointwiseErgodicTheorems.varPart r
            ((fun n => z (n - m)) + -(fun n => if n < m then z 0 else 0))
        ≤ Submission.PointwiseErgodicTheorems.varPart r (fun n => z (n - m))
            + Submission.PointwiseErgodicTheorems.varPart r
                (-(fun n => if n < m then z 0 else 0)) :=
          Submission.PointwiseErgodicTheorems.varPart_add_le hr _ _
      _ = Submission.PointwiseErgodicTheorems.varPart r (fun n => z (n - m))
            + Submission.PointwiseErgodicTheorems.varPart r (fun n => if n < m then z 0 else 0) := by
          rw [hneg]
      _ ≤ Submission.PointwiseErgodicTheorems.varPart r z + ‖z 0‖ₑ :=
          add_le_add hvar_shift (Submission.PointwiseErgodicTheorems.varPart_step_le hr m (z 0))
  calc PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if n < m then (0 : ℂ) else z (n - m))
      = (⨆ n, ‖(fun n : ℕ => if n < m then (0 : ℂ) else z (n - m)) n‖ₑ)
          + Submission.PointwiseErgodicTheorems.varPart r
              (fun n : ℕ => if n < m then (0 : ℂ) else z (n - m)) :=
        Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r _
    _ ≤ (⨆ n, ‖z n‖ₑ) + (Submission.PointwiseErgodicTheorems.varPart r z + ‖z 0‖ₑ) :=
        add_le_add (le_of_eq hsup) hvar
    _ ≤ (⨆ n, ‖z n‖ₑ) + (Submission.PointwiseErgodicTheorems.varPart r z
          + PointwiseErgodicTheorems.variationalNorm r z) :=
        add_le_add le_rfl
          (add_le_add le_rfl (Submission.PointwiseErgodicTheorems.le_variationalNorm r z 0))
    _ = 2 * PointwiseErgodicTheorems.variationalNorm r z := by
        rw [two_mul, Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r z]
        ac_rfl

end Work.KMTPlan.A6
