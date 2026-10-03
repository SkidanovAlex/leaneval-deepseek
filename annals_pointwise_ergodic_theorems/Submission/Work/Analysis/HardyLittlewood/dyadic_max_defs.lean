import Mathlib
import Submission.Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded_large
import Submission.Commons.Analysis.HardyLittlewood.discrete_maximal_lp
import Submission.Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf
import Submission.Commons.Analysis.Hilbert.radial_kernel_tsum_le_maximal
import Submission.Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert
import Submission.Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
import Submission.Work.Analysis.Probability.exists_level_of_Vpath_gt

/-!
# Shifted dyadic blocks and dyadic maximal functions on `ℤ`

This file isolates the combinatorial objects used to reduce the *interval* Hardy--Littlewood
maximal function `Commons.Analysis.Hilbert.dMax` on `ℤ` to two *dyadic* (martingale) maximal
functions.

For `ε : Bool` (`false` = grid `0`, `true` = grid `1`) and scale `m : ℕ`:

* grid `0` is the partition of `ℤ` into the blocks `[2^m k, 2^m (k+1) - 1]`;
* grid `1` is the partition of `ℤ` into the blocks `[2^(m-1) + 2^m k, 2^(m-1) + 2^m (k+1) - 1]`

(`2^(m-1)` is interpreted as `2^0 = 1` for `m = 0`).  The function `blk ε m x` is the left
endpoint of the block of scale `m` (grid `ε`) that contains `x`, and `dyadMax ε g x` is the
corresponding dyadic maximal function of `g : ℤ → ℂ`.

The two deterministic lemmas `blk_le_self` and `self_lt_blk_add` record that `x` lies in its own
block.
-/

namespace Work.Analysis.HardyLittlewood

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The left endpoint of the dyadic block of scale `m` in grid `ε` containing `x`. -/
def blk (ε : Bool) (m : ℕ) (x : ℤ) : ℤ :=
  (if ε then (2 : ℤ) ^ (m - 1) else 0) +
    (2 : ℤ) ^ m * ((x - (if ε then (2 : ℤ) ^ (m - 1) else 0)) / (2 : ℤ) ^ m)

/-- The dyadic maximal function of grid `ε`: the supremum, over the scales `m`, of the average
of `‖g‖` over the block of scale `m` in grid `ε` containing `x`. -/
def dyadMax (ε : Bool) (g : ℤ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  ⨆ m : ℕ, (((2 : ℕ) ^ m : ℝ≥0∞))⁻¹ *
    ∑ k ∈ Finset.Icc (blk ε m x) (blk ε m x + (2 : ℤ) ^ m - 1), ‖g k‖ₑ

/-- The left endpoint of the block containing `x` does not exceed `x`. -/
lemma blk_le_self (ε : Bool) (m : ℕ) (x : ℤ) : blk ε m x ≤ x := by
  unfold blk
  have hpos : (0 : ℤ) < (2 : ℤ) ^ m := by positivity
  have h := Int.ediv_mul_le (x - (if ε then (2 : ℤ) ^ (m - 1) else 0)) (ne_of_gt hpos)
  rw [mul_comm] at h
  linarith

/-- `x` is smaller than the right endpoint of its own block. -/
lemma self_lt_blk_add (ε : Bool) (m : ℕ) (x : ℤ) : x < blk ε m x + (2 : ℤ) ^ m := by
  unfold blk
  have hpos : (0 : ℤ) < (2 : ℤ) ^ m := by positivity
  have h : (x - (if ε then (2 : ℤ) ^ (m - 1) else 0)) % (2 : ℤ) ^ m < (2 : ℤ) ^ m :=
    Int.emod_lt_of_pos _ hpos
  have h2 : (2 : ℤ) ^ m * ((x - (if ε then (2 : ℤ) ^ (m - 1) else 0)) / (2 : ℤ) ^ m)
      + (x - (if ε then (2 : ℤ) ^ (m - 1) else 0)) % (2 : ℤ) ^ m
      = x - (if ε then (2 : ℤ) ^ (m - 1) else 0) :=
    Int.mul_ediv_add_emod _ _
  linarith

/-- The average of `‖g‖` over the block of grid `ε` and scale `m` containing `x` is at most
`dyadMax ε g x`. -/
lemma le_dyadMax_block (ε : Bool) (g : ℤ → ℂ) (m : ℕ) (x : ℤ) :
    (((2 : ℕ) ^ m : ℝ≥0∞))⁻¹ *
        ∑ k ∈ Finset.Icc (blk ε m x) (blk ε m x + (2 : ℤ) ^ m - 1), ‖g k‖ₑ
      ≤ dyadMax ε g x := by
  unfold dyadMax
  exact le_iSup (fun m : ℕ => (((2 : ℕ) ^ m : ℝ≥0∞))⁻¹ *
    ∑ k ∈ Finset.Icc (blk ε m x) (blk ε m x + (2 : ℤ) ^ m - 1), ‖g k‖ₑ) m


/-- The interval Hardy--Littlewood maximal function of an `ℝ≥0∞`-valued weight (the same formula
as `Commons.Analysis.Hilbert.dMax`, with `‖·‖ₑ` replaced by the identity). -/
def dMaxENN (w : ℤ → ℝ≥0∞) (m : ℤ) : ℝ≥0∞ :=
  ⨆ (p : {p : ℤ × ℤ // p.1 ≤ m ∧ m ≤ p.2}),
    ((p.1.2 - p.1.1 + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc p.1.1 p.1.2, w k

lemma le_dMaxENN_of_interval (w : ℤ → ℝ≥0∞) (m : ℤ) {a b : ℤ} (hab : a ≤ m ∧ m ≤ b) :
    ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, w k ≤ dMaxENN w m := by
  unfold dMaxENN
  exact le_iSup (fun p : {p : ℤ × ℤ // p.1 ≤ m ∧ m ≤ p.2} =>
    ((p.1.2 - p.1.1 + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc p.1.1 p.1.2, w k) ⟨(a, b), hab⟩

end

end Work.Analysis.HardyLittlewood
