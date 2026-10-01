import Mathlib
import Submission.Work.ZeroFreeTables.XY.CosTayAbs
import Submission.Work.ZeroFreeTables.XY.SinTayAbs

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables.XY

/-- Lower bound for `Real.cos θ` from the Taylor bound `CosTayAbs`: if the `N`-th partial
Maclaurin sum shifted down by the Lagrange remainder dominates `lo`, then `lo ≤ cos θ`. -/
lemma cos_tay_ge (θ : ℝ) (N : ℕ) (lo : ℝ)
    (h : lo + |θ|^(2*N+2)/((2*N+2).factorial) ≤
      ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial)) :
    lo ≤ Real.cos θ := by
  have h1 := CosTayAbs θ N
  have h2 : -(|θ|^(2*N+2)/((2*N+2).factorial)) ≤ Real.cos θ -
      ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial) := (abs_le.mp h1).1
  linarith

/-- Upper bound for `Real.cos θ` from the Taylor bound `CosTayAbs`. -/
lemma cos_tay_le (θ : ℝ) (N : ℕ) (hi : ℝ)
    (h : (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial)) +
        |θ|^(2*N+2)/((2*N+2).factorial) ≤ hi) :
    Real.cos θ ≤ hi := by
  have h1 := CosTayAbs θ N
  have h2 : Real.cos θ - ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial) ≤
      |θ|^(2*N+2)/((2*N+2).factorial) := (abs_le.mp h1).2
  linarith

/-- Lower bound for `Real.sin θ` from the Taylor bound `SinTayAbs`. -/
lemma sin_tay_ge (θ : ℝ) (N : ℕ) (lo : ℝ)
    (h : lo + |θ|^(2*N+2)/((2*N+2).factorial) ≤
      ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial)) :
    lo ≤ Real.sin θ := by
  have h1 := SinTayAbs θ N
  have h2 : -(|θ|^(2*N+2)/((2*N+2).factorial)) ≤ Real.sin θ -
      ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial) := (abs_le.mp h1).1
  linarith

/-- Upper bound for `Real.sin θ` from the Taylor bound `SinTayAbs`. -/
lemma sin_tay_le (θ : ℝ) (N : ℕ) (hi : ℝ)
    (h : (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial)) +
        |θ|^(2*N+2)/((2*N+2).factorial) ≤ hi) :
    Real.sin θ ≤ hi := by
  have h1 := SinTayAbs θ N
  have h2 : Real.sin θ - ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial) ≤
      |θ|^(2*N+2)/((2*N+2).factorial) := (abs_le.mp h1).2
  linarith

/-- Rational enclosures (width `2·10⁻⁴`) of `cos θ`, `sin θ` at `θ = 3/2, 7/2, 5`, from the Taylor
bounds `CosTayAbs`/`SinTayAbs`. -/
theorem trig_low : (707362/10000000 : ℝ) ≤ Real.cos (3/2 : ℝ) ∧ Real.cos (3/2 : ℝ) ≤ (707383/10000000 : ℝ) ∧ (9974939/10000000 : ℝ) ≤ Real.sin (3/2 : ℝ) ∧ Real.sin (3/2 : ℝ) ≤ (498748/500000 : ℝ) ∧
  (-9365567/10000000 : ℝ) ≤ Real.cos (7/2 : ℝ) ∧ Real.cos (7/2 : ℝ) ≤ (-9363566/10000000 : ℝ) ∧ (-3508833/10000000 : ℝ) ≤ Real.sin (7/2 : ℝ) ∧ Real.sin (7/2 : ℝ) ≤ (-3506832/10000000 : ℝ) ∧
  (2835621/10000000 : ℝ) ≤ Real.cos (5 : ℝ) ∧ Real.cos (5 : ℝ) ≤ (2837622/10000000 : ℝ) ∧ (-9590243/10000000 : ℝ) ≤ Real.sin (5 : ℝ) ∧ Real.sin (5 : ℝ) ≤ (-9588242/10000000 : ℝ) := by
  refine ⟨cos_tay_ge (3/2) 6 _ (by norm_num [Finset.sum_range_succ]),
          cos_tay_le (3/2) 6 _ (by norm_num [Finset.sum_range_succ]),
          sin_tay_ge (3/2) 6 _ (by norm_num [Finset.sum_range_succ]),
          sin_tay_le (3/2) 6 _ (by norm_num [Finset.sum_range_succ]),
          cos_tay_ge (7/2) 7 _ (by norm_num [Finset.sum_range_succ]),
          cos_tay_le (7/2) 7 _ (by norm_num [Finset.sum_range_succ]),
          sin_tay_ge (7/2) 7 _ (by norm_num [Finset.sum_range_succ]),
          sin_tay_le (7/2) 7 _ (by norm_num [Finset.sum_range_succ]),
          cos_tay_ge (5) 9 _ (by norm_num [Finset.sum_range_succ]),
          cos_tay_le (5) 9 _ (by norm_num [Finset.sum_range_succ]),
          sin_tay_ge (5) 9 _ (by norm_num [Finset.sum_range_succ]),
          sin_tay_le (5) 9 _ (by norm_num [Finset.sum_range_succ])⟩

end Work.OffAxis.Tf72One
