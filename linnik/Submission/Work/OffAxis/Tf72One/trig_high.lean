import Mathlib
import Submission.Work.ZeroFreeTables.XY.CosTayAbs
import Submission.Work.ZeroFreeTables.XY.SinTayAbs

namespace Work.OffAxis.Tf72One

open scoped BigOperators

/-- Two-sided rational enclosure of `Real.cos θ` from the Taylor remainder bound
`Work.ZeroFreeTables.XY.CosTayAbs`: if the `N`-th partial Maclaurin sum `S` of `cos` at `θ` and the
remainder `R = |θ|^(2N+2)/(2N+2)!` satisfy `lo + R ≤ S` and `S + R ≤ hi`, then
`lo ≤ cos θ ≤ hi`. -/
lemma cos_bounds (θ lo hi : ℝ) (N : ℕ)
    (hlo : lo + |θ|^(2*N+2)/((2*N+2).factorial)
        ≤ ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial))
    (hhi : (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial))
        + |θ|^(2*N+2)/((2*N+2).factorial) ≤ hi) :
    lo ≤ Real.cos θ ∧ Real.cos θ ≤ hi := by
  have h := Work.ZeroFreeTables.XY.CosTayAbs θ N
  obtain ⟨ha, hb⟩ := abs_le.mp h
  exact ⟨by linarith, by linarith⟩

/-- Two-sided rational enclosure of `Real.sin θ` from the Taylor remainder bound
`Work.ZeroFreeTables.XY.SinTayAbs`. -/
lemma sin_bounds (θ lo hi : ℝ) (N : ℕ)
    (hlo : lo + |θ|^(2*N+2)/((2*N+2).factorial)
        ≤ ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial))
    (hhi : (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial))
        + |θ|^(2*N+2)/((2*N+2).factorial) ≤ hi) :
    lo ≤ Real.sin θ ∧ Real.sin θ ≤ hi := by
  have h := Work.ZeroFreeTables.XY.SinTayAbs θ N
  obtain ⟨ha, hb⟩ := abs_le.mp h
  exact ⟨by linarith, by linarith⟩

/-- Rational enclosures (width `2·10⁻⁴`) of `cos θ`, `sin θ` at `θ = 15/2, 8, 42/5`. -/
theorem trig_high : (3465353/10000000 : ℝ) ≤ Real.cos (15/2 : ℝ) ∧ Real.cos (15/2 : ℝ) ≤ (3467354/10000000 : ℝ) ∧ (9378999/10000000 : ℝ) ≤ Real.sin (15/2 : ℝ) ∧ Real.sin (15/2 : ℝ) ≤ (9381/10000 : ℝ) ∧
  (-1456001/10000000 : ℝ) ≤ Real.cos (8 : ℝ) ∧ Real.cos (8 : ℝ) ≤ (-727/5000 : ℝ) ∧ (9892582/10000000 : ℝ) ≤ Real.sin (8 : ℝ) ∧ Real.sin (8 : ℝ) ≤ (9894583/10000000 : ℝ) ∧
  (-5193887/10000000 : ℝ) ≤ Real.cos (42/5 : ℝ) ∧ Real.cos (42/5 : ℝ) ≤ (-5191886/10000000 : ℝ) ∧ (8544989/10000000 : ℝ) ≤ Real.sin (42/5 : ℝ) ∧ Real.sin (42/5 : ℝ) ≤ (854699/1000000 : ℝ) := by
  have h1 := cos_bounds (15/2) (3465353/10000000) (3467354/10000000) 13
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h2 := sin_bounds (15/2) (9378999/10000000) (9381/10000) 13
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h3 := cos_bounds (8) (-1456001/10000000) (-727/5000) 14
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h4 := sin_bounds (8) (9892582/10000000) (9894583/10000000) 13
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h5 := cos_bounds (42/5) (-5193887/10000000) (-5191886/10000000) 14
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  have h6 := sin_bounds (42/5) (8544989/10000000) (854699/1000000) 14
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2⟩

end Work.OffAxis.Tf72One
