import Mathlib
import Submission.Work.ZeroFreeTables.XY.CosTayAbs
import Submission.Work.ZeroFreeTables.XY.SinTayAbs

open scoped BigOperators

namespace Work.OffAxis.Tf72One

/-- Lower enclosure of `cos θ` from the Taylor remainder bound `CosTayAbs`: if `lo` is at most
the partial Maclaurin sum of order `2N` minus its remainder bound `|θ|^(2N+2)/(2N+2)!`, then
`lo ≤ cos θ`. -/
lemma cos_ge_of_tay (θ : ℝ) (N : ℕ) {lo : ℝ}
    (hlo : lo ≤ (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial)) - |θ|^(2*N+2)/((2*N+2).factorial)) :
    lo ≤ Real.cos θ := by
  have h := Work.ZeroFreeTables.XY.CosTayAbs θ N
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  linarith

/-- Upper enclosure of `cos θ`: if `hi` is at least the partial Maclaurin sum of order `2N`
plus its remainder bound, then `cos θ ≤ hi`. -/
lemma cos_le_of_tay (θ : ℝ) (N : ℕ) {hi : ℝ}
    (hhi : (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial)) + |θ|^(2*N+2)/((2*N+2).factorial) ≤ hi) :
    Real.cos θ ≤ hi := by
  have h := Work.ZeroFreeTables.XY.CosTayAbs θ N
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  linarith

/-- Lower enclosure of `sin θ` from the Taylor remainder bound `SinTayAbs`. -/
lemma sin_ge_of_tay (θ : ℝ) (N : ℕ) {lo : ℝ}
    (hlo : lo ≤ (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial)) - |θ|^(2*N+2)/((2*N+2).factorial)) :
    lo ≤ Real.sin θ := by
  have h := Work.ZeroFreeTables.XY.SinTayAbs θ N
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  linarith

/-- Upper enclosure of `sin θ` from the Taylor remainder bound `SinTayAbs`. -/
lemma sin_le_of_tay (θ : ℝ) (N : ℕ) {hi : ℝ}
    (hhi : (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial)) + |θ|^(2*N+2)/((2*N+2).factorial) ≤ hi) :
    Real.sin θ ≤ hi := by
  have h := Work.ZeroFreeTables.XY.SinTayAbs θ N
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  linarith

/-- Rational enclosures (width `2·10⁻⁴`) of `cos θ`, `sin θ` at `θ = 6, 13/2, 7`. -/
theorem trig_mid : (9600702/10000000 : ℝ) ≤ Real.cos (6 : ℝ) ∧ Real.cos (6 : ℝ) ≤ (9602703/10000000 : ℝ) ∧ (-2795155/10000000 : ℝ) ≤ Real.sin (6 : ℝ) ∧ Real.sin (6 : ℝ) ≤ (-2793154/10000000 : ℝ) ∧
  (9764876/10000000 : ℝ) ≤ Real.cos (13/2 : ℝ) ∧ Real.cos (13/2 : ℝ) ≤ (9766877/10000000 : ℝ) ∧ (2150199/10000000 : ℝ) ≤ Real.sin (13/2 : ℝ) ∧ Real.sin (13/2 : ℝ) ≤ (10761/50000 : ℝ) ∧
  (7538022/10000000 : ℝ) ≤ Real.cos (7 : ℝ) ∧ Real.cos (7 : ℝ) ≤ (7540023/10000000 : ℝ) ∧ (6568865/10000000 : ℝ) ≤ Real.sin (7 : ℝ) ∧ Real.sin (7 : ℝ) ≤ (6570866/10000000 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply cos_ge_of_tay 6 11; norm_num
  · apply cos_le_of_tay 6 11; norm_num
  · apply sin_ge_of_tay 6 11; norm_num
  · apply sin_le_of_tay 6 11; norm_num
  · apply cos_ge_of_tay (13/2) 12; norm_num
  · apply cos_le_of_tay (13/2) 12; norm_num
  · apply sin_ge_of_tay (13/2) 11; norm_num
  · apply sin_le_of_tay (13/2) 11; norm_num
  · apply cos_ge_of_tay 7 12; norm_num
  · apply cos_le_of_tay 7 12; norm_num
  · apply sin_ge_of_tay 7 12; norm_num
  · apply sin_le_of_tay 7 12; norm_num

end Work.OffAxis.Tf72One
