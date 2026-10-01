import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.HarmonicLogBound
import Submission.Work.LinnikAreas.JutilaPieces.LogFloorGap

namespace Work.LinnikAreas.JutilaPieces

/-- **Step 3 of the `S3MainTerm` bookkeeping: the harmonic `q`-sum** (pure Mathlib, no import, so it
cannot drift against `s3G`/`s3main`).  For `2 ≤ z ≤ N`,

  `|Σ_{q ≤ N/z} 1/q − log(N/z)| ≤ C`, with `C` absolute.

Route (`C = 1 + log 2` works): with `m = N/z` (Nat floor), `z ≤ N` gives `m ≥ 1`; the classical
harmonic estimate `log m ≤ Σ_{q ≤ m} 1/q ≤ 1 + log m` (lower bound via `∫_1^{m+1} dt/t`, upper via
`1 + ∫_1^m dt/t`) gives `|H_m − log m| ≤ 1`; and `m ≤ N/z < m + 1` gives
`1 ≤ (N/z)/m < 1 + 1/m ≤ 2`, so `|log(N/z) − log m| ≤ log 2`.  Triangle inequality, uniform in
`N, z`; the edge case `z = 2, N = 2` gives sum `1`, `log 1 = 0`, difference `1 ≤ C`. -/
theorem S3HarmonicSum : ∃ C : ℝ, 0 < C ∧ ∀ (N z : ℕ), 2 ≤ z → z ≤ N →
    |(∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ)) - Real.log ((N : ℝ) / (z : ℝ))| ≤ C := by
  refine ⟨1 + Real.log 2, by positivity, ?_⟩
  intro N z hz hzN
  set m := N / z with hm
  have hzpos : 0 < z := by omega
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact (Nat.le_div_iff_mul_le hzpos).mpr (by simpa using hzN)
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    linarith
  have hid : (∑ q ∈ Finset.Icc 1 m, (1 : ℝ) / (q : ℝ)) = (harmonic m : ℝ) := by
    have h : (harmonic m : ℝ) = ∑ q ∈ Finset.Icc 1 m, (1 : ℝ) / (q : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      push_cast
      simp [one_div]
    exact h.symm
  have hlow : Real.log (m : ℝ) ≤ ∑ q ∈ Finset.Icc 1 m, (1 : ℝ) / (q : ℝ) := by
    rw [hid]
    exact le_trans (Real.log_le_log hmpos (by push_cast; linarith)) (log_add_one_le_harmonic m)
  have hup : (∑ q ∈ Finset.Icc 1 m, (1 : ℝ) / (q : ℝ)) ≤ 1 + Real.log (m : ℝ) := HarmonicLogBound m
  have hHm : |(∑ q ∈ Finset.Icc 1 m, (1 : ℝ) / (q : ℝ)) - Real.log (m : ℝ)| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hgap : |Real.log (m : ℝ) - Real.log ((N : ℝ) / (z : ℝ))| ≤ Real.log 2 := by
    have h := LogFloorGap N z hz hzN
    rw [← hm] at h
    rw [abs_sub_comm] at h
    exact h
  calc |(∑ q ∈ Finset.Icc 1 m, (1 : ℝ) / (q : ℝ)) - Real.log ((N : ℝ) / (z : ℝ))|
      ≤ |(∑ q ∈ Finset.Icc 1 m, (1 : ℝ) / (q : ℝ)) - Real.log (m : ℝ)|
        + |Real.log (m : ℝ) - Real.log ((N : ℝ) / (z : ℝ))| := abs_sub_le _ _ _
    _ ≤ 1 + Real.log 2 := add_le_add hHm hgap

end Work.LinnikAreas.JutilaPieces
