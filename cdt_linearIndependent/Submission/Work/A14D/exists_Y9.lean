import Mathlib
import Submission.Work.A14.defs
import Submission.Work.C17f.frobenius_double_exponent_zero

namespace Work.A14D

/-- `PZ` factors as `(z - 1/9) * q` with `q z = -9z(1−z)`, so `1/9` is a regular singular
point with both indicial exponents equal to `0`. -/
lemma PZ_factor (z : ℂ) : PZ z = (z - ninth) * (-9 * z * (1 - z)) := by
  simp only [PZ, ninth]; ring

/-- `q(1/9) ≠ 0`. -/
lemma q_ninth_ne : (-9 : ℂ) * ninth * (1 - ninth) ≠ 0 := by
  simp only [ninth]; norm_num

/-- The residue condition `PZ'(1/9) = q(1/9)` (exponents `0, 0`). -/
lemma PZ'_at_ninth : PZ' ninth = -9 * ninth * (1 - ninth) := by
  simp only [PZ', ninth]; norm_num

theorem exists_Y9 : ∃ y9 δ, Y9 y9 δ := by
  obtain ⟨δ, hδpos, y, hydiff, hyval, hode⟩ :=
    Work.C17f.frobenius_double_exponent_zero (s := ninth) (P2 := PZ) (P1 := PZ')
      (P0 := RZ) (q := fun z => -9 * z * (1 - z)) (1 : ℂ)
      PZ_factor
      (by fun_prop)
      q_ninth_ne
      (by unfold PZ'; fun_prop)
      PZ'_at_ninth
      (by unfold RZ; fun_prop)
  refine ⟨y, min δ (1 / 20), ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min hδpos (by norm_num)
  · exact min_le_right _ _
  · exact hydiff.mono (Metric.ball_subset_ball (min_le_left δ (1 / 20)))
  · rw [hyval]; norm_num
  · intro z hz
    have hz' : z ∈ Metric.ball ninth δ := Metric.ball_subset_ball (min_le_left δ (1 / 20)) hz
    simpa only [LZ] using hode z hz'

end Work.A14D
