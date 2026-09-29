import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.Fx
import Submission.Work.CNum.CircleParam.unitCircle_param
import Submission.Work.CNum.GridCover.grid_cover

namespace Work.CNum

open scoped BigOperators

/-- **Boundary norm bounds for `φ_C` from the certified arc bounds.**

If the certified upper bounds `Gv k` bound `circleLog φ_C` from above on the `k`-th arc of the
dyadic subdivision of `[0,1]` and are `≤ log 700000`, and the certified lower bounds `gv k` bound
it from below and are `≥ log (1/10¹³)`, then every point `z` of the unit circle at which `φ_C`
does not vanish satisfies `1/10¹³ ≤ ‖φ_C z‖ ≤ 700000`. -/
theorem PhiCNormBounds (hUp : ∀ (k : ℕ), k < 1024 → ∀ t ∈ Set.Icc ((k : ℝ) / 1024) (((k : ℝ) + 1) / 1024), Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t ≤ Work.ANum.m2r (Work.CNum.Gv k)) (hDn : ∀ (k : ℕ), k < 1024 → ∀ t ∈ Set.Icc ((k : ℝ) / 1024) (((k : ℝ) + 1) / 1024), Work.ANum.m2r (Work.CNum.gv k) ≤ Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t) (hGv : ∀ (k : ℕ), k < 1024 → Work.ANum.m2r (Work.CNum.Gv k) ≤ Real.log 700000) (hgv : ∀ (k : ℕ), k < 1024 → Real.log (1 / 10 ^ 13) ≤ Work.ANum.m2r (Work.CNum.gv k)) (z : ℂ) (hz : ‖z‖ = 1) (hne : Submission.CDTPlan.phiC z ≠ 0) : (1 : ℝ) / 10 ^ 13 ≤ ‖Submission.CDTPlan.phiC z‖ ∧ ‖Submission.CDTPlan.phiC z‖ ≤ 700000 := by
  -- `z` is `e^{2πit}` for some `t ∈ [0,1]`, and `t` lies in one of the 1024 arcs.
  obtain ⟨t, htI, hexp⟩ := CircleParam.unitCircle_param z hz
  obtain ⟨k, hk, htk⟩ := GridCover.grid_cover t htI
  -- On that arc, `circleLog φ_C t` is the logarithm of the norm of `φ_C z`.
  have hlog : Submission.CDTPlan.circleLog Submission.CDTPlan.phiC t =
      Real.log ‖Submission.CDTPlan.phiC z‖ := by
    simp only [Submission.CDTPlan.circleLog]
    rw [hexp]
  have hpos : (0 : ℝ) < ‖Submission.CDTPlan.phiC z‖ := norm_pos_iff.mpr hne
  constructor
  · -- lower bound
    have h1 := hDn k hk t htk
    have h2 := hgv k hk
    have h3 : Real.log (1 / 10 ^ 13) ≤ Real.log ‖Submission.CDTPlan.phiC z‖ := by
      rw [← hlog]; linarith
    calc (1 : ℝ) / 10 ^ 13 = Real.exp (Real.log (1 / 10 ^ 13)) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log ‖Submission.CDTPlan.phiC z‖) := Real.exp_le_exp.mpr h3
      _ = ‖Submission.CDTPlan.phiC z‖ := Real.exp_log hpos
  · -- upper bound
    have h1 := hUp k hk t htk
    have h2 := hGv k hk
    have h3 : Real.log ‖Submission.CDTPlan.phiC z‖ ≤ Real.log 700000 := by
      rw [← hlog]; linarith
    calc ‖Submission.CDTPlan.phiC z‖ = Real.exp (Real.log ‖Submission.CDTPlan.phiC z‖) :=
          (Real.exp_log hpos).symm
      _ ≤ Real.exp (Real.log 700000) := Real.exp_le_exp.mpr h3
      _ = 700000 := Real.exp_log (by norm_num)

end Work.CNum
