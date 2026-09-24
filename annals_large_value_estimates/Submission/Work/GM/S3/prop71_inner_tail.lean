import Mathlib
import Submission.Work.GM.S3.prop71_defs

namespace Work.GM.S3

open Complex MeasureTheory

/-- GM Prop 7.1, off the stationary set: if `|phas m v| > τ = (M N)^η / N` (and `N ≥ 1`), the
inner integral is at most `Cj · ((M N)^η)^{-j}` — the `O(T^{-300})` gain of the proposition.
`hdec` is the non-stationary-phase estimate `Work.GM.S3.prop71_inner_decay`.

Key computation: `|N · phas m v| = N · |phas m v| > N · τ = (M N)^η > 0`, so
`Cj / |N phas|^j ≤ Cj / ((M N)^η)^j = Cj · ((M N)^η)^{-j}` (`Real.rpow_neg`, `Real.rpow_natCast`).
`hbig` also gives `phas m v ≠ 0`, so the hypothesis of `hdec` holds. -/
theorem prop71_inner_tail (j : ℕ) (Cj : ℝ) (hCj : 0 < Cj)
    (hdec : ∀ (N : ℕ) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ), v ∈ pbox → (N : ℝ) * phas m v ≠ 0 →
      ‖innerInt N m v‖ ≤ Cj / |(N : ℝ) * phas m v| ^ j)
    (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (hη : 0 < η) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ) (hv : v ∈ pbox)
    (hbig : (Submission.LargeValues.M N) ^ η / (N : ℝ) < |phas m v|) :
    ‖innerInt N m v‖ ≤ Cj * (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))) := by
  have _ : 0 < η := hη
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMpos : 0 < Submission.LargeValues.M N := by
    unfold Submission.LargeValues.M
    exact Real.rpow_pos_of_pos hNpos _
  have hBpos : 0 < (Submission.LargeValues.M N) ^ η := Real.rpow_pos_of_pos hMpos η
  -- `hbig` forces the phase to be nonzero
  have hphane : phas m v ≠ 0 := by
    intro h0
    have hlt : (Submission.LargeValues.M N) ^ η / (N : ℝ) < 0 := by
      rw [h0, abs_zero] at hbig
      exact hbig
    have hpos : 0 < (Submission.LargeValues.M N) ^ η / (N : ℝ) := div_pos hBpos hNpos
    linarith
  have hne : (N : ℝ) * phas m v ≠ 0 := mul_ne_zero (ne_of_gt hNpos) hphane
  refine (hdec N m v hv hne).trans ?_
  -- `|N · phas| = N |phas| > (M N)^η`
  have hBA : (Submission.LargeValues.M N) ^ η < |(N : ℝ) * phas m v| := by
    rw [abs_mul, abs_of_pos hNpos]
    have h := (div_lt_iff₀ hNpos).mp hbig
    linarith
  -- hence `((M N)^η)^j ≤ |N phas|^j`, and inverting reverses the inequality
  have hp : ((Submission.LargeValues.M N) ^ η) ^ j ≤ |(N : ℝ) * phas m v| ^ j :=
    pow_le_pow_left₀ hBpos.le hBA.le j
  have hBj : 0 < ((Submission.LargeValues.M N) ^ η) ^ j := pow_pos hBpos j
  calc Cj / |(N : ℝ) * phas m v| ^ j
      ≤ Cj / ((Submission.LargeValues.M N) ^ η) ^ j :=
        div_le_div_of_nonneg_left hCj.le hBj hp
    _ = Cj * (((Submission.LargeValues.M N) ^ η) ^ (-(j : ℝ))) := by
        rw [div_eq_mul_inv, Real.rpow_neg hBpos.le, Real.rpow_natCast]

end Work.GM.S3
