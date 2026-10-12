import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.ChiSmall
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `ζ ≥ √2/2` on the quarter cube face (`Work.BoseB1Cube.zetaQuarterLower`)

The FS 1D cosine profile `ζ(y) = cos(π y)·1_{|y| ≤ 1/2}` (`Submission.BoseGases.zeta1d`)
is bounded below by `√2/2` on `|y| ≤ 1/4`: `[0, π/4]` is the first half of the cosine's
first monotonicity arc `[0, π]`, where `cos` decreases from `1` to `cos(π/4) = √2/2`.

This is the input that turns the *unnormalised* `M`-th power base
`chiSmallBase M z = (ζ z₁ ζ z₂ ζ z₃)^M` into the **lower** bound `((√2/2)³)^M` on the
quarter cube `|z_j| ≤ 1/4` (see `Submission.BoseB1Cube.chiBumpDefs` and its consumers),
used to locate the plateau of the small-box bump.

Contents:
* `cos_pi_mul_ge_sqrt_two_div_two` — the trigonometric core, `|t| ≤ 1/4 → √2/2 ≤ cos(π t)`;
* `zetaQuarterLower` — the requested statement about `Submission.BoseGases.zeta1d`.
-/

namespace Work.BoseB1Cube

/-- **Trigonometric core.** `cos (π t) ≥ √2/2` whenever `|t| ≤ 1/4`.

`cos` is even, so `cos (π t) = cos |π t|`; and `cos` is antitone on `[0, π]`, with
`|π t| ≤ π/4 ≤ π`, whence `cos (π t) = cos |π t| ≥ cos (π/4) = √2/2`. -/
theorem cos_pi_mul_ge_sqrt_two_div_two {t : ℝ} (ht : |t| ≤ 1 / 4) :
    Real.sqrt 2 / 2 ≤ Real.cos (Real.pi * t) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hle : |Real.pi * t| ≤ Real.pi / 4 := by
    calc
      |Real.pi * t| = Real.pi * |t| := by rw [abs_mul, abs_of_pos hpi]
      _ ≤ Real.pi * (1 / 4) := mul_le_mul_of_nonneg_left ht (le_of_lt hpi)
      _ = Real.pi / 4 := by ring
  have hc : Real.cos (Real.pi / 4) ≤ Real.cos (Real.pi * t) := by
    have h' : Real.cos (Real.pi / 4) ≤ Real.cos (|Real.pi * t|) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (Real.pi * t))
        (by linarith) hle
    rwa [Real.cos_abs] at h'
  calc
    Real.sqrt 2 / 2 = Real.cos (Real.pi / 4) := by rw [Real.cos_pi_div_four]
    _ ≤ Real.cos (Real.pi * t) := hc

/-- **The requested lemma.** On the quarter face `|t| ≤ 1/4` the FS 1D cosine profile
`Submission.BoseGases.zeta1d` is at least `√2/2` (where it coincides with `cos (π t)`). -/
theorem zetaQuarterLower {t : ℝ} (ht : |t| ≤ 1 / 4) :
    Real.sqrt 2 / 2 ≤ Submission.BoseGases.zeta1d t := by
  have hhalf : |t| ≤ 1 / 2 := le_trans ht (by norm_num)
  rw [Submission.BoseGases.zeta1d_of_abs_le hhalf]
  exact cos_pi_mul_ge_sqrt_two_div_two ht

end Work.BoseB1Cube
