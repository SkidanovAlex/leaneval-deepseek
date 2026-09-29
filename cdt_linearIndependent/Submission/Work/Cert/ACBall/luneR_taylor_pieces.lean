import Mathlib
import Submission.Work.Cert.ACBall.LuneChain

namespace Work.Cert.ACBall

open Work.APsi

/-- The Taylor remainder of the quadratic radicand `R = luneR c`, and the (exact) Lipschitz
constant `2B²` of `R'`, at `c = 36/5`.  Both are elementary consequences of the exact Taylor
identity `Work.ANum2.luneR_taylor` for the quadratic `R` and of `R' = Work.ANum2.luneRd`. -/
theorem luneR_taylor_pieces (z z0 : ℂ) :
    ‖Work.APsi.luneR (36 / 5) z - Work.APsi.luneR (36 / 5) z0‖
        ≤ ‖deriv (Work.APsi.luneR (36 / 5)) z0‖ * ‖z - z0‖
          + (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * ‖z - z0‖ ^ 2 ∧
      ‖deriv (Work.APsi.luneR (36 / 5)) z - deriv (Work.APsi.luneR (36 / 5)) z0‖
        ≤ 2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * ‖z - z0‖ := by
  -- the leading coefficient `B² = (1 + c²)²` of the quadratic `luneR c` is a positive real,
  -- so its norm is itself
  have hK : ‖(1 + ((36 / 5 : ℝ) : ℂ) ^ 2) ^ 2‖ = (1 + (36 / 5 : ℝ) ^ 2) ^ 2 := by
    rw [show (1 + ((36 / 5 : ℝ) : ℂ) ^ 2) ^ 2 = (((1 + (36 / 5 : ℝ) ^ 2) ^ 2 : ℝ) : ℂ) by
      push_cast; ring]
    exact Work.ANum2.norm_ofReal_of_nonneg (by positivity)
  -- exact Taylor identity: `R z - R z₀ = R'(z₀)(z - z₀) + B²(z - z₀)²`
  have hT : Work.APsi.luneR (36 / 5) z - Work.APsi.luneR (36 / 5) z0
      = Work.ANum2.luneRd (36 / 5) z0 * (z - z0)
        + (1 + ((36 / 5 : ℝ) : ℂ) ^ 2) ^ 2 * (z - z0) ^ 2 := by
    linear_combination (Work.ANum2.luneR_taylor (36 / 5) z z0)
  have hD : Work.ANum2.luneRd (36 / 5) z0
      = deriv (Work.APsi.luneR (36 / 5)) z0 := (Work.ANum2.deriv_luneR (36 / 5) z0).symm
  constructor
  · rw [hT]
    calc ‖Work.ANum2.luneRd (36 / 5) z0 * (z - z0)
            + (1 + ((36 / 5 : ℝ) : ℂ) ^ 2) ^ 2 * (z - z0) ^ 2‖
        ≤ ‖Work.ANum2.luneRd (36 / 5) z0 * (z - z0)‖
            + ‖(1 + ((36 / 5 : ℝ) : ℂ) ^ 2) ^ 2 * (z - z0) ^ 2‖ := norm_add_le _ _
      _ = ‖deriv (Work.APsi.luneR (36 / 5)) z0‖ * ‖z - z0‖
            + (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * ‖z - z0‖ ^ 2 := by
            simp only [norm_mul, norm_pow, hK, hD]
  · -- `R' = luneRd (36/5)` is affine with slope `2B²`
    have h2 : deriv (Work.APsi.luneR (36 / 5)) z - deriv (Work.APsi.luneR (36 / 5)) z0
        = 2 * (1 + ((36 / 5 : ℝ) : ℂ) ^ 2) ^ 2 * (z - z0) := by
      rw [Work.ANum2.deriv_luneR, Work.ANum2.deriv_luneR]
      simp only [Work.ANum2.luneRd]
      ring
    rw [h2]
    refine le_of_eq ?_
    simp only [norm_mul, hK]
    norm_num

end Work.Cert.ACBall
