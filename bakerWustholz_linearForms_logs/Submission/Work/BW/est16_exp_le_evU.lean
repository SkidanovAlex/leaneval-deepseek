import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.num_xi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The `(16)`-exponent at level `J+1` (with `‖z‖ = R` and `|s| ≤ 4S^{(J)}`, written with the
abstract `sz = |s|`) is at most `evU`: only the `(‖z‖+sz)/2^{J+1}` term needs an argument, namely
`‖z‖ + sz ≤ R + 4S^{(J)}` with `R = 7.2S'`. -/
theorem est16_exp_le_evU {r : ℕ} (hr : 2 ≤ r) {d h J : ℕ} {σ : Fin r → ℝ} {z : ℂ} {sz : ℝ}
    (hz : ‖z‖ = evR r J (pS r d h : ℝ))
    (hsz : sz ≤ 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) (hsz0 : 0 ≤ sz)
    (hD : 0 ≤ pD r d σ) :
    (d : ℝ) * (h : ℝ) * (pxi r * (pxi r ^ (r * J) * (pT r d σ : ℝ)))
        + 1.055 * (pS r d h : ℝ) * pD r d σ
        + 1.008 * ((‖z‖ + sz) / 2 ^ (J + 1)) * pD r d σ
        + 0.044 * ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ
      ≤ evU r d h σ J := by
  rw [evU]
  have hR : ‖z‖ + sz
      ≤ evR r J (pS r d h : ℝ) + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)) := by
    rw [hz]; linarith
  have hmain : 1.008 * ((‖z‖ + sz) / 2 ^ (J + 1)) * pD r d σ
      ≤ 1.008 * ((evR r J (pS r d h : ℝ)
          + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / 2 ^ (J + 1)) * pD r d σ := by
    gcongr
  linarith

end Work.BW
