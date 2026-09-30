import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.TentDefs
import Submission.Work.BMF.tent_fourier

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Fourier series of the integration kernel `kern`

The kernel `kern K` is the constant `π²K/2` times the Fourier coefficient sequence of the
tent function of width `1/(2K)`:

`kern K c = (π²K/2) · tentCoeff (1/(2K)) c`.

Since `0 < 1/(2K) ≤ 1/2` as soon as `K ≥ 1`, the Fourier series of the tent
(`tent_fourier`) immediately gives

`∑_{c ∈ ℤ} kern K c · e(cθ) = (π²K/2) · tent (1/(2K)) θ`,

which is the statement below.
-/

namespace Work.BMF

theorem kern_hasSum (K : ℕ) (hK : 1 ≤ K) (θ : ℝ) :
    HasSum (fun c : ℤ => (kern K c : ℂ) * eZ ((c : ℝ) * θ))
      (((Real.pi ^ 2 * (K : ℝ) / 2) * tent (1 / (2 * (K : ℝ))) θ : ℝ) : ℂ) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hBpos : 0 < 1 / (2 * (K : ℝ)) := by positivity
  have hB2 : 1 / (2 * (K : ℝ)) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ 2 * (K : ℝ) := by linarith
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h
  have h := (tent_fourier (1 / (2 * (K : ℝ))) θ hBpos hB2).mul_left
      (((Real.pi ^ 2 * (K : ℝ) / 2) : ℝ) : ℂ)
  convert h using 1
  · funext c
    simp only [kern, Complex.ofReal_mul]
    ring
  · push_cast
    ring

end Work.BMF
