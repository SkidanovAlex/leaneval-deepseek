import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.Kernel

/-!
# The far-field kernel bound used at the point `z = (1-u)𝓛`

Combining the pointwise bound `‖Hk L K z‖ ≤ e^{-(L-2K)·Re z}·4/‖z‖²` (Kernel.lean) with
`Re z ≥ 0` (so the exponential factor is `≤ 1`) and the elementary estimate
`‖u‖ ≤ 2‖u - 1‖` (valid as `‖u‖ ≥ 2`) gives

`‖Hk L K ((1-u)𝓛)‖ ≤ 16 / (𝓛² ‖u‖²)`

for `L - 2K > 0`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

theorem norm_Hk_le {L K 𝓛 : ℝ} (hK : 0 < K) (hLK : 0 < L - 2 * K) (h𝓛 : 0 < 𝓛) {u : ℂ}
    (h1 : 0 < u.re) (h2 : u.re < 1) (h3 : 2 ≤ ‖u‖) :
    ‖Work.LinnikContract.Hk L K ((1 - u) * (𝓛 : ℂ))‖ ≤ (16 / 𝓛 ^ 2) / ‖u‖ ^ 2 := by
  set z : ℂ := (1 - u) * (𝓛 : ℂ) with hzdef
  -- `Re z = (1 - Re u)·𝓛 > 0`, since `Re u < 1` and `𝓛 > 0`.
  have hzre : 0 ≤ z.re := by
    have h : z.re = (1 - u.re) * 𝓛 := by
      rw [hzdef, Complex.mul_re]
      simp
    rw [h]
    exact mul_nonneg (by linarith) (le_of_lt h𝓛)
  have hineq := norm_Hk_le_inv_sq (L := L) (K := K) hK hzre
  -- The exponential factor is at most `1` because `L - 2K > 0` and `Re z ≥ 0`.
  have hexp1 : Real.exp (-(L - 2 * K) * z.re) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [hzre, hLK]
  have hstep : ‖Hk L K z‖ ≤ 4 / ‖z‖ ^ 2 := by
    calc ‖Hk L K z‖ ≤ Real.exp (-(L - 2 * K) * z.re) * (4 / ‖z‖ ^ 2) := hineq
      _ ≤ 1 * (4 / ‖z‖ ^ 2) := mul_le_mul_of_nonneg_right hexp1 (by positivity)
      _ = 4 / ‖z‖ ^ 2 := one_mul _
  -- `‖z‖ = 𝓛·‖u - 1‖`.
  have hzn : ‖z‖ = 𝓛 * ‖u - 1‖ := by
    rw [hzdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝓛]
    rw [norm_sub_rev (1 : ℂ) u]
    ring
  -- Since `‖u‖ ≥ 2`, we have `‖u‖ ≤ 2‖u - 1‖`.
  have htri : ‖u‖ ≤ ‖u - 1‖ + 1 := by
    have h := norm_add_le (u - 1) (1 : ℂ)
    rw [sub_add_cancel] at h
    simpa using h
  have hu1 : 1 ≤ ‖u - 1‖ := by linarith
  have hun : ‖u‖ ≤ 2 * ‖u - 1‖ := by linarith
  have hzpos : 0 < ‖z‖ := by rw [hzn]; exact mul_pos h𝓛 (by linarith)
  -- `4/‖z‖² ≤ 16/(𝓛²‖u‖²)`.
  have hfin : 4 / ‖z‖ ^ 2 ≤ (16 / 𝓛 ^ 2) / ‖u‖ ^ 2 := by
    rw [div_le_iff₀ (pow_pos hzpos 2)]
    have h𝓛ne : 𝓛 ≠ 0 := ne_of_gt h𝓛
    have hune : ‖u‖ ≠ 0 := by positivity
    have hexpand : ((16 / 𝓛 ^ 2) / ‖u‖ ^ 2) * ‖z‖ ^ 2 = 16 * ‖u - 1‖ ^ 2 / ‖u‖ ^ 2 := by
      rw [hzn]
      field_simp
    rw [hexpand]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖u‖ ^ 2)]
    have hs : ‖u‖ ^ 2 ≤ (2 * ‖u - 1‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hun 2
    nlinarith [hs]
  linarith [hstep, hfin]

end Work.LinnikAreas
