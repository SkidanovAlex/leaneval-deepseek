import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.KfBall

/-- **The ball membership criterion.**  For `‖z‖ < ρ`, a point `ω` of the unit sphere and a
radius `r > 0`, the point `r • ω` lies in the open ball `B(z, ρ)` exactly when `r` is below the
larger root `⟨z, ω⟩ + √(⟨z, ω⟩² + (ρ² - ‖z‖²))` of the quadratic that describes `‖r ω - z‖ = ρ`.

The proof is the elementary computation
`‖r ω - z‖² = r² - 2 r ⟨z, ω⟩ + ‖z‖²`, whose comparison with `ρ²` is the quadratic inequality
`(r - ⟨z, ω⟩)² < ⟨z, ω⟩² + ρ² - ‖z‖²`; the *lower* root of the quadratic is automatically negative
(because `ρ² - ‖z‖² > 0`), so for `r > 0` only the upper root matters. -/
theorem mem_ball_smul_sphere_iff (z : Work.LWP.R3) {ρ : ℝ} (hz : ‖z‖ < ρ)
    (ω : Metric.sphere (0 : Work.LWP.R3) 1) {r : ℝ} (hr : 0 < r) :
    r • (ω : Work.LWP.R3) ∈ Metric.ball z ρ ↔
      r < inner ℝ z (ω : Work.LWP.R3)
        + Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2)) := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hz
  have hω_norm : ‖(ω : Work.LWP.R3)‖ = 1 := by
    have h := ω.2
    rw [mem_sphere_iff_norm, sub_zero] at h
    exact h
  rw [Metric.mem_ball, dist_eq_norm]
  set a : ℝ := inner ℝ z (ω : Work.LWP.R3) with ha
  set c : ℝ := a ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2) with hc
  have hcpos : 0 < c := by
    rw [hc]; nlinarith [sq_nonneg a, norm_nonneg z]
  have hsq : ‖r • (ω : Work.LWP.R3) - z‖ ^ 2 = r ^ 2 - 2 * r * a + ‖z‖ ^ 2 := by
    rw [norm_sub_sq_real]
    have h1 : ‖r • (ω : Work.LWP.R3)‖ ^ 2 = r ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hω_norm, mul_one, sq_abs]
    have h2 : inner ℝ (r • (ω : Work.LWP.R3)) z = r * a := by
      rw [inner_smul_left]; simp [ha, real_inner_comm]
    rw [h1, h2]; ring
  have hstep1 : ‖r • (ω : Work.LWP.R3) - z‖ < ρ ↔
      ‖r • (ω : Work.LWP.R3) - z‖ ^ 2 < ρ ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_of_pos hρ]
  have hstep2 : ‖r • (ω : Work.LWP.R3) - z‖ ^ 2 < ρ ^ 2 ↔ (r - a) ^ 2 < c := by
    rw [hsq, hc]
    constructor <;> intro h <;> nlinarith
  rw [hstep1, hstep2]
  have hlt : a - Real.sqrt c < 0 := by
    have h2c : a ^ 2 < c := by rw [hc]; nlinarith [norm_nonneg z]
    have h1 : Real.sqrt (a ^ 2) < Real.sqrt c := Real.sqrt_lt_sqrt (sq_nonneg a) h2c
    rw [Real.sqrt_sq_eq_abs] at h1
    nlinarith [le_abs_self a]
  have hfin : (r - a) ^ 2 < c ↔ r < a + Real.sqrt c := by
    have hL : (r - a) ^ 2 < c ↔ |r - a| < Real.sqrt c := by
      rw [← sq_abs (r - a), Real.lt_sqrt (abs_nonneg (r - a))]
    rw [hL, abs_lt]
    constructor
    · rintro ⟨-, h2⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩
  rw [hfin]

end Work.CoreResiduals.BiotSavart.KfBall
