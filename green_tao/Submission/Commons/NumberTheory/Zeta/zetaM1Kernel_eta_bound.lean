import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_bound_m1

namespace Commons.NumberTheory.Zeta

/-!
# The Green–Tao single-pair kernel bound on the vertical line `Γ₁`

We prove the pointwise bound requested for the Green–Tao `m = 1` kernel

`K(z,z') = ζ(1+z+z')/(ζ(1+z)·ζ(1+z')) · R^{z+z'}/(z²·z'²)`

along the vertical line `Γ₁ = {Re = 1/log R}`, i.e. at `z = zetaM1Eta R x`,
`z' = zetaM1Eta R y`:

`‖K(η x, η y)‖ ≤ K · (log(|x|+2)+1)/(1+x²) · (log(|y|+2)+1)/(1+y²)`.

Since `Re (1 + η x) = 1 + 1/log R > 1` and `Re (1 + η x + η y) = 1 + 2/log R > 1`
are both inside the half-plane of absolute convergence, every factor is
elementary: `ζ` is bounded in the half-plane `Re ≥ 1 + 1/log R`
(`norm_riemannZeta_le_const_of_one_lt_re`), `1/ζ(1+η x) ≪ log(|x|+2)+1` by the
zero-free-region bound (`zeta_region_inv_analytic_bound_ne`), the exponential
factor has norm exactly `R^{2/log R} = e²`, and each quadratic denominator
contributes `≪ (log R)²/(1+x²)` (`norm_inv_sq_zetaM1Eta`).
-/

/-- The norm of the single-pair kernel factors into the norms of its six factors. -/
private lemma zetaM1Kernel_norm_factor (R : ℝ) (z z' : ℂ) :
    ‖riemannZeta (1 + z + z') / (riemannZeta (1 + z) * riemannZeta (1 + z'))
        * (R : ℂ) ^ (z + z') / (z ^ 2 * z' ^ 2)‖
      = ‖riemannZeta (1 + z + z')‖ * ‖(riemannZeta (1 + z))⁻¹‖ * ‖(riemannZeta (1 + z'))⁻¹‖
        * ‖(R : ℂ) ^ (z + z')‖ * ‖(z ^ 2)⁻¹‖ * ‖(z' ^ 2)⁻¹‖ := by
  rw [show riemannZeta (1 + z + z') / (riemannZeta (1 + z) * riemannZeta (1 + z'))
        * (R : ℂ) ^ (z + z') / (z ^ 2 * z' ^ 2)
      = riemannZeta (1 + z + z') * (riemannZeta (1 + z))⁻¹ * (riemannZeta (1 + z'))⁻¹
        * (R : ℂ) ^ (z + z') * (z ^ 2)⁻¹ * (z' ^ 2)⁻¹ by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]; ring]
  simp only [norm_mul]

private lemma log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three

theorem zetaM1Kernel_eta_bound {R : ℝ} (hR : 3 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ,
      ‖riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R x + Commons.NumberTheory.Zeta.zetaM1Eta R y)
        / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R x) * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R y))
        * (R : ℂ) ^ (Commons.NumberTheory.Zeta.zetaM1Eta R x + Commons.NumberTheory.Zeta.zetaM1Eta R y)
        / ((Commons.NumberTheory.Zeta.zetaM1Eta R x) ^ 2 * (Commons.NumberTheory.Zeta.zetaM1Eta R y) ^ 2)‖
      ≤ K * ((Real.log (|x| + 2) + 1) / (1 + x ^ 2))
          * ((Real.log (|y| + 2) + 1) / (1 + y ^ 2)) := by
  -- Elementary facts about `log R`.
  have hlogR_ge : 1 ≤ Real.log R :=
    le_trans (le_of_lt log_three_gt_one) (Real.log_le_log (by norm_num) hR)
  have hlogR_pos : 0 < Real.log R := by linarith
  have hRpos : 0 < R := by linarith
  have hσpos : 0 < 1 / Real.log R := one_div_log_pos hR
  have hσle : 1 / Real.log R ≤ 1 := one_div_log_le_one hR
  -- The two analytic inputs: `1/ζ(1+z) ≪ log(|z.im|+2)+1` near `Γ₂`, and `ζ` bounded
  -- on the half-plane `Re ≥ 1 + 1/log R`.
  obtain ⟨β₀, hβ₀pos, _hβ₀le, C, hCpos, hCbd⟩ := zeta_region_inv_analytic_bound_ne
  obtain ⟨Cn, hCnpos, hCnb⟩ :=
    norm_riemannZeta_le_const_of_one_lt_re (σ := 1 + 1 / Real.log R) (by linarith)
  refine ⟨Real.exp 2 * Cn * C ^ 2 * (Real.log R) ^ 4, by positivity, ?_⟩
  intro x y
  -- Nonnegativity of the two logarithmic weights.
  have hAx : 0 ≤ Real.log (|x| + 2) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ |x| + 2 by linarith [abs_nonneg x]); linarith
  have hAy : 0 ≤ Real.log (|y| + 2) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ |y| + 2 by linarith [abs_nonneg y]); linarith
  -- `η t ≠ 0`, since its real part is `1/log R > 0`.
  have hzx_ne : zetaM1Eta R x ≠ 0 := by
    intro h
    have h0 : (zetaM1Eta R x).re = 0 := by rw [h]; simp
    rw [zetaM1Eta_re] at h0
    exact (ne_of_gt hσpos) h0
  have hzy_ne : zetaM1Eta R y ≠ 0 := by
    intro h
    have h0 : (zetaM1Eta R y).re = 0 := by rw [h]; simp
    rw [zetaM1Eta_re] at h0
    exact (ne_of_gt hσpos) h0
  -- `η x` lies in the zero-free region `-(β₀/log(|Im|+2)) ≤ Re ≤ 1`.
  have hzx_low : -(β₀ / Real.log (|(zetaM1Eta R x).im| + 2)) ≤ (zetaM1Eta R x).re := by
    rw [zetaM1Eta_im, zetaM1Eta_re]
    have hlogx : 0 < Real.log (|x| + 2) := Real.log_pos (by linarith [abs_nonneg x])
    have h1 : 0 ≤ β₀ / Real.log (|x| + 2) := div_nonneg hβ₀pos.le hlogx.le
    linarith
  have hzx_high : (zetaM1Eta R x).re ≤ 1 := by rw [zetaM1Eta_re]; exact hσle
  have hzy_low : -(β₀ / Real.log (|(zetaM1Eta R y).im| + 2)) ≤ (zetaM1Eta R y).re := by
    rw [zetaM1Eta_im, zetaM1Eta_re]
    have hlogy : 0 < Real.log (|y| + 2) := Real.log_pos (by linarith [abs_nonneg y])
    have h1 : 0 ≤ β₀ / Real.log (|y| + 2) := div_nonneg hβ₀pos.le hlogy.le
    linarith
  have hzy_high : (zetaM1Eta R y).re ≤ 1 := by rw [zetaM1Eta_re]; exact hσle
  -- The two `1/ζ` factors.
  have hinvx : ‖(riemannZeta (1 + zetaM1Eta R x))⁻¹‖
      ≤ C * (Real.log (|x| + 2) + 1) := by
    have h := (hCbd (zetaM1Eta R x) hzx_ne hzx_low hzx_high).2.2
    rwa [zetaM1Eta_im] at h
  have hinvy : ‖(riemannZeta (1 + zetaM1Eta R y))⁻¹‖
      ≤ C * (Real.log (|y| + 2) + 1) := by
    have h := (hCbd (zetaM1Eta R y) hzy_ne hzy_low hzy_high).2.2
    rwa [zetaM1Eta_im] at h
  -- The `ζ` numerator: `Re (1 + η x + η y) = 1 + 2/log R ≥ 1 + 1/log R`.
  have hnum_re : (1 + zetaM1Eta R x + zetaM1Eta R y).re = 1 + 2 / Real.log R := by
    simp only [Complex.add_re, Complex.one_re, zetaM1Eta_re]
    ring
  have hnum : ‖riemannZeta (1 + zetaM1Eta R x + zetaM1Eta R y)‖ ≤ Cn := by
    refine hCnb _ ?_
    rw [hnum_re]
    have h2 : (2 : ℝ) / Real.log R = 2 * (1 / Real.log R) := by ring
    rw [h2]
    linarith
  -- The exponential factor: `‖R^{η x + η y}‖ = R^{2/log R} = e²`.
  have hnormR : ‖(R : ℂ) ^ (zetaM1Eta R x + zetaM1Eta R y)‖ = Real.exp 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos]
    have hre : (zetaM1Eta R x + zetaM1Eta R y).re = 2 / Real.log R := by
      simp only [Complex.add_re, zetaM1Eta_re]
      ring
    rw [hre, Real.rpow_def_of_pos hRpos]
    congr 1
    field_simp
  have hnormR_le : ‖(R : ℂ) ^ (zetaM1Eta R x + zetaM1Eta R y)‖ ≤ Real.exp 2 :=
    le_of_eq hnormR
  -- The two quadratic denominators.
  have hmu_x : ‖(zetaM1Eta R x ^ 2)⁻¹‖ ≤ (Real.log R) ^ 2 * (1 + x ^ 2)⁻¹ :=
    norm_inv_sq_zetaM1Eta hR x
  have hmu_y : ‖(zetaM1Eta R y ^ 2)⁻¹‖ ≤ (Real.log R) ^ 2 * (1 + y ^ 2)⁻¹ :=
    norm_inv_sq_zetaM1Eta hR y
  have hinvx_nn : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  have hinvy_nn : 0 ≤ (1 + y ^ 2)⁻¹ := by positivity
  -- Assemble.
  have hfac := zetaM1Kernel_norm_factor R (zetaM1Eta R x) (zetaM1Eta R y)
  calc ‖riemannZeta (1 + zetaM1Eta R x + zetaM1Eta R y)
          / (riemannZeta (1 + zetaM1Eta R x) * riemannZeta (1 + zetaM1Eta R y))
          * (R : ℂ) ^ (zetaM1Eta R x + zetaM1Eta R y)
          / ((zetaM1Eta R x) ^ 2 * (zetaM1Eta R y) ^ 2)‖
      = ‖riemannZeta (1 + zetaM1Eta R x + zetaM1Eta R y)‖
        * ‖(riemannZeta (1 + zetaM1Eta R x))⁻¹‖
        * ‖(riemannZeta (1 + zetaM1Eta R y))⁻¹‖
        * ‖(R : ℂ) ^ (zetaM1Eta R x + zetaM1Eta R y)‖
        * ‖(zetaM1Eta R x ^ 2)⁻¹‖ * ‖(zetaM1Eta R y ^ 2)⁻¹‖ := hfac
    _ ≤ Cn * (C * (Real.log (|x| + 2) + 1)) * (C * (Real.log (|y| + 2) + 1))
        * Real.exp 2 * ((Real.log R) ^ 2 * (1 + x ^ 2)⁻¹)
        * ((Real.log R) ^ 2 * (1 + y ^ 2)⁻¹) := by
        gcongr
    _ = (Real.exp 2 * Cn * C ^ 2 * (Real.log R) ^ 4)
        * ((Real.log (|x| + 2) + 1) / (1 + x ^ 2))
        * ((Real.log (|y| + 2) + 1) / (1 + y ^ 2)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring

end Commons.NumberTheory.Zeta
