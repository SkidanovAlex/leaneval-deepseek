import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Work.ZeroDensity.Ingham.mkOneNormBound
import Submission.Work.ZeroDensity.Ingham.cpowOneSubNormBound
import Submission.Work.ZeroDensity.Ingham.gammaOneSubNormBound
import Submission.Work.ZeroDensity.Ingham.residueArithCore

set_option autoImplicit false
open scoped Classical BigOperators
open MeasureTheory

namespace Work.ZeroDensity.Ingham

/-- (Put this in namespace `Work.ZeroDensity.Ingham`, with `open scoped Classical BigOperators` and
`open MeasureTheory`; import `Submission.Work.ZeroDensity.Ingham.Defs` and
`Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs`.)

**The residue of the `ζ`-pole is small.**  There is `A₀ ≥ 6` such that for every `A ≥ A₀`, every
`T ≥ 2`, all `K, Y` with `1 ≤ K ≤ T`, `1 ≤ Y ≤ T²`, and every `ρ` with `1/2 ≤ Re ρ ≤ 1`,
`|Im ρ| ≤ T` and `(log (A T))² ≤ |Im ρ|`,

`‖residueTerm K Y ρ‖ = ‖Γ(1-ρ) Y^{1-ρ} M_K(1)‖ ≤ 1/20`.

Pure estimate.  Write `β = Re ρ ∈ [1/2,1]`, `γ = Im ρ`, so `|γ| ≥ (log (A T))² ≥ 1`.  Bounds:
(i) `Y^{1-β} ≤ Y^{1/2} ≤ T` (as `β ≥ 1/2`, `1 ≤ Y ≤ T²`);
(ii) `‖M_K(1)‖ = ‖Σ_{n≤K} μ(n)n^{-1}‖ ≤ Σ_{n ≤ K} 1/n ≤ 1 + log K ≤ 1 + log T` (each `|μ(n)| ≤ 1`;
use `ArithmeticFunction.abs_moebius_le_one` and a harmonic-sum estimate such as
`Real.log_le_sub_one_of_pos`/integral comparison);
(iii) `‖Γ(1-ρ)‖`: with `z = 1-ρ = (1-β) + i(-γ)`, for `β < 1` the real part `1-β` lies in `(0,1)`
and `|Im z| = |γ| ≥ 1`, so `Commons.Analysis.Complex.Gamma_vertical_norm_bounds.gamma_strip_upper`
(with `u = 1-β`, `t = -γ`) gives `‖Γ z‖ ≤ K6 (1+|γ|)^6 exp(-(π/2)|γ|)` for the explicit constant
`K6` of that file; for `β = 1` use `Complex.Gamma_add_one` (`Γ(iγ) = Γ(1+iγ)/(iγ)` for `γ ≠ 0`) and
`gamma_strip_upper` at real part `1`, giving the same bound up to the factor `(1+|γ|)/|γ| ≤ 2`.
Hence `‖residueTerm‖ ≤ 2 K6 (1+T)^7 exp(-(π/2)(log (A T))²)` using `|γ| ≤ T`, and choosing `A₀` large
(any `A₀ ≥ e^10` is plenty) makes this `≤ 1/20` for all `T ≥ 2`, because
`(π/2)(log (A T))² ≥ 8 log T` dominates the polynomial factor `(1+T)^7`. -/
theorem residueTermSmall : ∃ A₀ : ℝ, 6 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ T : ℝ, 2 ≤ T →
    ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → (K : ℝ) ≤ T → 1 ≤ Y → Y ≤ T ^ 2 →
    ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
      (Real.log (A * T)) ^ 2 ≤ |ρ.im| → ‖residueTerm K Y ρ‖ ≤ 1 / 20 := by
  refine ⟨Real.exp 300, ?_, ?_⟩
  · have h := Real.add_one_le_exp (300 : ℝ)
    linarith
  · intro A hA T hT K Y hK1 hKT hY1 hYT ρ hβ1 hβ2 hγim hlog
    have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos 300) hA
    have hTpos : 0 < T := by linarith
    have hlogA : 300 ≤ Real.log A := by
      have h := Real.log_le_log (Real.exp_pos 300) hA
      rwa [Real.log_exp] at h
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hlogAT : Real.log (A * T) = Real.log A + Real.log T :=
      Real.log_mul (ne_of_gt hApos) (ne_of_gt hTpos)
    have h300 : (300 : ℝ) ≤ Real.log (A * T) := by rw [hlogAT]; linarith
    have hγ1 : 1 ≤ |ρ.im| := by
      have h1 : (1 : ℝ) ≤ (Real.log (A * T)) ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 300) h300 2
        norm_num at h
        linarith
      linarith
    have hΓ := gammaOneSubNormBound ρ hβ1 hβ2 hγ1
    have hYc := cpowOneSubNormBound T Y ρ (by linarith) hY1 hYT hβ1
    have hMK : ‖MK K 1‖ ≤ 1 + Real.log T := by
      have h := mkOneNormBound K
      have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
      have hlogKT : Real.log (K : ℝ) ≤ Real.log T := Real.log_le_log hKpos hKT
      linarith
    have hP : (1 + |ρ.im|) ^ 20 ≤ (1 + T) ^ 20 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 20
      have := abs_nonneg ρ.im
      linarith
    have hE : Real.exp (-(Real.pi / 2) * |ρ.im|) ≤
        Real.exp (-(Real.pi / 2) * (Real.log (A * T)) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
      have h := mul_le_mul_of_nonneg_left hlog hpi2
      linarith
    have hK11 : (0 : ℝ) < Commons.Analysis.Complex.K11 := Commons.Analysis.Complex.K11_pos
    have hB1 : 0 ≤ Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * |ρ.im|) *
        (1 + |ρ.im|) ^ 20 :=
      mul_nonneg (mul_nonneg hK11.le (Real.exp_nonneg _)) (pow_nonneg (by positivity) 20)
    have hstep1 : ‖Complex.Gamma (1 - ρ)‖ * ‖(Y : ℂ) ^ (1 - ρ)‖ ≤
        (Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * |ρ.im|) *
          (1 + |ρ.im|) ^ 20) * T :=
      mul_le_mul hΓ hYc (norm_nonneg _) hB1
    have hstep2 : ‖Complex.Gamma (1 - ρ)‖ * ‖(Y : ℂ) ^ (1 - ρ)‖ * ‖MK K 1‖ ≤
        (Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * |ρ.im|) *
          (1 + |ρ.im|) ^ 20) * T * (1 + Real.log T) :=
      mul_le_mul hstep1 hMK (norm_nonneg _) (mul_nonneg hB1 hTpos.le)
    have hEE : Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * |ρ.im|) *
          (1 + |ρ.im|) ^ 20 ≤
        Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * (Real.log (A * T)) ^ 2) *
          (1 + T) ^ 20 := by
      calc Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * |ρ.im|) *
              (1 + |ρ.im|) ^ 20
          = (Commons.Analysis.Complex.K11 * (1 + |ρ.im|) ^ 20) *
              Real.exp (-(Real.pi / 2) * |ρ.im|) := by ring
        _ ≤ (Commons.Analysis.Complex.K11 * (1 + T) ^ 20) *
              Real.exp (-(Real.pi / 2) * |ρ.im|) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hK11.le)
              (Real.exp_nonneg _)
        _ ≤ (Commons.Analysis.Complex.K11 * (1 + T) ^ 20) *
              Real.exp (-(Real.pi / 2) * (Real.log (A * T)) ^ 2) :=
            mul_le_mul_of_nonneg_left hE
              (mul_nonneg hK11.le (pow_nonneg (by positivity) 20))
        _ = Commons.Analysis.Complex.K11 *
              Real.exp (-(Real.pi / 2) * (Real.log (A * T)) ^ 2) * (1 + T) ^ 20 := by ring
    have hstep3 : (Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * |ρ.im|) *
          (1 + |ρ.im|) ^ 20) * T * (1 + Real.log T) ≤
        Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * (Real.log (A * T)) ^ 2) *
          (1 + T) ^ 20 * T * (1 + Real.log T) := by
      have h1 : (Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * |ρ.im|) *
            (1 + |ρ.im|) ^ 20) * T ≤
          (Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * (Real.log (A * T)) ^ 2) *
            (1 + T) ^ 20) * T :=
        mul_le_mul_of_nonneg_right hEE hTpos.le
      exact mul_le_mul_of_nonneg_right h1 (by linarith)
    calc ‖residueTerm K Y ρ‖
        = ‖Complex.Gamma (1 - ρ)‖ * ‖(Y : ℂ) ^ (1 - ρ)‖ * ‖MK K 1‖ := by
          rw [residueTerm, norm_mul, norm_mul]
      _ ≤ (Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * |ρ.im|) *
            (1 + |ρ.im|) ^ 20) * T * (1 + Real.log T) := hstep2
      _ ≤ Commons.Analysis.Complex.K11 *
            Real.exp (-(Real.pi / 2) * (Real.log (A * T)) ^ 2) *
            (1 + T) ^ 20 * T * (1 + Real.log T) := hstep3
      _ ≤ 1 / 20 := residueArithCore A T hA hT

end Work.ZeroDensity.Ingham
