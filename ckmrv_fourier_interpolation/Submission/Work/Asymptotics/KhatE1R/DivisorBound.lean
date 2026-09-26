import Mathlib
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.FunnelNumerics.E4_funnel_bounds

/-! Cycle-free copy of the divisor lemmas of `KhatE1/KdevBracket_rest.lean`. -/

namespace Work.Asymptotics.KhatE1RDiv

open UpperHalfPlane

/-- **The uniform divisor bound on the funnel strip.**

For `τ` in the funnel and `z` in the strip `-1 ≤ Re z ≤ 2` with `Im z = t ≥ Im τ + 1`, the
function `Sh τ z = E₄(z)³ - Δ(z)j(τ)` is bounded below by the absolute constant `1/16`
(this is `Work.Asymptotics.funnel_Sh_ge` with the hypothesis `Re z = 0` removed: every
ingredient, `‖Δ(z)‖ ≤ 2e^{-2πt}`, `‖j(τ)‖ ≤ (27/4)e^{2π Im τ}` and
`1/2 ≤ ‖E₄(z)‖` for `Im z ≥ 3`, is independent of `Re z`). -/
theorem funnel_Sh_ge_strip (τ z : UpperHalfPlane) (t : ℝ) (hτ : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) (hz : z.im = t) :
    (1 / 16 : ℝ) ≤ ‖Work.Asymptotics.Compact.Sh τ z‖ := by
  have hτ2 : 2 ≤ τ.im := hτ.2
  have ht3 : 3 ≤ t := by linarith
  have hz3 : 3 ≤ z.im := by rw [hz]; linarith
  -- `‖Δ(z) j(τ)‖ ≤ 1/16`
  have hDz : ‖Work.Kernels.DeltaFun z‖ ≤ 2 * Real.exp (-(2 * Real.pi * t)) := by
    have h := Work.Asymptotics.DeltaFun_upper_sharp z (by rw [hz]; linarith)
    rwa [hz] at h
  have hjτ : ‖Work.Kernels.jInvariantFun τ‖ ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by
    have hΔlow : (1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ :=
      Work.FunnelNumerics.Delta_funnel_bounds.1 τ hτ2
    have hE4b : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 :=
      Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ
    have hnum : ‖Work.Kernels.E4Fun τ ^ 3‖ ≤ (3 / 2) ^ 3 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hE4b 3
    have hqexp : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
      Work.Asymptotics.norm_qParamFun τ
    have hpos : 0 < (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)) :=
      mul_pos (by norm_num) (Real.exp_pos _)
    have hmain : ‖Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ‖
        ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by
      rw [norm_div]
      have hinv : (‖Work.Kernels.DeltaFun τ‖)⁻¹
          ≤ ((1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)))⁻¹ := by
        rw [← hqexp]
        exact inv_anti₀ (mul_pos (by norm_num) (by rw [hqexp]; exact Real.exp_pos _)) hΔlow
      have hrec : ((1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)))⁻¹
          = 2 * Real.exp (2 * Real.pi * τ.im) := by
        rw [Real.exp_neg]
        field_simp
      rw [hrec] at hinv
      calc ‖Work.Kernels.E4Fun τ ^ 3‖ / ‖Work.Kernels.DeltaFun τ‖
          = ‖Work.Kernels.E4Fun τ ^ 3‖ * (‖Work.Kernels.DeltaFun τ‖)⁻¹ := by ring
        _ ≤ (3 / 2) ^ 3 * (2 * Real.exp (2 * Real.pi * τ.im)) :=
            mul_le_mul hnum hinv (by positivity) (by positivity)
        _ = (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by norm_num; ring
    simpa [Work.Kernels.jInvariantFun] using hmain
  have hρ : ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖ ≤ (1 / 16 : ℝ) := by
    rw [norm_mul]
    have hcombi : (2 * Real.exp (-(2 * Real.pi * t))) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im))
        = (27 / 2) * Real.exp (-(Real.pi * (t - τ.im))) ^ 2 := by
      rw [show (2 * Real.exp (-(2 * Real.pi * t))) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im))
          = (27 / 2) * (Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * τ.im)) by ring]
      rw [← Real.exp_add]
      rw [show -(2 * Real.pi * t) + 2 * Real.pi * τ.im
        = -(Real.pi * (t - τ.im)) + -(Real.pi * (t - τ.im)) by ring, Real.exp_add]
      ring
    have hmul : ‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.jInvariantFun τ‖
        ≤ (2 * Real.exp (-(2 * Real.pi * t))) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) :=
      mul_le_mul hDz hjτ (norm_nonneg _) (by positivity)
    rw [hcombi] at hmul
    refine le_trans hmul ?_
    have hsq : Real.exp (-(Real.pi * (t - τ.im))) ^ 2
        = Real.exp (-(2 * Real.pi * (t - τ.im))) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [hsq]
    have h1 : (1 : ℝ) ≤ t - τ.im := by linarith
    have h2 : Real.exp (-(2 * Real.pi * (t - τ.im))) ≤ Real.exp (-(2 * Real.pi)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, h1])
    have h3 : (27 / 2 : ℝ) * Real.exp (-(2 * Real.pi)) ≤ 1 / 16 := by
      rw [Real.exp_neg,
        show (27 / 2 : ℝ) * (Real.exp (2 * Real.pi))⁻¹
          = 27 / (2 * Real.exp (2 * Real.pi)) by ring,
        div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.exp (2 * Real.pi))]
      nlinarith [Work.Asymptotics.ft_exp_two_pi_ge]
    linarith [h2, h3]
  -- `1/8 ≤ ‖E₄(z)³‖`
  have hE4z : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ :=
    Work.FunnelNumerics.E4_funnel_bounds.2 z hz3
  have hE4z3 : (1 / 8 : ℝ) ≤ ‖Work.Kernels.E4Fun z ^ 3‖ := by
    rw [norm_pow]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hE4z 3
    norm_num at h
    linarith
  rw [show Work.Asymptotics.Compact.Sh τ z
      = Work.Kernels.E4Fun z ^ 3 - Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
    from rfl]
  have h := abs_norm_sub_norm_le (Work.Kernels.E4Fun z ^ 3)
    (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ)
  have h2 : ‖Work.Kernels.E4Fun z ^ 3‖
      - ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖
      ≤ ‖Work.Kernels.E4Fun z ^ 3
          - Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖ :=
    le_trans (le_abs_self _) h
  linarith [h2, hE4z3, hρ]

/-- **The lower bound for the clearing factor `Δ(τ) Sh τ z` on the funnel strip.**
Together with the Δ-lower bound `(1/2)‖q(τ)‖ ≤ ‖Δ(τ)‖` this gives
`‖Δ(τ) Sh τ z‖ ≥ (1/32)‖q(τ)‖`. -/
theorem Delta_mul_Sh_ge_strip (τ z : UpperHalfPlane) (t : ℝ)
    (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t) (hz : z.im = t) :
    (1 / 32 : ℝ) * ‖Work.Kernels.qParamFun τ‖
      ≤ ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z‖ := by
  have hτ2 : 2 ≤ τ.im := hτ.2
  have hD : (1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ :=
    Work.FunnelNumerics.Delta_funnel_bounds.1 τ hτ2
  have hS : (1 / 16 : ℝ) ≤ ‖Work.Asymptotics.Compact.Sh τ z‖ :=
    funnel_Sh_ge_strip τ z t hτ ht hz
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  rw [norm_mul]
  have h32 : (1 / 32 : ℝ) * ‖Work.Kernels.qParamFun τ‖
      = ((1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖) * (1 / 16) := by ring
  rw [h32]
  exact mul_le_mul hD hS (by norm_num) (by positivity)


end Work.Asymptotics.KhatE1RDiv
