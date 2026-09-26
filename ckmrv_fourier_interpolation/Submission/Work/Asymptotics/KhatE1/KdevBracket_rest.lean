import Mathlib
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs
import Submission.Work.Asymptotics.KhatE1.KdevE2fun_funnel
import Submission.Work.Asymptotics.KhatE1Core.Kdev8_matching_bridge
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Asymptotics.KhatE1R.BracketTail

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

/-!
# The sharp funnel remainder of the bracket, and its cleared form

`Kdev8Bracket ℓ τ z = 2 · KdevRem ℓ τ z` is the explicit bracket of
`KhatE1Core.Kdev8_matching_bridge`, and `KdevE2 ℓ τ z` is the `E(z)²`-coefficient of the
funnel deviation `K̂ - Ĝ` (`KhatE1.KdevE2Defs`).  The requested statement bounds the residual

  `Kdev8Bracket ℓ τ z - 2 · KdevE2 ℓ τ z · E(z)²`      (`E(z) = Ept z`)

by `C ‖q(τ)‖ (scale τ)^N (1+t)^M e^{-2πt}` on the funnel strip `-1 ≤ Re z ≤ 2`,
`t = Im z ≥ Im τ + 1`.

This file

* proves the *uniform divisor bound* `‖Δ(τ) Sh τ z‖ ≥ (1/32)‖q(τ)‖` on that strip
  (`Sh τ z = E₄(z)³ - Δ(z)j(τ) = -Δ(z)(j(τ) - j(z))`); the sibling
  `Work.Asymptotics.funnel_Sh_ge` gives `‖Sh‖ ≥ 1/16` only on the imaginary axis, and the
  strip version is what the clearing reduction below needs;
* records the *reduction* `KdevBracket_rest_of_cleared`: it suffices to prove the bound for
  the **cleared** expression `Δ(τ) Sh τ z ( Kdev8Bracket - 2 KdevE2 E(z)² )` with the
  right-hand side `C‖q(τ)‖²‖E(z)‖²(scale τ)^N(1+t)^M`.  The point is that the cleared
  expression has no denominators left (`Sh`, `Δ(τ)`, `Δ(z)`, `j(τ) - j(z)` are all cleared),
  so the bound is a statement about its double cusp expansion in `(q(τ), q(z))` — the form in
  which the CKMRV paper proves its kernel estimates (Lemma `lem:boundsonKnew`).  Numerically
  `‖Δ(τ) Sh τ z (Kdev8Bracket - 2 KdevE2 E(z)²)‖ / (‖q(τ)‖²‖E(z)‖²) ≤ 28.3` on the whole
  strip, uniformly in `Re z` (dps 200), so the cleared statement holds with `N = M = 0`.
-/

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

/-- **The reduction to the cleared form.**  If the *cleared* bracket residual,
`Δ(τ) Sh τ z (Kdev8Bracket - 2 KdevE2 E(z)²)`, is `O(‖q(τ)‖²‖E(z)‖²(scale τ)^N(1+t)^M)` on
the funnel strip, then the requested statement holds.

Indeed `E(z)²` has norm `e^{-2πt}`, and dividing by the uniform lower bound
`‖Δ(τ) Sh τ z‖ ≥ (1/32)‖q(τ)‖` of `Delta_mul_Sh_ge_strip` turns the `‖q(τ)‖²` of the cleared
bound into the `‖q(τ)‖` of the target. -/
theorem KdevBracket_rest_of_cleared (ℓ : Work.Kernels.LogLambdaData)
    (h : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
            (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
              - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Residues.Ept z‖ ^ 2
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨32 * C + 1, N, M, by positivity, hN, hM, ?_⟩
  intro τ z t hτ ht h1 h2 hzim
  have hcl := hb τ z t hτ ht h1 h2 hzim
  have hdiv := Delta_mul_Sh_ge_strip τ z t hτ ht hzim
  have hqpos : 0 < ‖Work.Kernels.qParamFun τ‖ := by
    have h := Work.Asymptotics.norm_qParamFun τ
    rw [h]
    exact Real.exp_pos _
  have hEsq : ‖Work.Residues.Ept z‖ ^ 2 = Real.exp (-(2 * Real.pi * t)) := by
    rw [Work.Residues.norm_Ept, hzim]
    rw [show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
  -- `‖T‖ = ‖Δ τ · Sh · T‖ / (‖Δ τ‖ ‖Sh‖)`
  have hden : (1 / 32 : ℝ) * ‖Work.Kernels.qParamFun τ‖
      ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.Compact.Sh τ z‖ := by
    rw [← norm_mul]; exact hdiv
  have hdenpos : 0 < (1 / 32 : ℝ) * ‖Work.Kernels.qParamFun τ‖ :=
    mul_pos (by norm_num) hqpos
  have hden0 : (0 : ℝ) < ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.Compact.Sh τ z‖ :=
    lt_of_lt_of_le hdenpos hden
  have hdenne : ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.Compact.Sh τ z‖ ≠ 0 :=
    ne_of_gt hden0
  have hsplit : ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
        - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
      = (‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
            (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
              - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)‖)
        / (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.Compact.Sh τ z‖) := by
    simp only [norm_mul]
    rw [show ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.Compact.Sh τ z‖ * ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
        = (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.Compact.Sh τ z‖)
          * ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ from by ring]
    exact (mul_div_cancel_left₀ _ hdenne).symm
  rw [hsplit]
  -- divide the cleared bound
  have hstep : ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
        (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
          - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)‖
      / (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.Compact.Sh τ z‖)
      ≤ (C * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Residues.Ept z‖ ^ 2
            * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
        / ((1 / 32 : ℝ) * ‖Work.Kernels.qParamFun τ‖) := by
    have hnumC : (0 : ℝ) ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 2
        * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) (sq_nonneg _))
        (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N))
        (Real.rpow_nonneg (by have := hτ.2; linarith) M)
    exact div_le_div₀ hnumC hcl hdenpos hden
  refine le_trans hstep ?_
  have hqne : ‖Work.Kernels.qParamFun τ‖ ≠ 0 := ne_of_gt hqpos
  have hsimp : (C * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Residues.Ept z‖ ^ 2
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
        / ((1 / 32 : ℝ) * ‖Work.Kernels.qParamFun τ‖)
      = 32 * C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(2 * Real.pi * t)) := by
    rw [hEsq]
    rw [div_eq_iff (ne_of_gt (mul_pos (by norm_num) hqpos))]
    ring
  rw [hsimp]
  have hsN : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N
  have ht0 : (0 : ℝ) ≤ 1 + t := by have := hτ.2; linarith
  have hMt : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg ht0 M
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := Real.exp_nonneg _
  have hbase : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hsN) hMt) hE0
  have hC0 : (0 : ℝ) ≤ C := hC.le
  calc 32 * C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * Real.exp (-(2 * Real.pi * t))
      = (32 * C) * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t))) := by ring
    _ ≤ (32 * C + 1) * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t))) :=
        mul_le_mul_of_nonneg_right (by linarith) hbase
    _ = (32 * C + 1) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * Real.exp (-(2 * Real.pi * t)) := by ring

/-- **The reduction to the sharp statement for `KdevRem`.**

If the leading-term-free funnel deviation `KdevRem ℓ τ z = K̂ - Ĝ - (E1combo8/(288π))E(z)` is
`O(‖q(τ)‖ (scale τ)^N (1+t)^M e^{-2πt})` on the funnel strip — the statement exploited (and, via
`Kdev8Bracket_eq_two_KdevRem`, equivalent to the requested one) by the whole funnel chapter —
then the requested statement for the bracket holds: on the strip
`Kdev8Bracket = 2 · KdevRem`, and the subtracted `E(z)²`-coefficient is controlled by the
(axiom-clean) bound `KdevE2fun_funnel` on `KdevE2`. -/
theorem KdevBracket_rest_of_sharp (ℓ : Work.Kernels.LogLambdaData)
    (h : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1.KdevRem ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := h
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := KdevE2fun_funnel ℓ
  refine ⟨2 * (C1 + C2) + 1, max N1 N2, max M1 M2, by linarith [hC1, hC2],
    le_max_of_le_left hN1, le_max_of_le_left hM1, ?_⟩
  intro τ z t hF ht h1 h2 hzim
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hs1
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have ht0 : (0 : ℝ) ≤ 1 + t := by linarith [hF.2, ht]
  have hE1t : (1 : ℝ) ≤ 1 + t := by linarith [hF.2, ht]
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := Real.exp_nonneg _
  have hEsq : ‖Work.Residues.Ept z‖ ^ 2 = Real.exp (-(2 * Real.pi * t)) := by
    rw [Work.Residues.norm_Ept, hzim]
    rw [show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
  -- the divisor is nonzero on the strip
  have hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0 := by
    intro h0
    have hge := funnel_Sh_ge_strip τ z t hF ht hzim
    rw [h0, norm_zero] at hge
    norm_num at hge
  have hJ : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro h0'
    refine hSh ?_
    have hD : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
    rw [Work.Asymptotics.Compact.Sh, h0']
    rw [← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z]
    ring
  rw [Work.Asymptotics.KhatE1Core.Kdev8Bracket_eq_two_KdevRem ℓ τ z hJ hSh]
  -- bounds for the two terms, with exponent-inflated factors
  have hN1 : (Work.Kernels.scale τ) ^ N1 ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hN2 : (Work.Kernels.scale τ) ^ N2 ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hM1 : (1 + t) ^ M1 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le hE1t (le_max_left _ _)
  have hM2 : (1 + t) ^ M2 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le hE1t (le_max_right _ _)
  have hsN0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (max N1 N2) := Real.rpow_nonneg hs0 _
  have hMt0 : (0 : ℝ) ≤ (1 + t) ^ (max M1 M2) := Real.rpow_nonneg ht0 _
  set S : ℝ := ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
      * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t)) with hSdef
  have hS0 : (0 : ℝ) ≤ S := by
    rw [hSdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hq0 hsN0) hMt0) hE0
  have e1 : ‖Work.Asymptotics.KhatE1.KdevRem ℓ τ z‖ ≤ C1 * S := by
    have hb := hb1 τ z t hF ht h1 h2 hzim
    refine le_trans hb ?_
    rw [hSdef]
    have hN1' : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N1 := Real.rpow_nonneg hs0 _
    have hM1' : (0 : ℝ) ≤ (1 + t) ^ M1 := Real.rpow_nonneg ht0 _
    have h1' : C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N1
        ≤ C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2) :=
      mul_le_mul_of_nonneg_left hN1 (by positivity)
    have h2' : C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ M1
        ≤ C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2) :=
      mul_le_mul_of_nonneg_left hM1 (by positivity)
    have h3' : C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2)
        = C1 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2)) := by ring
    calc C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
          * Real.exp (-(2 * Real.pi * t))
        = (C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N1
            * (1 + t) ^ M1) * Real.exp (-(2 * Real.pi * t)) := by ring
      _ ≤ (C1 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2)) * Real.exp (-(2 * Real.pi * t)) := by
            refine mul_le_mul_of_nonneg_right ?_ hE0
            exact le_trans (mul_le_mul_of_nonneg_right h1' hM1') h2'
      _ = C1 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))) := by ring
  have e2 : ‖2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
      ≤ 2 * C2 * S := by
    have hb := hb2 τ z t hF ht h1 h2 hzim
    have hnorm : ‖2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
        = 2 * (‖Work.Asymptotics.KhatE1.KdevE2 ℓ τ z‖ * Real.exp (-(2 * Real.pi * t))) := by
      rw [norm_mul, norm_mul, norm_pow, hEsq, show ‖(2 : ℂ)‖ = 2 by norm_num]
      ring
    rw [hnorm]
    have hstep : ‖Work.Asymptotics.KhatE1.KdevE2 ℓ τ z‖ * Real.exp (-(2 * Real.pi * t))
        ≤ (C2 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2)
            * Real.exp (-(2 * Real.pi * t)) :=
      mul_le_mul_of_nonneg_right hb hE0
    have hN2' : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N2 := Real.rpow_nonneg hs0 _
    have hM2' : (0 : ℝ) ≤ (1 + t) ^ M2 := Real.rpow_nonneg ht0 _
    have h1 : C2 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N2
        ≤ C2 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2) :=
      mul_le_mul_of_nonneg_left hN2 (by positivity)
    have h2 : C2 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ M2
        ≤ C2 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2) :=
      mul_le_mul_of_nonneg_left hM2 (by positivity)
    have h3 : (C2 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2)
          * Real.exp (-(2 * Real.pi * t))
        ≤ (C2 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2)) * Real.exp (-(2 * Real.pi * t)) := by
      refine mul_le_mul_of_nonneg_right ?_ hE0
      exact le_trans (mul_le_mul_of_nonneg_right h1 hM2') h2
    have hfin : 2 * (C2 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2) * Real.exp (-(2 * Real.pi * t))) = 2 * C2 * S := by
      rw [hSdef]; ring
    refine le_trans (mul_le_mul_of_nonneg_left (le_trans hstep h3) (by norm_num : (0:ℝ) ≤ 2)) ?_
    rw [hfin]

  -- assemble
  have htri : ‖2 * Work.Asymptotics.KhatE1.KdevRem ℓ τ z
        - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
      ≤ ‖2 * Work.Asymptotics.KhatE1.KdevRem ℓ τ z‖
        + ‖2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ :=
    norm_sub_le _ _
  have h2R : ‖2 * Work.Asymptotics.KhatE1.KdevRem ℓ τ z‖ = 2 * ‖Work.Asymptotics.KhatE1.KdevRem ℓ τ z‖ := by
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
  refine le_trans htri ?_
  rw [h2R]
  refine le_trans (add_le_add (mul_le_mul_of_nonneg_left e1 (by norm_num : (0:ℝ) ≤ 2)) e2) ?_
  have hEq : (2 * (C1 + C2) + 1) * ‖Work.Kernels.qParamFun τ‖
        * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        * Real.exp (-(2 * Real.pi * t)) = (2 * (C1 + C2) + 1) * S := by
    rw [hSdef]; ring
  rw [hEq]
  have hcomb : 2 * (C1 * S) + 2 * C2 * S = (2 * C1 + 2 * C2) * S := by ring
  rw [hcomb]
  exact mul_le_mul_of_nonneg_right (by linarith) hS0

theorem KdevBracket_rest (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  -- The statement is *exactly* the sharp funnel tail of the `d = 8` bracket.  The derivation
  -- is the one of the `KhatE1Sharp` chapter, re-wired so that it does not import this file
  -- (see `Submission/Work/Asymptotics/KhatE1R/`): `Wres = Kdev8Bracket - 2·KdevE2·E(z)²` is
  -- doubly cleared, `Δ(τ)·(Δ(τ)·Sh(τ,z)·Wres) = WresPoly + WresDev` is bounded in
  -- `WresPolyPol_bound`, `Kdev8WresPolyDevBound` and `WresDevBound`, and the lower bounds
  -- `‖Δ(τ)‖ ≥ ‖q(τ)‖/2`, `‖Δ(τ)Sh(τ,z)‖ ≥ ‖q(τ)‖/32` (the second is copied as
  -- `KhatE1RDiv.Delta_mul_Sh_ge_strip`) convert the cleared estimate into the stated one.
  exact Work.Asymptotics.KhatE1RAssembly.KdevBracket_rest_R ℓ

end Work.Asymptotics.KhatE1
