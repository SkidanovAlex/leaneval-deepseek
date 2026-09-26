import Mathlib
import Submission.Work.CKFinal.LineDecay.Ncusp8Clean
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Kernels.Kernels

namespace Work.CKFinal.LineDecay

noncomputable section

/-- The elementary identification of the two writings of the cusp factor:
`e^{-π(2y+t)}/(e^{-2πt} + e^{-2πy}) = e^{-πt}/(1 + e^{2π(y-t)})`, with the factors `C₂, P, Q`
carried along. -/
private lemma tail_arith (C₂ c P Q y t : ℝ) :
    C₂ * P * Q * Real.exp (-(Real.pi * (2 * y + t))) /
        (c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * y))))
      = (C₂ / c) * P * Q * (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t)))) := by
  have hident : Real.exp (-(Real.pi * (2 * y + t))) /
        (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * y)))
      = Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))) := by
    have h1 : Real.exp (-(Real.pi * (2 * y + t)))
        = Real.exp (-(2 * Real.pi * y)) * Real.exp (-(Real.pi * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (2 * Real.pi * (y - t))
        = Real.exp (2 * Real.pi * y) * Real.exp (-(2 * Real.pi * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-(2 * Real.pi * y)) * Real.exp (2 * Real.pi * y) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    rw [div_eq_div_iff (by positivity) (by positivity), h1, h2, mul_add, mul_one]
    linear_combination (Real.exp (-(Real.pi * t)) * Real.exp (-(2 * Real.pi * t))) * h3
  have hfac : C₂ * P * Q * Real.exp (-(Real.pi * (2 * y + t))) /
        (c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * y))))
      = (C₂ * P * Q / c) * (Real.exp (-(Real.pi * (2 * y + t))) /
          (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * y)))) := by
    rw [div_mul_div_comm]
  rw [hfac, hident]
  ring


/-- **The `K₋` half of the tail bound on the lines `Re τ = ±1/2`.**

Assume the CKMRV divisor lower bound `hD` on the two lines:
`c (e^{-2π t} + e^{-2π Im τ}) ≤ ‖Δ(τ)Δ(it)(j(τ) - j(it))‖` for `Re τ = ±1/2`, `Im τ ≥ Y₀ ≥ 1`,
`t ≥ 1`.  Then, for those same `τ, t`, the slashed kernel on the line satisfies

`t² ‖K₋^{(8)}(τ, S·(i t))‖ ≤ C (1+‖τ‖)^A (1+t)^A · e^{-πt}/(1 + e^{2π(Im τ - t)})`.

Route: `Work.CKFinal.LineDecay.ncusp8_decay_bound ℓ` (a clean re-proof of
`Work.CKFinal.Ncusp8_Delta_bound`, see `Submission/Work/CKFinal/LineDecay/Ncusp8Clean.lean`)
gives `‖Δ(τ)·Ncusp ℓ 8 τ z‖ ≤ C₂(1+‖τ‖)^{A₂}(1+‖z‖)^{A₂} e^{-π(2 Im τ + Im z)}` for
`Im τ, Im z ≥ 1/3`; `Work.Asymptotics.Ncusp_ident ℓ 8 (Or.inl rfl) τ z hne` gives
`Ncusp ℓ 8 τ z = Δ(z)(j τ - j z)·(z² K₋^{(8)}(τ, S·z))` (note `-(2 - 8/2) = 2`); `hD`
lower-bounds the divisor `Δ(τ)Δ(z)(jτ-jz)`, and
`e^{-2π Im τ}e^{-πt}/(e^{-2πt}+e^{-2π Im τ}) = e^{-πt}/(1+e^{2π(Im τ - t)})`.  The hypothesis
`jInvariantFun τ ≠ jInvariantFun (i t)` needed by `Ncusp_ident` follows from `hD` (its
right-hand side is `> 0`).

IMPORTANT -- import constraint: do NOT import `Submission.Work.Asymptotics.KMinus_slash_bound_half`,
`...KMinusCuspBallBound`, `...KernelBoundAux`, `...KPlus_axis_compact`, `...KMinus_axis_compact`,
or `...MiddleRange.Main`: they pull in both `Work.Asymptotics.KernelBoundAux` and
`Work.Asymptotics.MiddleRange.Basic`, which both define `Work.Asymptotics.continuous_scale` and so
cannot coexist in one Lean environment (the requester's module needs `MiddleRange.Basic`). -/
theorem KMinus_tail_lines (ℓ : Work.Kernels.LogLambdaData) (c Y₀ : ℝ) (hc : 0 < c) (hY : 1 ≤ Y₀)
    (hD : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im → 1 ≤ t →
        c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
          ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
              (Work.Kernels.jInvariantFun τ
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im → 1 ≤ t →
        t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ
              (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + t) ^ A *
              (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by
  obtain ⟨C₂, A₂, hC₂, hA₂, hb⟩ := ncusp8_decay_bound ℓ
  refine ⟨C₂ / c, A₂, div_nonneg hC₂.le hc.le, hA₂, ?_⟩
  intro τ t ht hline hYτ h1t
  set z : UpperHalfPlane := Work.Kernels.imagAxis t ht with hz
  have hzim : z.im = t := by rw [hz]; simp [Work.Kernels.imagAxis]
  have hznorm : ‖(z : ℂ)‖ = t := by
    rw [hz]
    rw [show ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg ht.le]
  have hτ13 : (1 : ℝ) / 3 ≤ τ.im := by
    have := le_trans hY hYτ; linarith
  have hz13 : (1 : ℝ) / 3 ≤ z.im := by rw [hzim]; linarith
  have hDinst : c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
      ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    rw [hz]; exact hD τ t ht hline hYτ h1t
  have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro h
    have hpos : 0 < c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im))) := by
      positivity
    have hlt : 0 < ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
      lt_of_lt_of_le hpos hDinst
    rw [h, sub_self, mul_zero, norm_zero] at hlt
    exact lt_irrefl 0 hlt
  have hsplit : ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 8 τ z‖
      = (t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)‖)
        * ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    rw [Work.Asymptotics.Ncusp_ident ℓ 8 (Or.inl rfl) τ z hne]
    norm_num
    rw [hznorm]
    ring
  have hNc := hb τ z hτ13 hz13
  rw [hsplit, hznorm, hzim] at hNc
  have hden : 0 < c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im))) := by
    positivity
  have hkey : (t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)‖) *
        (c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im))))
      ≤ C₂ * (1 + ‖(τ : ℂ)‖) ^ A₂ * (1 + t) ^ A₂ *
          Real.exp (-(Real.pi * (2 * τ.im + t))) :=
    le_trans (mul_le_mul_of_nonneg_left hDinst (by positivity)) hNc
  have hstep : t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)‖
      ≤ C₂ * (1 + ‖(τ : ℂ)‖) ^ A₂ * (1 + t) ^ A₂ *
          Real.exp (-(Real.pi * (2 * τ.im + t))) /
          (c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))) := by
    rw [le_div_iff₀ hden]
    exact hkey
  refine le_trans hstep (le_of_eq ?_)
  exact tail_arith C₂ c ((1 + ‖(τ : ℂ)‖) ^ A₂) ((1 + t) ^ A₂) τ.im t

end

end Work.CKFinal.LineDecay
