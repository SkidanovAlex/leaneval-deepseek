/-
# The strip bound for the CKMRV kernel `K^{(d)}`

For `τ` in the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and `z = x + i R` in the strip
`-1 ≤ x ≤ 1`, `R ≥ Im τ + 1` — i.e. *above* the poles of the kernel in the second variable —
the CKMRV kernel satisfies

  `‖K^{(d)}(τ, z)‖ ≤ C (1 + R)^N exp (2π R)`.

This is the "top-edge" growth bound consumed by the contour shift of CKMRV §5.3: multiplied by
the Gaussian `e^{-πr²R}` with `r² > 2` it gives the decay that kills the horizontal edge of the
shifted rectangle.

The proof needs no cusp expansion at all.  It is the *divisor* form of Theorem 4.9(4),

  `‖K(τ,z)‖ · ‖Δ(τ) Δ(z)^e (j τ - j z)‖ ≤ α (scale τ)^N (scale z)^M`   (`e = 1, 2`)

(`Work.Asymptotics.norm_Kfun_mul_growthPrefactor_le`, already proved from the cleared-kernel
moderate growth `Work.Asymptotics.KClear_mg2`), divided by the lower bound for the divisor
`Δ(z)(jτ - jz)` of `Work.Asymptotics.KPlus24Strip.divisor_lower_strip` (`≥ 1/16` for
`Im z ≥ Im τ + 1`, at *every* real part) and the cusp lower bound
`‖Δ(z)‖ ≥ (1/2) e^{-2π Im z}` of `Work.Asymptotics.DeltaFun_funnel_lower_sharp`.  The factor
`Δ(z)^{e-1}` which survives for `d = 24` is exactly the factor `e^{-2π Im z}` that produces the
`e^{2π R}` on the right.
-/
import Mathlib
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Asymptotics.Divisor
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.KhatE1.KPlus24SharpStrip
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.funnelTailBasic

noncomputable section

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-- `τ` on the lines `Re = ±1/2`, `Im ≥ 12` lies in the fundamental region `𝒟`. -/
theorem mem_DomainD_of_line (τ : UpperHalfPlane) (hre : τ.re = 1/2 ∨ τ.re = -1/2)
    (him : 12 ≤ τ.im) : τ ∈ Work.Asymptotics.DomainD := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hre with h | h <;> rw [h] <;> norm_num
  · rcases hre with h | h <;> rw [h] <;> norm_num
  · have h1 : (((τ:ℂ) - (1/2:ℂ)).im) = τ.im := by simp [Complex.sub_im]
    have h2 := Complex.abs_im_le_norm ((τ:ℂ) - (1/2:ℂ))
    rw [h1, abs_of_pos τ.im_pos] at h2
    linarith
  · have h1 : (((τ:ℂ) + (1/2:ℂ)).im) = τ.im := by simp [Complex.add_im]
    have h2 := Complex.abs_im_le_norm ((τ:ℂ) + (1/2:ℂ))
    rw [h1, abs_of_pos τ.im_pos] at h2
    linarith

/-- The divisor lower bound in the strip, `d = 8`: only `Δ(z)(jτ - jz)` has to be bounded
below. -/
theorem growthPrefactor_lower_strip_eight (τ z : UpperHalfPlane) (hτ : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ z.im) :
    (1 / 64) * ‖Work.Kernels.DeltaFun τ‖ ≤ ‖Work.Kernels.growthPrefactor 8 τ z‖ := by
  have hdiv : (1 / 16 : ℝ) ≤ ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
    Work.Asymptotics.KPlus24Strip.divisor_lower_strip τ z hτ ht
  have hΔτ : 0 ≤ ‖Work.Kernels.DeltaFun τ‖ := norm_nonneg _
  have hpowe : Work.Kernels.DeltaFun z ^ (if (8 : ℕ) = 8 then (1 : ℕ) else 2)
      = Work.Kernels.DeltaFun z := by rw [if_pos rfl, pow_one]
  rw [Work.Kernels.growthPrefactor, hpowe, mul_assoc, norm_mul]
  calc (1 / 64) * ‖Work.Kernels.DeltaFun τ‖
      ≤ ‖Work.Kernels.DeltaFun τ‖ * (1 / 16) := by linarith
    _ ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
        mul_le_mul_of_nonneg_left hdiv hΔτ

/-- The divisor lower bound in the strip, `d = 24`: this time `Δ(z)` itself survives, and the
cusp lower bound `‖Δ(z)‖ ≥ (1/2) e^{-2π Im z}` is what produces the exponential factor. -/
theorem growthPrefactor_lower_strip_twentyfour (τ z : UpperHalfPlane)
    (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ z.im) :
    (1 / 64) * ‖Work.Kernels.DeltaFun τ‖ * Real.exp (-(2 * Real.pi * z.im))
      ≤ ‖Work.Kernels.growthPrefactor 24 τ z‖ := by
  have hdiv : (1 / 16 : ℝ) ≤ ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
    Work.Asymptotics.KPlus24Strip.divisor_lower_strip τ z hτ ht
  have hΔz : (1 / 2) * Real.exp (-(2 * Real.pi * z.im)) ≤ ‖Work.Kernels.DeltaFun z‖ :=
    Work.Asymptotics.DeltaFun_funnel_lower_sharp
      (by have := Work.Asymptotics.Funnel.im_two hτ; linarith)
  have hD : (0 : ℝ) ≤ ‖Work.Kernels.DeltaFun τ‖ := norm_nonneg _
  have hpowe : Work.Kernels.DeltaFun z ^ (if (24 : ℕ) = 8 then (1 : ℕ) else 2)
      = Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun z := by
    rw [if_neg (by norm_num), pow_two]
  have hgp : ‖Work.Kernels.growthPrefactor 24 τ z‖
      = ‖Work.Kernels.DeltaFun τ‖ * (‖Work.Kernels.DeltaFun z‖
          * (‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.jInvariantFun τ
              - Work.Kernels.jInvariantFun z‖)) := by
    rw [Work.Kernels.growthPrefactor, hpowe]
    rw [show (Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun z))
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
        = Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun z * (Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))) from by
      rw [mul_assoc, mul_assoc]]
    rw [norm_mul, norm_mul, norm_mul]
  rw [hgp]
  calc (1 / 64) * ‖Work.Kernels.DeltaFun τ‖ * Real.exp (-(2 * Real.pi * z.im))
      = ‖Work.Kernels.DeltaFun τ‖ * ((1 / 2) * Real.exp (-(2 * Real.pi * z.im))) * (1 / 32) := by
        ring
    _ ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖ * (1 / 32) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔz hD) (by norm_num)
    _ ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖ * (1 / 16) :=
        mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 32 ≤ 1 / 16)
          (mul_nonneg hD (norm_nonneg _))
    _ ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖
          * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ
              - Work.Kernels.jInvariantFun z)‖ :=
        mul_le_mul_of_nonneg_left hdiv (mul_nonneg hD (norm_nonneg _))
    _ = ‖Work.Kernels.DeltaFun τ‖ * (‖Work.Kernels.DeltaFun z‖
          * (‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.jInvariantFun τ
              - Work.Kernels.jInvariantFun z‖)) := by rw [norm_mul, mul_assoc]

/-- **The strip bound for `K^{(d)}`.**  For `τ` in the funnel, `-1 ≤ Re z ≤ 1` and
`Im z ≥ Im τ + 1`, the kernel is bounded by a polynomial in `Im z` times `e^{2π Im z}`. -/
theorem Kfun_bound_strip (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : Work.Asymptotics.Funnel τ) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 1 → τ.im + 1 ≤ z.im →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z)‖
        ≤ C * (1 + z.im) ^ N * Real.exp (2 * Real.pi * z.im) := by
  obtain ⟨α, N, M, hα, hN, hM, hb⟩ :=
    Work.Asymptotics.norm_Kfun_mul_growthPrefactor_le (ℓ := ℓ) hd
      (Work.Asymptotics.KClear_mg2 ℓ d hd).1
  have hΔτpos : 0 < ‖Work.Kernels.DeltaFun τ‖ := by
    rw [norm_pos_iff]; exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  refine ⟨max (64 * α * (Work.Kernels.scale τ) ^ N * 4 ^ M / ‖Work.Kernels.DeltaFun τ‖) 1,
    M, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hM, ?_⟩
  intro z hz1 hz2 hz3
  have hτ2 : (2 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_two hτ
  have hzpos : 0 < z.im := by linarith
  have hz1le : (1 : ℝ) ≤ z.im := by linarith
  set W : UpperHalfPlane := ⟨z, hzpos⟩ with hW
  have hWof : UpperHalfPlane.ofComplex z = W := by
    rw [hW, UpperHalfPlane.ofComplex_apply_of_im_pos hzpos]
  rw [hWof]
  have hWim : W.im = z.im := rfl
  -- the divisor lower bound, uniformly in `d ∈ {8,24}`
  have hDlow : (1 / 64) * ‖Work.Kernels.DeltaFun τ‖
      * Real.exp (-(2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im))
      ≤ ‖Work.Kernels.growthPrefactor d τ W‖ := by
    rcases hd with h8 | h24
    · rw [h8]
      have he : (if (8 : ℕ) = 8 then (0 : ℝ) else 1) = 0 := by rw [if_pos rfl]
      rw [he]
      simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
      exact growthPrefactor_lower_strip_eight τ W hτ (by rw [hWim]; linarith)
    · rw [h24]
      have he : (if (24 : ℕ) = 8 then (0 : ℝ) else 1) = 1 := by rw [if_neg (by norm_num)]
      rw [he, mul_one]
      exact growthPrefactor_lower_strip_twentyfour τ W hτ (by rw [hWim]; linarith)
  have hDpos : 0 < (1 / 64) * ‖Work.Kernels.DeltaFun τ‖
      * Real.exp (-(2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im)) := by
    have h1 : (0 : ℝ) < (1 / 64) * ‖Work.Kernels.DeltaFun τ‖ := by linarith
    exact mul_pos h1 (Real.exp_pos _)
  have hstep : ‖Work.Kernels.Kfun ℓ d τ W‖ * ((1 / 64) * ‖Work.Kernels.DeltaFun τ‖
      * Real.exp (-(2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im)))
      ≤ α * (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale W) ^ M :=
    le_trans (mul_le_mul_of_nonneg_left hDlow (norm_nonneg _)) (hb τ W)
  -- multiply by `64 e^{b}`, `b = 2π·(if d = 8 then 0 else 1)·Im z`
  have hmul : ‖Work.Kernels.Kfun ℓ d τ W‖ * ‖Work.Kernels.DeltaFun τ‖
      ≤ 64 * (α * (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale W) ^ M)
        * Real.exp (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im) := by
    have h1 := mul_le_mul_of_nonneg_right hstep
      (by positivity : (0 : ℝ) ≤ 64 * Real.exp
        (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im))
    have hee : Real.exp (-(2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im))
        * Real.exp (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hL : (‖Work.Kernels.Kfun ℓ d τ W‖ * ((1 / 64) * ‖Work.Kernels.DeltaFun τ‖
          * Real.exp (-(2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im))))
        * (64 * Real.exp (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im))
        = ‖Work.Kernels.Kfun ℓ d τ W‖ * ‖Work.Kernels.DeltaFun τ‖ := by
      calc (‖Work.Kernels.Kfun ℓ d τ W‖ * ((1 / 64) * ‖Work.Kernels.DeltaFun τ‖
            * Real.exp (-(2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im))))
          * (64 * Real.exp (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im))
          = ‖Work.Kernels.Kfun ℓ d τ W‖ * ‖Work.Kernels.DeltaFun τ‖
              * (Real.exp (-(2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im))
                * Real.exp (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im)) := by ring
        _ = ‖Work.Kernels.Kfun ℓ d τ W‖ * ‖Work.Kernels.DeltaFun τ‖ := by rw [hee, mul_one]
    rw [hL] at h1
    have h2 : (α * (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale W) ^ M)
        * (64 * Real.exp (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im))
        = 64 * (α * (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale W) ^ M)
          * Real.exp (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im) := by ring
    rwa [h2] at h1
  -- the exponent and the scale
  have hcz_le : (if d = 8 then (0 : ℝ) else 1) ≤ 1 := by
    by_cases h8 : d = 8
    · rw [if_pos h8]; norm_num
    · rw [if_neg h8]
  have hexp_le : Real.exp (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im)
      ≤ Real.exp (2 * Real.pi * z.im) := by
    apply Real.exp_le_exp.mpr
    calc 2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im
        = (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1)) * z.im := rfl
      _ ≤ (2 * Real.pi * 1) * z.im :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcz_le (by positivity)) hzpos.le
      _ = 2 * Real.pi * z.im := by ring
  have hscale_le : Work.Kernels.scale W ≤ 4 * (1 + z.im) := by
    rw [Work.Kernels.scale, hWim]
    have h1 : ‖z‖ ≤ 1 + z.im := by
      have hcoe : z = ((z.re : ℂ)) + ((z.im : ℂ)) * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im z]
      have hstep : ‖z‖ ≤ ‖((z.re : ℂ))‖ + ‖((z.im : ℂ)) * Complex.I‖ := by
        conv_lhs => rw [hcoe]
        exact norm_add_le ((z.re : ℂ)) (((z.im : ℂ)) * Complex.I)
      calc ‖z‖ ≤ ‖((z.re : ℂ))‖ + ‖((z.im : ℂ)) * Complex.I‖ := hstep
        _ = |z.re| + |z.im| := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 + z.im := by
            rw [abs_of_pos hzpos]; linarith [abs_le.mpr ⟨hz1, hz2⟩]
    have h2 : (z.im)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz1le
    linarith
  have hpow_le : (Work.Kernels.scale W) ^ M ≤ 4 ^ M * (1 + z.im) ^ M := by
    calc (Work.Kernels.scale W) ^ M ≤ (4 * (1 + z.im)) ^ M :=
          Real.rpow_le_rpow (Work.Kernels.scale_pos W).le hscale_le hM
      _ = 4 ^ M * (1 + z.im) ^ M := Real.mul_rpow (by norm_num) (by linarith)
  -- assemble
  set Q : ℝ := 64 * α * (Work.Kernels.scale τ) ^ N * 4 ^ M with hQ
  set P : ℝ := (1 + z.im) ^ M * Real.exp (2 * Real.pi * z.im) with hP
  have hPnn : 0 ≤ P := by rw [hP]; positivity
  have hmain : ‖Work.Kernels.Kfun ℓ d τ W‖ * ‖Work.Kernels.DeltaFun τ‖ ≤ Q * P := by
    refine le_trans hmul ?_
    rw [hQ, hP]
    have h1 : 64 * (α * (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale W) ^ M)
        * Real.exp (2 * Real.pi * (if d = 8 then (0 : ℝ) else 1) * z.im)
        ≤ 64 * (α * (Work.Kernels.scale τ) ^ N * (4 ^ M * (1 + z.im) ^ M))
          * Real.exp (2 * Real.pi * z.im) := by
      have hατ : 0 ≤ α * (Work.Kernels.scale τ) ^ N :=
        mul_nonneg hα (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N)
      have hX : (α * (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale W) ^ M)
          ≤ α * (Work.Kernels.scale τ) ^ N * (4 ^ M * (1 + z.im) ^ M) :=
        mul_le_mul_of_nonneg_left hpow_le hατ
      have hX64 := mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 64)
      refine mul_le_mul hX64 hexp_le (Real.exp_nonneg _) ?_
      exact mul_nonneg (by norm_num) (mul_nonneg hατ (mul_nonneg (by positivity) (by positivity)))
    exact le_trans h1 (le_of_eq (by ring))
  have hQD : Q ≤ max (Q / ‖Work.Kernels.DeltaFun τ‖) 1 * ‖Work.Kernels.DeltaFun τ‖ := by
    have h1 : (Q / ‖Work.Kernels.DeltaFun τ‖) * ‖Work.Kernels.DeltaFun τ‖ = Q :=
      div_mul_cancel₀ Q hΔτpos.ne'
    calc Q = (Q / ‖Work.Kernels.DeltaFun τ‖) * ‖Work.Kernels.DeltaFun τ‖ := h1.symm
      _ ≤ max (Q / ‖Work.Kernels.DeltaFun τ‖) 1 * ‖Work.Kernels.DeltaFun τ‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hΔτpos.le
  have hfin : ‖Work.Kernels.Kfun ℓ d τ W‖ * ‖Work.Kernels.DeltaFun τ‖
      ≤ (max (Q / ‖Work.Kernels.DeltaFun τ‖) 1 * P) * ‖Work.Kernels.DeltaFun τ‖ := by
    calc ‖Work.Kernels.Kfun ℓ d τ W‖ * ‖Work.Kernels.DeltaFun τ‖ ≤ Q * P := hmain
      _ ≤ (max (Q / ‖Work.Kernels.DeltaFun τ‖) 1 * ‖Work.Kernels.DeltaFun τ‖) * P :=
          mul_le_mul_of_nonneg_right hQD hPnn
      _ = (max (Q / ‖Work.Kernels.DeltaFun τ‖) 1 * P) * ‖Work.Kernels.DeltaFun τ‖ := by ring
  have hres := le_of_mul_le_mul_right hfin hΔτpos
  refine le_trans hres (le_of_eq ?_)
  rw [hQ, hP]
  ring

/-- The strip bound in the input shape used by the contour shift: the kernel evaluated at
`ofComplex (x + i R)` for `-1 ≤ x ≤ 1` and `R ≥ Im τ + 1`. -/
theorem Kfun_strip_tail_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hD : τ ∈ Work.Asymptotics.DomainD) (him : 12 ≤ τ.im) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → τ.im + 1 ≤ R →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I))‖
        ≤ C * (1 + R) ^ N * Real.exp (2 * Real.pi * R) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Kfun_bound_strip ℓ d hd τ ⟨hD, by linarith⟩
  refine ⟨C, N, hC, hN, fun x R hx1 hx2 hR => ?_⟩
  have hz : ((x : ℂ) + (R : ℂ) * Complex.I).re = x := by simp
  have zi : ((x : ℂ) + (R : ℂ) * Complex.I).im = R := by simp
  have h := hb ((x : ℂ) + (R : ℂ) * Complex.I) (by rw [hz]; exact hx1)
    (by rw [hz]; exact hx2) (by rw [zi]; exact hR)
  rwa [zi] at h

/-- The strip bound on the two critical lines `Re τ = ±1/2`, `Im τ ≥ 12`. -/
theorem Kfun_strip_tail_bound_line (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = -1 / 2) (him : 12 ≤ τ.im) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ x R : ℝ, -1 ≤ x → x ≤ 1 → τ.im + 1 ≤ R →
      ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I))‖
        ≤ C * (1 + R) ^ N * Real.exp (2 * Real.pi * R) :=
  Kfun_strip_tail_bound ℓ d hd τ (mem_DomainD_of_line τ hre him) him

end Work.CKFinal.LineDecay
