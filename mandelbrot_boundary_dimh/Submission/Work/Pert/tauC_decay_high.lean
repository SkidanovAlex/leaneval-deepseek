import Mathlib
import Submission.Work.Pert.Setup

namespace Work.Pert

/-- **Exponential decay of `τ_f` at the upper end** (Shishikura (A.1.7)(ii), lower gate, high
regime).  With `w = α z` and `t = w.im ≥ 1` the cover `τ_f z = σ / (1 - e^{-2πi α z})` satisfies

  `‖τ_f z‖ ≤ 2^6 ‖α‖ e^{-2π t}`

as soon as `‖σ‖ ≤ 32 ‖α‖`.

Indeed `- (2πi α z)` has real part `2π t`, so `‖e^{-2πi α z}‖ = e^{2π t} ≥ 2`; hence
`‖1 - e^{-2πi α z}‖ ≥ e^{2π t} - 1 ≥ e^{2π t}/2`, and dividing by it gives
`‖τ_f z‖ ≤ ‖σ‖ / (e^{2π t}/2) ≤ 2·32‖α‖·e^{-2π t} = 2^6 ‖α‖ e^{-2π t}`. -/
theorem tauC_decay_high {σ α z : ℂ} (hy : 1 ≤ (α * z).im) (hσ : ‖σ‖ ≤ 32 * ‖α‖) :
    ‖Work.Pert.tauC σ α z‖ ≤ 2 ^ 6 * ‖α‖ * Real.exp (-(2 * Real.pi * (α * z).im)) := by
  set t : ℝ := (α * z).im with ht
  set w : ℂ := -(2 * Real.pi * Complex.I * α * z) with hw
  -- The real part of `w = -(2πi α z)` is `2π t`, so `‖e^w‖ = e^{2π t}`.
  have hwre' : (-(2 * Real.pi * Complex.I * α * z)).re = 2 * Real.pi * (α * z).im := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    ring
  have hwre : w.re = 2 * Real.pi * t := by
    rw [hw, hwre', ← ht]
  have hexp : ‖Complex.exp w‖ = Real.exp (2 * Real.pi * t) := by
    rw [Complex.norm_exp, hwre]
  have ht1 : 1 ≤ t := hy
  -- `2 ≤ exp (2π t)` since `2π t ≥ 2` and `exp 2 ≥ 3`.
  have hexp2 : (2 : ℝ) ≤ Real.exp (2 * Real.pi * t) := by
    have h2pi : (2 : ℝ) ≤ 2 * Real.pi * t := by
      have := Real.pi_gt_three; nlinarith [ht1]
    calc (2:ℝ) ≤ Real.exp 2 := by
          have := Real.add_one_le_exp (2:ℝ); linarith [Real.exp_pos (2:ℝ)]
      _ ≤ Real.exp (2 * Real.pi * t) := Real.exp_le_exp.mpr h2pi
  -- Reverse triangle: `exp (2π t) - 1 ≤ ‖1 - e^w‖`, hence `exp (2π t)/2 ≤ ‖1 - e^w‖`.
  have hden : Real.exp (2 * Real.pi * t) / 2 ≤ ‖1 - Complex.exp w‖ := by
    have h1 : ‖Complex.exp w‖ ≤ ‖1 - Complex.exp w‖ + 1 := by
      have h := norm_add_le (Complex.exp w - 1) (1:ℂ)
      have he : (Complex.exp w - 1) + 1 = Complex.exp w := by ring
      rw [he, norm_one] at h
      rwa [norm_sub_rev (Complex.exp w) 1] at h
    rw [hexp] at h1
    linarith
  have hdenpos : 0 < Real.exp (2 * Real.pi * t) / 2 := by positivity
  rw [Work.Pert.tauC, ← hw, norm_div]
  calc ‖σ‖ / ‖1 - Complex.exp w‖
      ≤ ‖σ‖ / (Real.exp (2 * Real.pi * t) / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg σ) hdenpos hden
    _ = 2 * ‖σ‖ * (Real.exp (2 * Real.pi * t))⁻¹ := by ring
    _ ≤ 2 * (32 * ‖α‖) * (Real.exp (2 * Real.pi * t))⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith [hσ]
    _ = 2 ^ 6 * ‖α‖ * Real.exp (-(2 * Real.pi * t)) := by
        rw [Real.exp_neg]
        ring

end Work.Pert
