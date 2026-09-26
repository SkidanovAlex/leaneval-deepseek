import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.KPlus_funnel_tail_eight
import Submission.Work.Asymptotics.KMinus_funnel_tail_eight
import Submission.Work.Asymptotics.KPlus_funnel_tail_twentyfour
import Submission.Work.Asymptotics.KMinus_funnel_tail_twentyfour
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.Khat_funnel_tail_sharp_core

namespace Work.Asymptotics

open UpperHalfPlane

/-- On the funnel, the cusp parameter `q(τ) = e^{2πiτ}` has modulus at most `1`. -/
lemma qParamFun_norm_le_one_of_Funnel {τ : UpperHalfPlane} (hτ : Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  have him : 0 ≤ τ.im := le_of_lt τ.im_pos
  have h1 : ‖Work.Kernels.qParamFun τ‖
      = Real.exp (-(2 * Real.pi * τ.im)) := by
    simp only [Work.Kernels.qParamFun, Complex.norm_exp, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    norm_num
  rw [h1]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, him])

/-- The reduction: a `q(τ)`-shaped sharp cusp-`∞` tail estimate for `K̂` implies the target.

`Khat_funnel_tail_sharp_core` is the sharp form of the tail estimate, with the extra factor
`‖q(τ)‖ = e^{-2π Im τ} ≤ 1`; it is proved in
`Submission/Work/Asymptotics/Khat_funnel_tail_sharp_core.lean`.  Since the funnel has
`Im τ ≥ 2`, the extra factor is at most `1`, so the target follows. -/
theorem Khat_funnel_tail_sharp_of_core (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (h : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.Khat ℓ d τ z
            - (Work.Asymptotics.Compact.Gplus d τ z
                - Work.Asymptotics.Compact.Gminus d ℓ τ z) / 2‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.Khat ℓ d τ z
            - (Work.Asymptotics.Compact.Gplus d τ z
                - Work.Asymptotics.Compact.Gminus d ℓ τ z) / 2‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht hz => ?_⟩
  have hq : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := qParamFun_norm_le_one_of_Funnel hτ
  have hspos : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N
  have hexp : (0 : ℝ) < Real.exp (-(Real.pi * t)) := Real.exp_pos _
  have him2 : (2 : ℝ) ≤ τ.im := hτ.2
  have h1t : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg (by linarith) M
  have hstep : C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * Real.exp (-(Real.pi * t))
      ≤ C * 1 * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
    have h2 : (0 : ℝ) ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * Real.exp (-(Real.pi * t)) := by positivity
    calc C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(Real.pi * t))
        = (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)))
            * ‖Work.Kernels.qParamFun τ‖ := by ring
      _ ≤ (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t))) * 1 :=
          mul_le_mul_of_nonneg_left hq h2
      _ = C * 1 * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by ring
  calc ‖Work.Kernels.Khat ℓ d τ z
          - (Work.Asymptotics.Compact.Gplus d τ z
              - Work.Asymptotics.Compact.Gminus d ℓ τ z) / 2‖
      ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(Real.pi * t)) := hb τ z t hτ ht hz
    _ ≤ C * 1 * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := hstep
    _ = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by ring

theorem Khat_funnel_tail_sharp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.Khat ℓ d τ z
            - (Work.Asymptotics.Compact.Gplus d τ z
                - Work.Asymptotics.Compact.Gminus d ℓ τ z) / 2‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) :=
  Khat_funnel_tail_sharp_of_core ℓ d
    (Work.Asymptotics.Khat_funnel_tail_sharp_core ℓ d hd)

end Work.Asymptotics
