import Mathlib
import Submission.Work.CKFinal.LineDecay.shift_helpers

namespace Work.CKFinal.LineDecay

open MeasureTheory Filter Topology

set_option linter.unusedVariables false

/-! # Decay of the `K(τ, ·+1)` ray integral on the top edge `[-1,0] + iR`

The contour shift of CKMRV §5.3 moves the `K(τ, ·+1)` ray onto the vertical segment
`[-1,0] + iR`; the integral of `f2fun ℓ d τ r` along that segment is controlled by the
Kernel bound `‖K^{(d)}(τ, ·)‖ ≤ C(1+R)^N e^{2πR}` on the strip `-1 ≤ Re ≤ 1`, `Im ≥ τ.im+1`,
together with the Gaussian factor `‖e^{iπr²z}‖ = e^{-πr² Im z}` and `r² > 2`. -/

/-- `R ↦ (1+R)^N e^{-cR} → 0` at `+∞` for `N ≥ 0` and `c > 0`. -/
lemma tendsto_one_add_rpow_mul_exp_neg (N c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun R : ℝ => (1 + R)^N * Real.exp (-(c*R))) Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun R : ℝ => (R+1)^N * Real.exp (-c*(R+1))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero N c hc).comp
      (tendsto_atTop_add_const_right Filter.atTop 1 tendsto_id)
  have h1 := h0.const_mul (Real.exp c)
  simp only [mul_zero] at h1
  refine h1.congr' ?_
  filter_upwards with R
  have hexp : Real.exp (-c*(R+1)) = Real.exp (-(c*R)) * Real.exp (-c) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, Real.exp_neg c, show (1:ℝ) + R = R + 1 by ring]
  have hne : Real.exp c ≠ 0 := Real.exp_ne_zero c
  rw [show Real.exp c * ((R+1)^N * (Real.exp (-(c*R)) * (Real.exp c)⁻¹))
      = Real.exp c * (Real.exp c)⁻¹ * ((R+1)^N * Real.exp (-(c*R))) by ring]
  rw [mul_inv_cancel₀ hne, one_mul]

theorem f2fun_top_edge_of_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r^2) {C N : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hb : ∀ (x R : ℝ), -1 ≤ x → x ≤ 1 → τ.im + 1 ≤ R →
        ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x:ℂ) + (R:ℂ)*Complex.I))‖
          ≤ C * (1 + R)^N * Real.exp (2 * Real.pi * R)) :
    Filter.Tendsto (fun R : ℝ => ∫ x in (-1:ℝ)..0, Work.CKFinal.LineDecay.f2fun ℓ d τ r ((x:ℂ) + (R:ℂ)*Complex.I))
      Filter.atTop (nhds 0) := by
  set c : ℝ := Real.pi * (r^2 - 2) with hcdef
  have hc : 0 < c := by
    rw [hcdef]; exact mul_pos Real.pi_pos (by linarith)
  -- the Gaussian factor on the vertical line at height `R`
  have hker : ∀ x R : ℝ, ‖Work.Asymptotics.kerExp r ((x:ℂ) + (R:ℂ)*Complex.I)‖
      = Real.exp (-(Real.pi * r^2 * R)) := by
    intro x R
    rw [Work.Asymptotics.kerExp, Complex.norm_exp]
    congr 1
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  -- pointwise bound on the integrand
  have hpt : ∀ x R : ℝ, -1 ≤ x → x ≤ 0 → τ.im + 1 ≤ R →
      ‖Work.CKFinal.LineDecay.f2fun ℓ d τ r ((x:ℂ) + (R:ℂ)*Complex.I)‖
        ≤ C * (1+R)^N * Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi * r^2 * R)) := by
    intro x R hx1 hx2 hR
    have hz : (x:ℂ) + (R:ℂ)*Complex.I + 1 = ((x+1:ℝ):ℂ) + (R:ℂ)*Complex.I := by push_cast; ring
    have hK := hb (x+1) R (by linarith) (by linarith) hR
    have hK' : ‖Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex ((x:ℂ) + (R:ℂ)*Complex.I + 1))‖
        ≤ C * (1+R)^N * Real.exp (2*Real.pi*R) := by
      rw [hz]; exact hK
    simp only [f2fun, norm_mul, hker x R]
    exact mul_le_mul_of_nonneg_right hK' (Real.exp_pos _).le
  -- uniform bound on the integral over `[-1,0]`
  have hint : ∀ R : ℝ, τ.im + 1 ≤ R →
      ‖∫ x in (-1:ℝ)..0, Work.CKFinal.LineDecay.f2fun ℓ d τ r ((x:ℂ) + (R:ℂ)*Complex.I)‖
        ≤ C * (1+R)^N * Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi * r^2 * R)) := by
    intro R hR
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1:ℝ)) (b := (0:ℝ))
      (C := C * (1+R)^N * Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi * r^2 * R)))
      (f := fun x : ℝ => f2fun ℓ d τ r ((x:ℂ) + (R:ℂ)*Complex.I))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hx
        exact hpt x R (le_of_lt hx.1) (by linarith [hx.2]) hR)
    rwa [show |(0:ℝ) - (-1)| = 1 by norm_num, mul_one] at h
  -- the majorant decays to `0`
  have hkey : ∀ R : ℝ, C * ((1+R)^N * Real.exp (-(c*R)))
      = C * (1+R)^N * Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi * r^2 * R)) := by
    intro R
    have hE : Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi*r^2*R)) = Real.exp (-(c*R)) := by
      rw [← Real.exp_add]; congr 1; rw [hcdef]; ring
    calc C * ((1+R)^N * Real.exp (-(c*R)))
        = C * ((1+R)^N * (Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi*r^2*R)))) := by rw [hE]
      _ = C * (1+R)^N * Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi * r^2 * R)) := by ring
  have hmain : Filter.Tendsto (fun R : ℝ => C * (1+R)^N * Real.exp (2*Real.pi*R)
      * Real.exp (-(Real.pi * r^2 * R))) Filter.atTop (nhds 0) := by
    have h := (tendsto_one_add_rpow_mul_exp_neg N c hc).const_mul C
    simp only [mul_zero] at h
    exact h.congr' (by filter_upwards with R; exact hkey R)
  -- squeeze
  refine squeeze_zero_norm' ?_ hmain
  filter_upwards [eventually_ge_atTop (τ.im + 1)] with R hR
  exact hint R hR

end Work.CKFinal.LineDecay
