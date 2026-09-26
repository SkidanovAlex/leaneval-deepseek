import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.kerFormDefs
import Submission.Work.Asymptotics.continuationDefs
import Submission.Work.CKFinal.LineDecay.f2fun_top_edge_of_bound

namespace Work.CKFinal.LineDecay

open MeasureTheory Filter Topology

set_option linter.unusedVariables false

/-! # Decay of the `K̂(τ, ·+1)` ray integral on the top edge `[-1,0] + iR`

Identical in structure to `f2fun_top_edge_of_bound`, but for the *odd* kernel
`K̂ = -K|_2^τ S`: the integrand is `K̂(τ, z+1) e^{iπr²z}` on the vertical segment
`z = x + iR`, `x ∈ [-1,0]`.  There `z + 1` ranges over the strip `0 ≤ Re ≤ 1`,
`Im = R ≥ 1`, so the kernel growth bound `‖K̂(τ, ·)‖ ≤ C(1+R)^M e^{2πR}` on that strip
together with the Gaussian factor `‖e^{iπr²z}‖ = e^{-πr²R}` gives a majorant
`C (1+R)^M e^{-(r²-2)πR} → 0` as soon as `r² > 2`. -/

/-- `R ↦ (1+R)^M e^{-cR} → 0` at `+∞` for `M : ℕ` and `c > 0`. -/
lemma tendsto_one_add_pow_mul_exp_neg (M : ℕ) (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun R : ℝ => (1 + R)^M * Real.exp (-(c*R))) Filter.atTop (nhds 0) := by
  have h := tendsto_one_add_rpow_mul_exp_neg (M : ℝ) c hc
  refine h.congr' ?_
  filter_upwards with R
  rw [Real.rpow_natCast]

theorem f2fun_khat_top_edge (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) {r C : ℝ} {M : ℕ} (hr : 2 < r ^ 2) (hC : 0 ≤ C) (hstrip : ∀ (x t : ℝ), -1 ≤ x → x ≤ 1 → 1 ≤ t → ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t)) :
    Filter.Tendsto (fun R : ℝ => ∫ x in (-1 : ℝ)..0, Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (R : ℂ) * Complex.I + 1)) * Work.Asymptotics.kerExp r ((x : ℂ) + (R : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
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
  have hpt : ∀ x R : ℝ, -1 ≤ x → x ≤ 0 → 1 ≤ R →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x:ℂ) + (R:ℂ)*Complex.I + 1))
        * Work.Asymptotics.kerExp r ((x:ℂ) + (R:ℂ)*Complex.I)‖
        ≤ C * (1+R)^M * Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi * r^2 * R)) := by
    intro x R hx1 hx2 hR
    have hz : (x:ℂ) + (R:ℂ)*Complex.I + 1 = ((x+1:ℝ):ℂ) + (R:ℂ)*Complex.I := by push_cast; ring
    have hK := hstrip (x+1) R (by linarith) (by linarith) hR
    have hK' : ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x:ℂ) + (R:ℂ)*Complex.I + 1))‖
        ≤ C * (1+R)^M * Real.exp (2*Real.pi*R) := by
      rw [hz]; exact hK
    simp only [norm_mul, hker x R]
    exact mul_le_mul_of_nonneg_right hK' (Real.exp_nonneg _)
  -- uniform bound on the integral over `[-1,0]`
  have hint : ∀ R : ℝ, 1 ≤ R →
      ‖∫ x in (-1:ℝ)..0, Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x:ℂ) + (R:ℂ)*Complex.I + 1))
          * Work.Asymptotics.kerExp r ((x:ℂ) + (R:ℂ)*Complex.I)‖
        ≤ C * (1+R)^M * Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi * r^2 * R)) := by
    intro R hR
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1:ℝ)) (b := (0:ℝ))
      (C := C * (1+R)^M * Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi * r^2 * R)))
      (f := fun x : ℝ => Work.Kernels.Khat ℓ d τ
          (UpperHalfPlane.ofComplex ((x:ℂ) + (R:ℂ)*Complex.I + 1))
          * Work.Asymptotics.kerExp r ((x:ℂ) + (R:ℂ)*Complex.I))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hx
        exact hpt x R (le_of_lt hx.1) (by linarith [hx.2]) hR)
    rwa [show |(0:ℝ) - (-1)| = 1 by norm_num, mul_one] at h
  -- the majorant decays to `0`
  have hkey : ∀ R : ℝ, C * ((1+R)^M * Real.exp (-(c*R)))
      = C * (1+R)^M * Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi * r^2 * R)) := by
    intro R
    have hE : Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi*r^2*R)) = Real.exp (-(c*R)) := by
      rw [← Real.exp_add]; congr 1; rw [hcdef]; ring
    calc C * ((1+R)^M * Real.exp (-(c*R)))
        = C * ((1+R)^M * (Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi*r^2*R)))) := by rw [hE]
      _ = C * (1+R)^M * Real.exp (2*Real.pi*R) * Real.exp (-(Real.pi * r^2 * R)) := by ring
  have hmain : Filter.Tendsto (fun R : ℝ => C * (1+R)^M * Real.exp (2*Real.pi*R)
      * Real.exp (-(Real.pi * r^2 * R))) Filter.atTop (nhds 0) := by
    have h := (tendsto_one_add_pow_mul_exp_neg M c hc).const_mul C
    simp only [mul_zero] at h
    exact h.congr' (by filter_upwards with R; exact hkey R)
  -- squeeze
  refine squeeze_zero_norm' ?_ hmain
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  exact hint R hR

end Work.CKFinal.LineDecay
