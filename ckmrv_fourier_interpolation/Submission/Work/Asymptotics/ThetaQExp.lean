import Mathlib
import Submission.Work.Asymptotics.PGFar.Defs
import Submission.Work.Kernels.LogLambda.ThetaLaws
import Submission.Work.Kernels.LogLambda.ThetaLower.ratio_estimate
import Submission.Work.Asymptotics.theta00_pow_series
import Submission.Work.Asymptotics.ThetaQExpAux
import Submission.Work.Asymptotics.UFun_qexp

namespace Work.Asymptotics

noncomputable section

open UpperHalfPlane

/-- `‖nomeE w‖ ≤ 1/2` on the region `Im w ≥ 2`. -/
private lemma nomeE_norm_le_half (w : UpperHalfPlane) (hw : 2 ≤ w.im) :
    ‖nomeE w‖ ≤ 1 / 2 := by
  rw [norm_nomeE w, Real.exp_neg]
  rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
  have hpi : (1 : ℝ) ≤ Real.pi * w.im := by nlinarith [Real.pi_gt_three, hw]
  calc (2 : ℝ) = 1 + 1 := by norm_num
    _ ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    _ ≤ Real.exp (Real.pi * w.im) := Real.exp_le_exp.mpr hpi

/-- **`q`-expansion of `W = θ₀₁⁴`.**  Writing `e = nomeE w = exp (π i w)`, the fourth power of
Jacobi's `θ₀₁` agrees with `1 - 8 e + 24 e² - 32 e³ + 24 e⁴` up to `O(‖e‖⁵)` on `Im w ≥ 2`.
This is deduced from `UFun_qexp` by the `T`-law `θ₀₁(τ) = θ₀₀(τ + 1)`, which changes the sign
of the nome. -/
theorem WFun_qexp (w : UpperHalfPlane) (hw : 2 ≤ w.im) :
    ‖Work.Kernels.WFun w - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2
      - 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)‖
      ≤ 10000 * ‖nomeE w‖ ^ 5 := by
  have hTw : 2 ≤ (ModularGroup.T • w).im := by
    rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.vadd_im]
    exact hw
  have h := UFun_qexp (ModularGroup.T • w) hTw
  have hU : Work.Kernels.UFun (ModularGroup.T • w) = Work.Kernels.WFun w := by
    show Work.Kernels.theta00Fun (ModularGroup.T • w) ^ 4 = Work.Kernels.theta01Fun w ^ 4
    rw [Work.Kernels.theta00Fun_T w]
  have he : nomeE (ModularGroup.T • w) = -nomeE w := by
    rw [nomeE_def, nomeE_def, Work.Kernels.coe_T_smul]
    rw [show (Real.pi : ℂ) * Complex.I * ((w : ℂ) + 1)
        = Real.pi * Complex.I * (w : ℂ) + Real.pi * Complex.I by ring]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hpoly : (1 + 8 * (-nomeE w) + 24 * (-nomeE w) ^ 2 + 32 * (-nomeE w) ^ 3
      + 24 * (-nomeE w) ^ 4 : ℂ)
      = 1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
        + 24 * (nomeE w) ^ 4 := by ring
  rw [hU, he, hpoly, norm_neg] at h
  exact h

/-- **`q`-expansion of `V = θ₁₀⁴`.**  Writing `e = nomeE w = exp (π i w)`, the fourth power of
Jacobi's `θ₁₀` agrees with `16 e + 64 e³` up to `O(‖e‖⁵)` on `Im w ≥ 2`.  Indeed
`θ₁₀(τ) = e^{πiτ/4} · θ(τ/2, τ)` and `θ(z/2, z)/2 = ∑_{k ≥ 0} e^{k²+k}`, whose square term is
`e²`; the fourth power therefore contributes `16 e (1 + e²)⁴ = 16 e + 64 e³ + 96 e⁵ + …`. -/
theorem VFun_qexp (w : UpperHalfPlane) (hw : 2 ≤ w.im) :
    ‖Work.Kernels.VFun w - (16 * nomeE w + 64 * (nomeE w) ^ 3)‖
      ≤ 10000 * ‖nomeE w‖ ^ 5 := by
  have hwpos : 0 < w.im := by linarith
  have hrle : ‖nomeE w‖ ≤ 1 / 2 := nomeE_norm_le_half w hw
  set e : ℂ := nomeE w with he
  set u : ℂ := ∑' k : ℕ, e ^ (k ^ 2 + k) with hu
  set G : ℂ := ∑' k : ℕ, e ^ ((k + 1) ^ 2 + (k + 1)) with hG
  have hsumm : Summable (fun k : ℕ => e ^ (k ^ 2 + k)) :=
    summable_pow_of_le (e := e) (f := fun k => k ^ 2 + k) (m := 0) hrle (fun k => by nlinarith)
  have hsummG : Summable (fun k : ℕ => e ^ ((k + 1) ^ 2 + (k + 1))) :=
    summable_pow_of_le (e := e) (f := fun k => (k + 1) ^ 2 + (k + 1)) (m := 2) hrle
      (fun k => by nlinarith)
  have hu1 : u = 1 + G := by
    rw [hu, hG, hsumm.tsum_eq_zero_add]
    norm_num
  have hG2 : G = e ^ 2 + ∑' k : ℕ, e ^ ((k + 2) ^ 2 + (k + 2)) := by
    rw [hG, hsummG.tsum_eq_zero_add]
    norm_num
  have hGbound : ‖G - e ^ 2‖ ≤ 2 * ‖e‖ ^ 6 := by
    have h : G - e ^ 2 = ∑' k : ℕ, e ^ ((k + 2) ^ 2 + (k + 2)) := by rw [hG2]; ring
    rw [h]
    exact norm_tsum_pow_le (e := e) (f := fun k => (k + 2) ^ 2 + (k + 2)) (m := 6) hrle
      (fun k => by nlinarith)
  have hpair : jacobiTheta₂ ((w : ℂ) / 2) (w : ℂ) / 2 = u := by
    have h := thetaPair_pow_series (w : ℂ) (by rw [UpperHalfPlane.coe_im]; exact hwpos)
    rw [show Complex.exp (Real.pi * Complex.I * (w : ℂ)) = e from by rw [he, nomeE_def]] at h
    rwa [← hu] at h
  have hV : Work.Kernels.VFun w = 16 * e * u ^ 4 := by
    have h4 : (Complex.exp (Real.pi * Complex.I * (w : ℂ) / 4)) ^ 4 = e := by
      rw [← Complex.exp_nat_mul, he, nomeE_def]
      congr 1
      ring
    have hVd : Work.Kernels.VFun w
        = (Complex.exp (Real.pi * Complex.I * (w : ℂ) / 4)
            * jacobiTheta₂ ((w : ℂ) / 2) (w : ℂ)) ^ 4 := rfl
    rw [hVd, mul_pow, h4, ← hpair]
    ring
  have hb := V_bound e u G ‖e‖ (norm_nonneg e) hrle rfl hu1 hGbound
  rw [hV]
  exact hb

theorem ThetaQExp :
    (∀ w : UpperHalfPlane, 2 ≤ w.im →
      ‖Work.Kernels.UFun w - (1 + 8 * Work.Asymptotics.nomeE w + 24 * (Work.Asymptotics.nomeE w) ^ 2 + 32 * (Work.Asymptotics.nomeE w) ^ 3
        + 24 * (Work.Asymptotics.nomeE w) ^ 4)‖ ≤ 10000 * ‖Work.Asymptotics.nomeE w‖ ^ 5) ∧
    (∀ w : UpperHalfPlane, 2 ≤ w.im →
      ‖Work.Kernels.WFun w - (1 - 8 * Work.Asymptotics.nomeE w + 24 * (Work.Asymptotics.nomeE w) ^ 2 - 32 * (Work.Asymptotics.nomeE w) ^ 3
        + 24 * (Work.Asymptotics.nomeE w) ^ 4)‖ ≤ 10000 * ‖Work.Asymptotics.nomeE w‖ ^ 5) ∧
    (∀ w : UpperHalfPlane, 2 ≤ w.im →
      ‖Work.Kernels.VFun w - (16 * Work.Asymptotics.nomeE w + 64 * (Work.Asymptotics.nomeE w) ^ 3)‖ ≤ 10000 * ‖Work.Asymptotics.nomeE w‖ ^ 5) :=
  ⟨UFun_qexp, WFun_qexp, VFun_qexp⟩

end

end Work.Asymptotics
