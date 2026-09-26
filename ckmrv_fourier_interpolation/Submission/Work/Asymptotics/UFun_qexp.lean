import Mathlib
import Submission.Work.Asymptotics.ThetaQExpAux
import Submission.Work.Asymptotics.theta00_pow_series
import Submission.Work.Asymptotics.PGFar.Defs
import Submission.Work.Kernels.LogLambda.ThetaLaws

namespace Work.Asymptotics

open UpperHalfPlane

/-- **`q`-expansion of `U = θ₀₀⁴` at the cusp.**  Writing `e = nomeE w = exp (π i w)`, the
fourth power of Jacobi's `θ₀₀` agrees with the weight-two Eisenstein-type series
`1 + 8 e + 24 e² + 32 e³ + 24 e⁴` up to `O(‖e‖⁵)` on the half-plane `Im w ≥ 2`.

The coefficients `1, 8, 24, 32, 24` are the numbers of representations of `0, 1, 2, 3, 4` as a
sum of four squares; the sharp input is `quart_bound` (the fourth-power expansion estimate),
combined with the elementary theta `q`-expansion `theta00_pow_series`. -/
theorem UFun_qexp (w : UpperHalfPlane) (hw : 2 ≤ w.im) :
    ‖Work.Kernels.UFun w - (1 + 8 * Work.Asymptotics.nomeE w + 24 * (Work.Asymptotics.nomeE w) ^ 2
      + 32 * (Work.Asymptotics.nomeE w) ^ 3 + 24 * (Work.Asymptotics.nomeE w) ^ 4)‖
      ≤ 10000 * ‖Work.Asymptotics.nomeE w‖ ^ 5 := by
  have hwpos : 0 < w.im := by linarith
  -- `‖nomeE w‖ ≤ 1/2` on the region `Im w ≥ 2`.
  have hhalf : ‖nomeE w‖ ≤ 1 / 2 := by
    rw [norm_nomeE w, Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/2)]
    rw [show (1/2:ℝ)⁻¹ = 2 by norm_num]
    have hpi : (1:ℝ) ≤ Real.pi * w.im := by nlinarith [Real.pi_gt_three, hw]
    calc (2:ℝ) = 1 + 1 := by norm_num
      _ ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
      _ ≤ Real.exp (Real.pi * w.im) := Real.exp_le_exp.mpr hpi
  set e := nomeE w with he
  set r := ‖e‖ with hr
  have hrle : r ≤ 1 / 2 := hhalf
  -- the tail `x₂ = ∑_{n ≥ 0} e^{(n+3)²}` of the theta series beyond the first two terms
  set x₂ : ℂ := ∑' n : ℕ, e ^ ((n+3)^2) with hx₂
  have hx₂b : ‖x₂‖ ≤ 2 * r^9 := by
    rw [hx₂, hr]
    exact norm_tsum_pow_le (e := e) (f := fun n => (n+3)^2) (m := 9) hrle
      (fun n => by nlinarith)
  have hSsum : Summable (fun n : ℕ => e ^ ((n+1)^2)) :=
    summable_pow_of_le (e := e) (f := fun n => (n+1)^2) (m := 1) hrle (fun n => by nlinarith)
  have hS2sum : Summable (fun n : ℕ => e ^ ((n+2)^2)) :=
    summable_pow_of_le (e := e) (f := fun n => (n+2)^2) (m := 4) hrle (fun n => by nlinarith)
  -- split the theta series `∑_{n ≥ 1} e^{n²} = e + (e⁴ + x₂)`
  have hS : (∑' n : ℕ, e ^ ((n+1)^2)) = e + e^4 + x₂ := by
    rw [hSsum.tsum_eq_zero_add]
    have e1 : (∑' n : ℕ, e ^ (((n+1)+1)^2)) = ∑' n : ℕ, e ^ ((n+2)^2) := rfl
    rw [e1, hS2sum.tsum_eq_zero_add]
    have e2 : (∑' n : ℕ, e ^ (((n+2)+1)^2)) = x₂ := by rw [hx₂]
    rw [e2]; ring
  -- the exact `q`-expansion of `θ₀₀`
  have hU : Work.Kernels.UFun w = (1 + 2*e + 2*(e^4 + x₂))^4 := by
    have ht : jacobiTheta (w:ℂ) = 1 + 2 * ∑' n : ℕ, e ^ ((n+1)^2) := by
      rw [theta00_pow_series (w:ℂ) (by rw [UpperHalfPlane.coe_im]; exact hwpos)]
      congr 1
    rw [show Work.Kernels.UFun w = jacobiTheta (w:ℂ)^4 from rfl, ht, hS]
    ring
  have hP : (1 + 8*e + 24*e^2 + 32*e^3 + 24*e^4 : ℂ) = (1 + 2*e)^4 + 8*e^4 := by ring
  rw [hU, hP]
  have hq := quart_bound (2*e) e (e^4 + x₂) x₂ r (by positivity) hrle (by rw [hr])
    (by rw [norm_mul, Complex.norm_ofNat]) rfl hx₂b
  simpa using hq

end Work.Asymptotics
