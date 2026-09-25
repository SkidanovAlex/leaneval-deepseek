import Mathlib
import Submission.Commons.NumberTheory.Zeta.xiE_partialFraction_eq

noncomputable section
open Complex Filter Metric Set Function MeromorphicOn Topology
open scoped Real Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Commons.NumberTheory.Zeta

/-- The entire completion `Ξ(s) = 1/2 + (1/2)·s·(s−1)·Λ₀(s)` (Mathlib's Riemann xi function). -/
private def xiF : ℂ → ℂ :=
  fun z => (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z

private lemma xiF_one : xiF 1 = (1 / 2 : ℂ) := by
  simp [xiF]

private lemma xiF_zero : xiF 0 = (1 / 2 : ℂ) := by
  simp [xiF]

/-- `Ξ'(1) = Λ₀(1)/2`. -/
private lemma deriv_xiF_one : deriv xiF 1 = completedRiemannZeta₀ 1 / 2 := by
  let G : ℂ → ℂ := (fun _ : ℂ => (1 / 2 : ℂ)) +
    (((fun z : ℂ => (1 / 2 : ℂ) * z) * (fun z : ℂ => z - 1)) * completedRiemannZeta₀)
  have hG : HasDerivAt G ((1 / 2 : ℂ) * completedRiemannZeta₀ 1 +
      (((fun z : ℂ => (1 / 2 : ℂ) * z) * (fun z : ℂ => z - 1)) 1) *
        deriv completedRiemannZeta₀ 1) 1 := by
    have ha : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) * z) (1 / 2) 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).const_mul (1 / 2 : ℂ)
    have hb : HasDerivAt (fun z : ℂ => z - 1) (1 : ℂ) 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).sub_const (1 : ℂ)
    have hab : HasDerivAt ((fun z : ℂ => (1 / 2 : ℂ) * z) * (fun z : ℂ => z - 1)) (1 / 2) 1 := by
      have h := ha.mul hb
      simpa using h
    have hc : HasDerivAt (((fun z : ℂ => (1 / 2 : ℂ) * z) * (fun z : ℂ => z - 1)) *
          completedRiemannZeta₀)
        ((1 / 2) * completedRiemannZeta₀ 1 +
          (((fun z : ℂ => (1 / 2 : ℂ) * z) * (fun z : ℂ => z - 1)) 1) *
            deriv completedRiemannZeta₀ 1) 1 := by
      have h := hab.mul (differentiable_completedZeta₀ 1).hasDerivAt
      simpa using h
    have h := (hasDerivAt_const (1 : ℂ) (1 / 2 : ℂ)).add hc
    simpa only [G, zero_add] using h
  have hGeq : G = xiF := by
    funext z
    simp only [G, xiF, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  rw [← hGeq]
  rw [hG.deriv]
  simp only [Pi.mul_apply, Pi.sub_apply]
  ring

/-- `Ξ'(0) = −Λ₀(0)/2`. -/
private lemma deriv_xiF_zero : deriv xiF 0 = -completedRiemannZeta₀ 0 / 2 := by
  let G : ℂ → ℂ := (fun _ : ℂ => (1 / 2 : ℂ)) +
    (((fun z : ℂ => (1 / 2 : ℂ) * z) * (fun z : ℂ => z - 1)) * completedRiemannZeta₀)
  have hG : HasDerivAt G ((-(1 / 2)) * completedRiemannZeta₀ 0 +
      (((fun z : ℂ => (1 / 2 : ℂ) * z) * (fun z : ℂ => z - 1)) 0) *
        deriv completedRiemannZeta₀ 0) 0 := by
    have ha : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) * z) (1 / 2) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (1 / 2 : ℂ)
    have hb : HasDerivAt (fun z : ℂ => z - 1) (1 : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).sub_const (1 : ℂ)
    have hab : HasDerivAt ((fun z : ℂ => (1 / 2 : ℂ) * z) * (fun z : ℂ => z - 1)) (-(1 / 2)) 0 := by
      have h := ha.mul hb
      simpa using h
    have hc : HasDerivAt (((fun z : ℂ => (1 / 2 : ℂ) * z) * (fun z : ℂ => z - 1)) *
          completedRiemannZeta₀)
        ((-(1 / 2)) * completedRiemannZeta₀ 0 +
          (((fun z : ℂ => (1 / 2 : ℂ) * z) * (fun z : ℂ => z - 1)) 0) *
            deriv completedRiemannZeta₀ 0) 0 := by
      have h := hab.mul (differentiable_completedZeta₀ 0).hasDerivAt
      simpa using h
    have h := (hasDerivAt_const (0 : ℂ) (1 / 2 : ℂ)).add hc
    simpa only [G, zero_add] using h
  have hGeq : G = xiF := by
    funext z
    simp only [G, xiF, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  rw [← hGeq]
  rw [hG.deriv]
  simp only [Pi.mul_apply, Pi.sub_apply]
  ring

private lemma logDeriv_xiF_one : logDeriv xiF 1 = completedRiemannZeta₀ 1 := by
  rw [logDeriv_apply, deriv_xiF_one, xiF_one]
  ring

private lemma logDeriv_xiF_zero : logDeriv xiF 0 = -completedRiemannZeta₀ 0 := by
  rw [logDeriv_apply, deriv_xiF_zero, xiF_zero]
  ring

private lemma logDeriv_xiF_diff :
    logDeriv xiF 1 - logDeriv xiF 0 =
      (2 : ℂ) + (Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ)) := by
  rw [logDeriv_xiF_one, logDeriv_xiF_zero, completedRiemannZeta₀_one, completedRiemannZeta₀_zero]
  ring

theorem xi_partialFraction_sum_one :
    Filter.Tendsto (fun R : ℝ =>
      finsum (fun u : ℂ =>
        (((MeromorphicOn.divisor (fun z : ℂ =>
            (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (1 - u) + 1 / u)))
      Filter.atTop (nhds ((2 : ℂ) + (Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ)))) := by
  have hne : (1 / 2 : ℂ) + 1 / 2 * 1 * (1 - 1) * completedRiemannZeta₀ 1 ≠ 0 := by
    have h : (1 / 2 : ℂ) + 1 / 2 * 1 * (1 - 1) * completedRiemannZeta₀ 1 = 1 / 2 := by ring
    rw [h]; norm_num
  have hlim := xiE_partialFraction_eq 1 hne
  have hval : logDeriv (fun z : ℂ =>
        (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z) 1 -
      logDeriv (fun z : ℂ =>
        (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z) 0 =
      (2 : ℂ) + (Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ)) :=
    logDeriv_xiF_diff
  rw [hval] at hlim
  exact hlim

end Commons.NumberTheory.Zeta
