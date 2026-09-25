import Mathlib
import Submission.Commons.NumberTheory.Zeta.xi_partialFraction_sum_one
import Submission.Commons.NumberTheory.Zeta.completedRiemannZeta_zero_re_eq_half
import Submission.Commons.Analysis.Complex.inv_one_sub_add_inv_eq_inv_normSq
import Submission.Commons.Analysis.MeromorphicOn.divisor_closedBall_mono
import Submission.Commons.Analysis.Complex.re_finsum

open Complex Filter Metric Set Function MeromorphicOn Topology
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- `xiF` is the (entire) Riemann xi function `Ξ(s) = 1/2 + 1/2·s·(s−1)·Λ₀(s)`.  It equals
`1/2·s·(s−1)·Λ(s)` away from `0` and `1`. -/
private lemma completedRiemannZeta_eq_zero_of_xiF_eq_zero {u : ℂ}
    (hu : XiPF.xiF u = 0) : completedRiemannZeta u = 0 := by
  have hu' : (1/2 : ℂ) + (1/2 : ℂ) * u * (u - 1) * completedRiemannZeta₀ u = 0 := hu
  have h0 : u ≠ 0 := by intro h; rw [h] at hu'; norm_num at hu'
  have h1 : u ≠ 1 := by intro h; rw [h] at hu'; norm_num at hu'
  have hu0 : u - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hΛ₀ : completedRiemannZeta₀ u = completedRiemannZeta u + 1/u + 1/(1-u) := by
    have := completedRiemannZeta_eq u
    rw [this]; ring
  have hkey : (1/2 : ℂ) + (1/2 : ℂ) * u * (u - 1) *
      (completedRiemannZeta u + 1/u + 1/(1-u)) =
      (1/2 : ℂ) * u * (u - 1) * completedRiemannZeta u := by
    field_simp
    ring
  rw [hΛ₀, hkey] at hu'
  have hhalf : (1/2 : ℂ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hu' with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hhalf
      · exact absurd h h0
    · exact absurd h hu0
  · exact h

/-- The real part of `d · (‖u‖²)⁻¹` for `d : ℤ` is `d / ‖u‖²`. -/
private lemma re_int_mul_inv_normSq (d : ℤ) (u : ℂ) :
    ((d : ℂ) * ((‖u‖ ^ 2)⁻¹ : ℂ)).re = (d : ℝ)/‖u‖^2 := by
  rw [show (d : ℂ) * ((‖u‖ ^ 2)⁻¹ : ℂ) = (((d:ℝ)/‖u‖^2 : ℝ) : ℂ) by
    rw [Complex.ofReal_div]; push_cast; ring]
  exact Complex.ofReal_re _

/-- Pointwise: at a point where the divisor of `xiF` is non-zero (hence a zero of `xiF`, on the
critical line by `h`), the partial-fraction weight `1/(1−u) + 1/u` equals `1/‖u‖²`. -/
private lemma pointwise_term (h : RiemannHypothesis) {r : ℝ} {u : ℂ}
    (hd : MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r) u ≠ 0) :
    (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r) u : ℤ) : ℂ) *
        (1 / (1 - u) + 1 / u)).re =
      (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r) u : ℤ) : ℝ)) / ‖u‖ ^ 2 := by
  have hFx : XiPF.xiF u = 0 := XiPF.xiF_divisor_ne_zero_is_zero hd
  have hΛ : completedRiemannZeta u = 0 := completedRiemannZeta_eq_zero_of_xiF_eq_zero hFx
  have h0 : u ≠ 0 := by
    intro hu; rw [hu] at hFx; norm_num [XiPF.xiF] at hFx
  have h1 : u ≠ 1 := by
    intro hu; rw [hu] at hFx; norm_num [XiPF.xiF] at hFx
  have hre : u.re = 1/2 := completedRiemannZeta_zero_re_eq_half h hΛ h0 h1
  rw [Commons.Analysis.Complex.inv_one_sub_add_inv_eq_inv_normSq hre]
  exact re_int_mul_inv_normSq _ _

/-- **Zero-sum bound.**  Under the Riemann hypothesis, for every radius `R`, the sum of the
multiplicities of the zeros of the completed ξ-function inside the closed ball of radius `R`,
weighted by `1/‖u‖²`, is at most `2 + γ − log(4π)`.

Indeed, under RH every zero `u` of `Ξ` lies on the critical line, whence
`1/(1−u) + 1/u = 1/‖u‖²`; so the real weighted sum coincides with the real part of the
partial-fraction sum, which converges (by `xi_partialFraction_sum_one`) to
`logDeriv Ξ(1) − logDeriv Ξ(0) = 2 + γ − log(4π)`.  Monotonicity of the partial sums in `R`
then gives the bound. -/
theorem zeroSum_finsum_le_beta (h : RiemannHypothesis) (R : ℝ) :
    finsum (fun u : ℂ =>
      (((MeromorphicOn.divisor (fun z : ℂ =>
          (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) / ‖u‖ ^ 2)
      ≤ 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  let L : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)
  let S : ℝ → ℝ := fun r => finsum (fun u : ℂ =>
      (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r)) u : ℤ) : ℝ) / ‖u‖ ^ 2)
  let T : ℝ → ℂ := fun r => finsum (fun u : ℂ =>
      (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r)) u : ℤ) : ℂ) *
        (1 / (1 - u) + 1 / u))
  change S R ≤ 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)
  -- The complex partial-fraction partial sums converge to `L`.
  have hT : Tendsto T atTop (nhds (L : ℂ)) := by
    have hlim := Commons.NumberTheory.Zeta.xi_partialFraction_sum_one
    have hlog : Complex.log (4 * (Real.pi : ℂ)) = (Real.log (4 * Real.pi) : ℂ) := by
      rw [show (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.ofReal_log (by positivity)).symm
    have hlim' : (2 : ℂ) + (Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ))
        = (L : ℂ) := by
      rw [hlog]; simp only [L]; push_cast; ring
    rw [hlim'] at hlim
    change Tendsto (fun r : ℝ => finsum (fun u : ℂ =>
      (((MeromorphicOn.divisor (fun z : ℂ =>
          (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
        (Metric.closedBall 0 r)) u : ℤ) : ℂ) * (1 / (1 - u) + 1 / u)))
      atTop (nhds (L : ℂ))
    exact hlim
  -- `S r` is the real part of `T r`.
  have hST : ∀ r : ℝ, S r = (T r).re := by
    intro r
    have hfin : (Function.support (fun u : ℂ =>
        MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r) u)).Finite :=
      XiPF.xiF_divisor_support_finite r
    have hfinC : (Function.support (fun u : ℂ =>
        (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r)) u : ℤ) : ℂ) *
          (1 / (1 - u) + 1 / u))).Finite :=
      hfin.subset (fun u hu => by
        simp only [Function.mem_support] at hu ⊢
        intro h0; exact hu (by simp [h0]))
    change finsum (fun u : ℂ =>
        (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r)) u : ℤ) : ℝ) / ‖u‖ ^ 2) =
      (finsum (fun u : ℂ =>
        (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r)) u : ℤ) : ℂ) *
          (1 / (1 - u) + 1 / u))).re
    rw [Commons.Analysis.Complex.re_finsum hfinC]
    apply finsum_congr
    intro u
    by_cases hd : MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r) u = 0
    · simp [hd]
    · exact (pointwise_term h hd).symm
  have hStend : Tendsto S atTop (nhds L) := by
    have h1 : Tendsto (fun r => (T r).re) atTop (nhds L) := by
      have hcomp : (Complex.re ∘ T) = (fun r => (T r).re) := rfl
      have := (Complex.continuous_re.tendsto (L : ℂ)).comp hT
      rw [hcomp] at this
      simpa [Complex.ofReal_re] using this
    simpa only [show S = (fun r => (T r).re) from funext hST] using h1
  -- `S` is monotone in `R`.
  have hmono : Monotone S := by
    intro r r' hrr
    have hd : ∀ u : ℂ, (MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r)) u ≤
        (MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r')) u :=
      fun u => Commons.Analysis.MeromorphicOn.divisor_closedBall_mono XiPF.xiF_diff hrr u
    have hfr : (Function.support (fun u : ℂ =>
        (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r)) u : ℤ) : ℝ) /
          ‖u‖ ^ 2)).Finite :=
      (XiPF.xiF_divisor_support_finite r).subset (fun u hu => by
        simp only [Function.mem_support] at hu ⊢
        intro h0; exact hu (by simp [h0]))
    have hfr' : (Function.support (fun u : ℂ =>
        (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r')) u : ℤ) : ℝ) /
          ‖u‖ ^ 2)).Finite :=
      (XiPF.xiF_divisor_support_finite r').subset (fun u hu => by
        simp only [Function.mem_support] at hu ⊢
        intro h0; exact hu (by simp [h0]))
    simp only [S]
    apply finsum_le_finsum' hfr hfr'
    intro u
    have hcast : (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r)) u : ℤ) : ℝ) ≤
        (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r')) u : ℤ) : ℝ) := by
      exact_mod_cast hd u
    change (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r)) u : ℤ) : ℝ) / ‖u‖ ^ 2 ≤
        (((MeromorphicOn.divisor XiPF.xiF (Metric.closedBall 0 r')) u : ℤ) : ℝ) / ‖u‖ ^ 2
    exact div_le_div_of_nonneg_right hcast (by positivity)
  -- A monotone sequence converging to `L` is bounded above by `L`.
  have hle : S R ≤ L := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hStend ?_
    exact (eventually_ge_atTop R).mono (fun r hr => hmono hr)
  exact hle

end Commons.NumberTheory.Zeta
