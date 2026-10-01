import Mathlib
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries
import Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole

open Filter
open scoped Topology

namespace Work.ZeroFreeTables.P9

noncomputable section

/-!
# Derivatives of `logDeriv Γ_ℝ` as a Hurwitz-type series

For `k ≥ 1` and `1 < Re s` we compute the `k`-th derivative of the logarithmic derivative of the
completed Gamma function `Γ_ℝ`:

`(logDeriv Γ_ℝ)^{(k)}(s) = (-1)^{k+1} k! ∑_{n ≥ 0} (1/(s + 2n))^{k+1}`.

The proof is a three-line assembly: on the right half-plane `logDeriv Γ_ℝ` agrees with
`-(log π)/2 + (1/2) ψ(z/2)` (`logDeriv_GammaR_off_pole`), the chain rule for the halving
substitution turns the `k`-th derivative of `ψ(·/2)` into `(1/2)^k ψ^{(k)}(s/2)`, and the
digamma series `digammaDerivSeries` supplies `ψ^{(k)}(s/2) = (-1)^{k+1} k! ∑_n (1/(s/2+n))^{k+1}`;
substituting `s/2 + n = (s + 2n)/2` and collecting the powers of `2` gives the claim.

## Main result

* `logDeriv_GammaR_iteratedDeriv_series`
-/

/-- `(s/2).re = s.re/2`. -/
private lemma div_two_re (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [Complex.div_re]; simp [Complex.normSq]; ring

/-- Chain rule: the `k`-th derivative of `z ↦ f (c·z)` at `x` is `c^k` times the `k`-th
derivative of `f` at `c·x`, assuming only that `f` is `C^k` at `c·x`. -/
private lemma iteratedDeriv_comp_mul_left_of_contDiffAt (c : ℂ) (k : ℕ) {f : ℂ → ℂ} {x : ℂ}
    (hf : ContDiffAt ℂ k f (c * x)) :
    iteratedDeriv k (fun z : ℂ => f (c * z)) x = c ^ k * iteratedDeriv k f (c * x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hcont : Tendsto (fun y : ℂ => c * y) (𝓝 x) (𝓝 (c * x)) :=
      tendsto_const_nhds.mul tendsto_id
    have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℂ (k : ℕ∞) f (c * y) :=
      hcont.eventually ((ContDiffAt.eventually hf (by simp)).mono fun y hy => hy.of_le (by simp))
    have heq : iteratedDeriv k (fun z : ℂ => f (c * z)) =ᶠ[𝓝 x]
        fun y => c ^ k * iteratedDeriv k f (c * y) := by
      filter_upwards [hev] with y hy
      exact ih hy
    rw [heq.deriv_eq, deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul]
    ring

/-- `Γ` is analytic at every point of the open right half-plane. -/
private lemma analyticAt_Gamma_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ Complex.Gamma w := by
  have hsub : Metric.ball w (w.re / 2) ⊆ {z : ℂ | 0 < z.re} := by
    intro z hz
    change 0 < z.re
    have h1 : ‖z - w‖ < w.re / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have h2 : w.re - z.re ≤ ‖z - w‖ := by
      have h3 : w.re - z.re ≤ ‖w - z‖ := by
        simpa only [Complex.sub_re] using Complex.re_le_norm (w - z)
      rwa [norm_sub_rev] at h3
    linarith only [hw, h1, h2]
  have hdiff : DifferentiableOn ℂ Complex.Gamma (Metric.ball w (w.re / 2)) := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (by
      intro m h
      have hzre : 0 < z.re := hsub hz
      have hzm : z.re = -((m : ℝ)) := by rw [h]; simp
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith only [hzre, hzm, hm])).differentiableWithinAt
  exact (hdiff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self (by positivity))

/-- The `k`-th derivative of `z ↦ digamma (z/2)` is `(1/2)^k` times the `k`-th derivative of
digamma at `z/2`. -/
private lemma iteratedDeriv_digamma_div_two (k : ℕ) {w : ℂ} (hw : 0 < w.re) :
    iteratedDeriv k (fun z : ℂ => Complex.digamma (z / 2)) w
      = (1 / 2 : ℂ) ^ k * iteratedDeriv k Complex.digamma (w / 2) := by
  have hw2 : 0 < (w / 2).re := by rw [div_two_re]; linarith
  have hana : AnalyticAt ℂ Complex.digamma (w / 2) := by
    have hG : AnalyticAt ℂ Complex.Gamma (w / 2) := analyticAt_Gamma_of_re_pos hw2
    have hne : Complex.Gamma (w / 2) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m h
      have hre : (w / 2).re = -((m : ℝ)) := by rw [h]; simp
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith only [hre, hm, hw2]
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma / Complex.Gamma) (w / 2) := hG.deriv.div hG hne
    have hfun : Complex.digamma = deriv Complex.Gamma / Complex.Gamma := rfl
    rw [hfun]
    exact h1
  have hfun : (fun z : ℂ => Complex.digamma (z / 2))
      = fun z : ℂ => Complex.digamma ((2 : ℂ)⁻¹ * z) := by
    funext z; congr 1; rw [div_eq_mul_inv, mul_comm]
  have h3 : (2 : ℂ)⁻¹ * w = w / 2 := by ring
  have hdig : ContDiffAt ℂ k Complex.digamma ((2 : ℂ)⁻¹ * w) := by
    rw [h3]; exact hana.contDiffAt
  have h4 : (1 / 2 : ℂ) ^ k = ((2 : ℂ)⁻¹) ^ k := by simp only [one_div]
  have hchain := iteratedDeriv_comp_mul_left_of_contDiffAt (2 : ℂ)⁻¹ k hdig
  rw [h3] at hchain
  rw [hfun, h4]
  exact hchain

/-- For `k ≥ 1` and `1 < Re s`, the `k`-th derivative of `logDeriv Complex.Gammaℝ` at `s` is the
Hurwitz-type series `(-1)^{k+1} k! ∑_{n≥0} (1/(s + 2n))^{k+1}`. -/
theorem logDeriv_GammaR_iteratedDeriv_series (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (logDeriv Complex.Gammaℝ) s
      = (-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
        * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
  have hsre : 0 < s.re := by linarith
  have hk0 : 0 < k := hk
  have hw2 : 0 < (s / 2).re := by rw [div_two_re]; linarith
  -- off the poles of `Γ_ℝ`, its log-derivative is the constant plus `ψ(z/2)/2`
  have hev : logDeriv Complex.Gammaℝ =ᶠ[𝓝 s]
      fun z : ℂ => (-(Complex.log (Real.pi : ℂ)) / 2) + (1 / 2) * Complex.digamma (z / 2) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hsre] with z hz
    have hz2 : ∀ m : ℕ, z / 2 ≠ -((m : ℕ) : ℂ) := by
      intro m h
      have hre : (z / 2).re = -((m : ℝ)) := by rw [h]; simp
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hzre : 0 < (z / 2).re := by rw [div_two_re]; linarith
      linarith only [hre, hm, hzre]
    rw [Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole z hz2]
    ring
  rw [hev.iteratedDeriv_eq k]
  rw [iteratedDeriv_const_add hk0]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_digamma_div_two k (w := s) hsre]
  -- the digamma series at `w = s/2`
  have hHas := Work.LinnikAreas.FarRepel.digammaDerivSeries k hk hw2
  have hterm : ∀ n : ℕ, (1 / (s / 2 + (n : ℂ))) ^ (k + 1)
      = (2 : ℂ) ^ (k + 1) * (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1) := by
    intro n
    have hden : s / 2 + (n : ℂ) = (s + ((2 * n : ℕ) : ℂ)) / 2 := by push_cast; ring
    rw [hden, div_div_eq_mul_div, one_mul,
      show (2 : ℂ) / (s + ((2 * n : ℕ) : ℂ))
        = 2 * (1 / (s + ((2 * n : ℕ) : ℂ))) by ring, mul_pow]
  have hHas' : HasSum (fun n : ℕ =>
      ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * (2 : ℂ) ^ (k + 1))
        * (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))
      (iteratedDeriv k Complex.digamma (s / 2)) :=
    hHas.congr_fun fun n => by rw [hterm n]; ring
  have hval : iteratedDeriv k Complex.digamma (s / 2)
      = ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * (2 : ℂ) ^ (k + 1))
        * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
    rw [← hHas'.tsum_eq, tsum_mul_left]
  rw [hval]
  -- collect the powers of `2`
  have hpow : (1 / 2 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (k + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hkey : (1 / 2 : ℂ) * ((1 / 2) ^ k * (((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
        * (2 : ℂ) ^ (k + 1)) * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))))
      = ((1 / 2 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (k + 1))
          * ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
              * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))) := by
    rw [pow_succ]; ring
  rw [hkey, hpow, one_mul]

end

end Work.ZeroFreeTables.P9
