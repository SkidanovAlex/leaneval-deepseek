import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg
import Submission.Commons.NumberTheory.Zeta.xiE_zeroCount
import Submission.Commons.Analysis.MeromorphicOn.meromorphicOrderAt_eq_of_logDeriv_sub_pole
import Submission.Commons.NumberTheory.Zeta.trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos

open Complex Filter Metric
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.Zeta

noncomputable section

/-! ## The zero-count bound for `ζ₁` on balls centred at the origin

The entire completion `ζ₁ = (s-1)ζ(s)` has, inside the ball `|s| ≤ R`, the nontrivial zeros
of `ζ` (in the critical strip, counted with multiplicity) together with the trivial zeros
`-2(n+1)`.  The nontrivial zeros form exactly the zeros of the Riemann xi function `Ξ`, whose
divisor sum was bounded by `xiE_zeroCount`; the trivial zeros are simple and there are at most
`R` of them inside the ball.  This gives the `O(R log R)` bound.
-/

/-- The entire Riemann xi function `Ξ(s) = 1/2 + (1/2)·s·(s−1)·Λ₀(s)`. -/
noncomputable def xiZfun : ℂ → ℂ :=
  fun s => (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s

lemma xiZfun_differentiable : Differentiable ℂ xiZfun := by
  change Differentiable ℂ (fun s : ℂ =>
    (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s)
  have h1 : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) := by fun_prop
  have h2 : Differentiable ℂ (fun s : ℂ => completedRiemannZeta₀ s) :=
    differentiable_completedZeta₀
  exact (differentiable_const (1 / 2 : ℂ)).add (h1.mul h2)

/-- Nonnegativity of the divisor of `Ξ` on a closed ball (it is entire). -/
lemma xiZfun_divisor_nonneg (R : ℝ) (u : ℂ) :
    (0 : ℤ) ≤ (MeromorphicOn.divisor xiZfun (Metric.closedBall 0 R)) u := by
  have han : AnalyticOnNhd ℂ xiZfun (Metric.closedBall 0 R) :=
    fun z _ => xiZfun_differentiable.analyticAt z
  exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg han u

/-- The prefactor `s ↦ (1/2)·s·Γℝ(s)` relating `Ξ` to `riemannZeta₁`. -/
private def xiHead (s : ℂ) : ℂ := (1 / 2 : ℂ) * s * Complex.Gammaℝ s

private lemma xiHead_analyticAt {ρ : ℂ} (hre : 0 < ρ.re) : AnalyticAt ℂ xiHead ρ := by
  have hGinv : AnalyticAt ℂ (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) ρ :=
    Complex.differentiable_Gammaℝ_inv.analyticAt ρ
  have hne : ((fun z : ℂ => (Complex.Gammaℝ z)⁻¹) ρ) ≠ 0 := by
    simpa using inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hre)
  have hG : AnalyticAt ℂ (fun z : ℂ => Complex.Gammaℝ z) ρ :=
    (hGinv.inv hne).congr (by filter_upwards with z; simp)
  exact (analyticAt_const.mul analyticAt_id).mul hG

private lemma xiHead_ne_zero {ρ : ℂ} (hre : 0 < ρ.re) : xiHead ρ ≠ 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  unfold xiHead
  exact mul_ne_zero (mul_ne_zero (by norm_num) hρ0) (Complex.Gammaℝ_ne_zero_of_re_pos hre)

/-- Near any point of `Re s > 0` (other than `1`), `Ξ` agrees with `(1/2)·s·Γℝ(s)·ζ₁(s)`. -/
private lemma xiZfun_eventuallyEq {ρ : ℂ} (hre : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    xiZfun =ᶠ[𝓝[≠] ρ] xiHead * riemannZeta₁ := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_Ioi.preimage Complex.continuous_re
  have hre_nhds : ∀ᶠ z in 𝓝 ρ, 0 < z.re := hopen.mem_nhds hre
  have h1_nhds : ∀ᶠ z in 𝓝 ρ, z ≠ 1 :=
    isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hρ1)
  filter_upwards [hre_nhds.filter_mono nhdsWithin_le_nhds,
    h1_nhds.filter_mono nhdsWithin_le_nhds] with z hzre hz1
  have hz0 : z ≠ 0 := by
    intro h
    have h0 : z.re = 0 := by rw [h]; simp
    linarith
  have hzG : 0 < z.re := hzre
  have hG : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hzG
  have hΛ0 : completedRiemannZeta₀ z = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
    rw [completedRiemannZeta_eq]; ring
  have hΛ : completedRiemannZeta z = Complex.Gammaℝ z * riemannZeta z := by
    rw [riemannZeta_def_of_ne_zero hz0]
    field_simp
  have hζ : riemannZeta₁ z = (z - 1) * riemannZeta z := by
    rw [riemannZeta_eq_inv_sub_mul hz1]
    field_simp
  simp only [xiZfun, xiHead, Pi.mul_apply]
  rw [hΛ0, hΛ, hζ]
  field_simp
  ring

/-- At a zero `ρ` of `ζ₁` in the critical strip `0 < Re ρ < 1`, the multiplicity `zeta1Order ρ`
is the divisor of `Ξ` on the closed ball. -/
lemma zeta1Order_eq_xiZDivisor_ball {R : ℝ} (hR : 0 ≤ R) {ρ : ℂ}
    (hρ : riemannZeta₁ ρ = 0) (hρR : ‖ρ‖ ≤ R) (hre : 0 < ρ.re) (hre2 : ρ.re < 1) :
    (zeta1Order ρ : ℤ) = (MeromorphicOn.divisor xiZfun (Metric.closedBall 0 R)) ρ := by
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, riemannZeta₁_one] at hρ
    exact one_ne_zero hρ
  have hρK : ρ ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hρR
  have hξmero : MeromorphicOn xiZfun (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => (xiZfun_differentiable.analyticAt z).meromorphicAt
  have hordξ : meromorphicOrderAt xiZfun ρ = meromorphicOrderAt riemannZeta₁ ρ := by
    rw [meromorphicOrderAt_congr (xiZfun_eventuallyEq hre hρ1)]
    exact meromorphicOrderAt_mul_of_ne_zero (xiHead_analyticAt hre) (xiHead_ne_zero hre)
  obtain ⟨hm, hF⟩ := Classical.choose_spec (zeta1_logDeriv_pole_removal ρ hρ)
  have hordf :=
    Commons.Analysis.MeromorphicOn.meromorphicOrderAt_eq_of_logDeriv_sub_pole
      (differentiable_riemannZeta₁.analyticAt ρ) hρ
      (riemannZeta₁_not_eventually_zero ρ) hm hF
  have hzeta : zeta1Order ρ = Classical.choose (zeta1_logDeriv_pole_removal ρ hρ) := by
    rw [zeta1Order, dif_pos hρ]
  have hcast : ((Classical.choose (zeta1_logDeriv_pole_removal ρ hρ) : ℕ) : ℤ) =
      (zeta1Order ρ : ℤ) :=
    (congrArg (fun n : ℕ => (n : ℤ)) hzeta).symm
  rw [MeromorphicOn.divisor_apply hξmero hρK, hordξ, hordf, hcast]
  simp

/-! ### Simplicity of the trivial zeros of `ζ₁` -/

/-- A helper: differentiability at every point of a ball gives analyticity at the centre. -/
lemma analyticAt_of_ball {f : ℂ → ℂ} {x : ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ y : ℂ, ‖y - x‖ < r → DifferentiableAt ℂ f y) : AnalyticAt ℂ f x := by
  apply DifferentiableOn.analyticAt (s := Metric.ball x r)
  · intro y hy
    exact (h y (by simpa [Metric.mem_ball, dist_eq_norm] using hy)).differentiableWithinAt
  · exact Metric.ball_mem_nhds x hr

/-- `Γ` is analytic at every point of the half-plane `Re ≥ 3`. -/
lemma analyticAt_Gamma_of_re_ge_three {x : ℂ} (hx : 3 ≤ x.re) :
    AnalyticAt ℂ Complex.Gamma x := by
  apply analyticAt_of_ball (r := 1) (by norm_num)
  intro y hy
  apply Complex.differentiableAt_Gamma y
  intro m hm
  have hmm : (-(m:ℂ)).re = -(m:ℝ) := by simp
  have h1 : |y.re - x.re| ≤ ‖y - x‖ := by
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (y - x)
  have h2 := abs_lt.mp (lt_of_le_of_lt h1 hy)
  have hyr : 0 < y.re := by linarith [h2.1, hx]
  have := congrArg Complex.re hm
  rw [hmm] at this
  have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  linarith

/-- `ζ` is analytic at every point of the half-plane `Re ≥ 3`. -/
lemma analyticAt_riemannZeta_of_re_ge_three {x : ℂ} (hx : 3 ≤ x.re) :
    AnalyticAt ℂ riemannZeta x := by
  apply analyticAt_of_ball (r := 1) (by norm_num)
  intro y hy
  apply differentiableAt_riemannZeta
  intro hcon
  have h1 : |y.re - x.re| ≤ ‖y - x‖ := by
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (y - x)
  have h2 := abs_lt.mp (lt_of_le_of_lt h1 hy)
  have hyr : 1 < y.re := by linarith [h2.1, hx]
  rw [hcon] at hyr; simp at hyr

/-- `s ↦ sin (π s / 2)` has a simple zero at every negative even integer. -/
lemma meromorphicOrderAt_sin_pi_half_neg_two_mul (m : ℕ) :
    meromorphicOrderAt (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z / 2))
      (-(2 * (m : ℂ))) = 1 := by
  set ρ : ℂ := -(2 * (m : ℂ)) with hρ
  have hf : AnalyticAt ℂ (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z / 2)) ρ := by
    apply Differentiable.analyticAt
    fun_prop
  have hz : Complex.sin ((Real.pi : ℂ) * ρ / 2) = 0 := by
    have harg : (Real.pi : ℂ) * ρ / 2 = -((m : ℂ) * (Real.pi : ℂ)) := by
      rw [hρ]; ring
    rw [harg, Complex.sin_neg, Complex.sin_nat_mul_pi, neg_zero]
  have hd : deriv (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z / 2)) ρ ≠ 0 := by
    have hlin : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z / 2) ((Real.pi : ℂ) / 2) ρ := by
      have h := (hasDerivAt_const (x := ρ) (c := (Real.pi : ℂ))).mul (hasDerivAt_id ρ)
      have h' := h.div_const 2
      simpa using h'
    have hcomp := (Complex.hasDerivAt_sin ((Real.pi : ℂ) * ρ / 2)).comp ρ hlin
    have hderiv : deriv (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z / 2)) ρ
        = Complex.cos ((Real.pi : ℂ) * ρ / 2) * ((Real.pi : ℂ) / 2) := by
      change deriv (Complex.sin ∘ fun z : ℂ => (Real.pi : ℂ) * z / 2) ρ
        = Complex.cos ((Real.pi : ℂ) * ρ / 2) * ((Real.pi : ℂ) / 2)
      exact hcomp.deriv
    rw [hderiv]
    have hc : Complex.cos ((Real.pi : ℂ) * ρ / 2) = ((-1 : ℂ) ^ m) := by
      have harg : (Real.pi : ℂ) * ρ / 2 = -((m : ℂ) * (Real.pi : ℂ)) := by
        rw [hρ]; ring
      rw [harg, Complex.cos_neg]
      rw [show (m : ℂ) * (Real.pi : ℂ) = (((m : ℝ) * Real.pi : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_cos, Real.cos_nat_mul_pi]
      push_cast
      ring
    rw [hc]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)
  have h1 := hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hd
  rw [hf.meromorphicOrderAt_eq, h1]
  simp

/-- `ζ` has a simple zero at every negative even integer `-2(n+1)`, by the functional
equation (all other factors are analytic and non-vanishing there). -/
lemma meromorphicOrderAt_riemannZeta_neg_two_mul_succ (n : ℕ) :
    meromorphicOrderAt riemannZeta (-(2 * ((n : ℂ) + 1))) = 1 := by
  set ρ : ℂ := -(2 * ((n : ℂ) + 1)) with hρ
  let G : ℂ → ℂ := fun u =>
    (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (u - 1) * Complex.Gamma (1 - u) * riemannZeta (1 - u)
  let f : ℂ → ℂ := fun u => Complex.sin ((Real.pi : ℂ) * u / 2)
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hre1 : (1 - ρ).re = 1 + 2 * ((n : ℝ) + 1) := by
    rw [hρ]
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.mul_re, Complex.add_re,
      Complex.natCast_re]
    norm_num
  have hopen : IsOpen {u : ℂ | (1 : ℝ) < (1 - u).re} :=
    isOpen_Ioi.preimage (Complex.continuous_re.comp (continuous_const.sub continuous_id))
  have hmem : {u : ℂ | (1 : ℝ) < (1 - u).re} ∈ 𝓝 ρ := by
    apply hopen.mem_nhds
    show (1:ℝ) < (1 - ρ).re
    rw [hre1]; linarith
  have hfac : riemannZeta =ᶠ[𝓝[≠] ρ] (G * f) := by
    filter_upwards [nhdsWithin_le_nhds hmem] with u hu
    have hcond1 : ∀ k : ℕ, (1 - u) ≠ -↑k := by
      intro k hk
      have hm : (1 - u).re = -↑k := by rw [hk]; simp
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith [hu, hm, hk0]
    have hcond2 : (1 - u) ≠ 1 := by
      intro hk
      have hm : (1 - u).re = 1 := by rw [hk]; simp
      linarith [hu, hm]
    have hFE := riemannZeta_one_sub hcond1 hcond2
    have hu' : (1 : ℂ) - (1 - u) = u := by ring
    rw [hu'] at hFE
    have hcos : Complex.cos ((Real.pi : ℂ) * (1 - u) / 2) =
        Complex.sin ((Real.pi : ℂ) * u / 2) := by
      have : (Real.pi : ℂ) * (1 - u) / 2 = (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * u / 2 := by ring
      rw [this, Complex.cos_pi_div_two_sub]
    have hcp : (2 * (Real.pi : ℂ)) ^ (-(1 - u)) = (2 * (Real.pi : ℂ)) ^ (u - 1) := by
      congr 1; ring
    rw [hcos, hcp] at hFE
    rw [hFE]
    show (2 * (2 * (Real.pi:ℂ)) ^ (u-1) * Complex.Gamma (1-u)
          * Complex.sin ((Real.pi:ℂ)*u/2) * riemannZeta (1-u))
        = (2 * (2 * (Real.pi:ℂ)) ^ (u-1) * Complex.Gamma (1-u) * riemannZeta (1-u))
          * Complex.sin ((Real.pi:ℂ)*u/2)
    ring
  have hGan : AnalyticAt ℂ G ρ := by
    have h1 : AnalyticAt ℂ (fun u : ℂ => (2 * (Real.pi : ℂ)) ^ (u - 1)) ρ := by
      apply analyticAt_of_ball (r := 1) (by norm_num)
      intro y hy
      exact (differentiableAt_id.sub_const 1).const_cpow
        (Or.inl (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    have hΓ : AnalyticAt ℂ Complex.Gamma (1 - ρ) :=
      analyticAt_Gamma_of_re_ge_three (by rw [hre1]; linarith)
    have hζ : AnalyticAt ℂ riemannZeta (1 - ρ) :=
      analyticAt_riemannZeta_of_re_ge_three (by rw [hre1]; linarith)
    have hinner : AnalyticAt ℂ (fun u : ℂ => 1 - u) ρ := by
      apply Differentiable.analyticAt; fun_prop
    have h2 : AnalyticAt ℂ (fun u : ℂ => Complex.Gamma (1 - u)) ρ := by
      have hc := hΓ.comp hinner
      simpa only [Function.comp_def] using hc
    have h3 : AnalyticAt ℂ (fun u : ℂ => riemannZeta (1 - u)) ρ := by
      have hc := hζ.comp hinner
      simpa only [Function.comp_def] using hc
    have h2c : AnalyticAt ℂ (fun _ : ℂ => (2:ℂ)) ρ := analyticAt_const
    have h := ((h2c.mul h1).mul h2).mul h3
    refine h.congr ?_
    filter_upwards with u
    simp only [G, Pi.mul_apply]
  have hG0 : G ρ ≠ 0 := by
    simp only [G]
    have h1 : (2 * (Real.pi : ℂ)) ^ (ρ - 1) ≠ 0 := by
      rw [cpow_ne_zero_iff]
      exact Or.inl (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have h2 : Complex.Gamma (1 - ρ) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      rw [hre1]; linarith
    have h3 : riemannZeta (1 - ρ) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      rw [hre1]; linarith
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h1) h2) h3
  have hgoal : meromorphicOrderAt (G * f) ρ = 1 := by
    rw [meromorphicOrderAt_mul_of_ne_zero hGan hG0]
    show meromorphicOrderAt (fun u : ℂ => Complex.sin ((Real.pi : ℂ) * u / 2)) ρ = 1
    have hρ' : ρ = -(2 * (((n+1 : ℕ) : ℂ))) := by rw [hρ]; push_cast; ring
    rw [hρ']
    exact meromorphicOrderAt_sin_pi_half_neg_two_mul (n+1)
  rw [meromorphicOrderAt_congr hfac]
  exact hgoal

/-- The entire completion `ζ₁ = (s-1)ζ(s)` has a simple zero at every negative even integer. -/
lemma meromorphicOrderAt_riemannZeta₁_neg_two_mul_succ (n : ℕ) :
    meromorphicOrderAt riemannZeta₁ (-(2 * ((n : ℂ) + 1))) = 1 := by
  set ρ : ℂ := -(2 * ((n : ℂ) + 1)) with hρ
  have hne1 : ρ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hρ] at this
    simp at this
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hev : riemannZeta₁ =ᶠ[𝓝[≠] ρ] ((fun z : ℂ => z - 1) * riemannZeta) := by
    have h1 : ∀ᶠ z in 𝓝 ρ, z ≠ 1 := isOpen_compl_singleton.mem_nhds (by simpa using hne1)
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds] with z hz1
    have h := riemannZeta_eq_inv_sub_mul hz1
    simp only [Pi.mul_apply]
    rw [h]
    field_simp
  have hgan : AnalyticAt ℂ (fun z : ℂ => z - 1) ρ := by fun_prop
  rw [meromorphicOrderAt_congr hev]
  rw [meromorphicOrderAt_mul_of_ne_zero hgan (sub_ne_zero.mpr hne1)]
  exact meromorphicOrderAt_riemannZeta_neg_two_mul_succ n

/-- The multiplicity `zeta1Order` at a trivial zero `-2(n+1)` is `1`. -/
lemma zeta1Order_neg_two_mul_succ (n : ℕ) :
    zeta1Order (-(2 * ((n : ℂ) + 1))) = 1 := by
  set ρ : ℂ := -(2 * ((n : ℂ) + 1)) with hρ
  have hne1 : ρ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hρ] at this
    simp at this
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hρzero : riemannZeta₁ ρ = 0 := by
    have hz : riemannZeta ρ = 0 := by
      have h := riemannZeta_neg_two_mul_nat_add_one n
      have : -(2 * ((n:ℂ) + 1)) = -2 * ((n:ℂ) + 1) := by ring
      rw [hρ, this]; exact h
    have h := riemannZeta_eq_inv_sub_mul hne1
    have h' : (ρ - 1) * riemannZeta ρ = riemannZeta₁ ρ := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne1), one_mul]
    rw [← h', hz, mul_zero]
  have hmero : meromorphicOrderAt riemannZeta₁ ρ = 1 :=
    meromorphicOrderAt_riemannZeta₁_neg_two_mul_succ n
  have hspec := Classical.choose_spec (zeta1_logDeriv_pole_removal ρ hρzero)
  have hdef : zeta1Order ρ = Classical.choose (zeta1_logDeriv_pole_removal ρ hρzero) := by
    rw [zeta1Order, dif_pos hρzero]
  have hord := Commons.Analysis.MeromorphicOn.meromorphicOrderAt_eq_of_logDeriv_sub_pole
    (differentiable_riemannZeta₁.analyticAt ρ) hρzero
    (riemannZeta₁_not_eventually_zero ρ) hspec.1 hspec.2
  have hkey : ((zeta1Order ρ : ℤ) : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) := by
    rw [hdef]
    rw [← hord]
    exact hmero
  have hz : (zeta1Order ρ : ℤ) = 1 := WithTop.coe_inj.mp hkey
  exact_mod_cast hz

/-! ### The ball count -/

/-- **Nontrivial part**: for `R ≥ 2` the `ζ₁`-zeros with `Re > 0` inside `|s| ≤ R` contribute at
most the `Ξ`-divisor sum, which is bounded by `xiE_zeroCount`. -/
lemma zeta1_nontrivial_sum_le {cxi R : ℝ} (hR : 0 ≤ R) (hR2 : 2 ≤ R)
    (hcxi : ∀ R' : ℝ, 2 ≤ R' →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiZfun
          (Metric.closedBall 0 R')) u : ℤ) : ℝ)) ≤ cxi * R' * (Real.log (R' + 2) + 2)) :
    (∑ ρ ∈ (zetaZeroBallFin R hR).filter (fun ρ => 0 < ρ.re), (zeta1Order ρ : ℝ))
      ≤ cxi * R * (Real.log (R + 2) + 2) := by
  classical
  set S : Finset ℂ := (zetaZeroBallFin R hR).filter (fun ρ => 0 < ρ.re) with hS
  have hpt : ∀ ρ ∈ S, (zeta1Order ρ : ℝ) =
      (((MeromorphicOn.divisor xiZfun (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) := by
    intro ρ hρ
    rw [hS, Finset.mem_filter] at hρ
    obtain ⟨hρZ, hρre⟩ := hρ
    obtain ⟨hball, hz1⟩ := (zetaZeroBallFin_spec R hR ρ).mp hρZ
    have hnorm : ‖ρ‖ ≤ R := by rwa [Metric.mem_closedBall, dist_zero_right] at hball
    have hre1 : ρ.re < 1 := by
      by_contra h
      exact zeta1_ne_zero_of_one_le_re (not_lt.mp h) hz1
    have hEq := zeta1Order_eq_xiZDivisor_ball hR hz1 hnorm hρre hre1
    have hcast : ((zeta1Order ρ : ℤ) : ℝ) =
        (((MeromorphicOn.divisor xiZfun (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) := by
      rw [hEq]
    simpa using hcast
  set g : ℂ → ℝ := fun u => (((MeromorphicOn.divisor xiZfun
      (Metric.closedBall 0 R)) u : ℤ) : ℝ) with hg
  have hgnn : ∀ u, 0 ≤ g u := fun u => by
    have h := xiZfun_divisor_nonneg R u
    have h' : (0 : ℝ) ≤ (((MeromorphicOn.divisor xiZfun
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by exact_mod_cast h
    simpa only [hg] using h'
  have hfin : (Function.support g).Finite := by
    have hD : (Function.support (MeromorphicOn.divisor xiZfun
        (Metric.closedBall 0 R))).Finite :=
      (MeromorphicOn.divisor xiZfun (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall (0 : ℂ) R)
    rw [hg]
    refine hD.subset ?_
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by simp [h0])
  have hstep : (∑ ρ ∈ S, g ρ) ≤ ∑ᶠ u, g u := by
    rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset)
      (fun x hx => hfin.mem_toFinset.mpr hx)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ρ hρ
      have hpt' : (zeta1Order ρ : ℝ) = g ρ := hpt ρ hρ
      rw [hfin.mem_toFinset]
      rw [Function.mem_support]
      intro hzero
      have hpos : (0:ℝ) < (zeta1Order ρ : ℝ) := by
        rw [hS, Finset.mem_filter] at hρ
        obtain ⟨hρZ, _⟩ := hρ
        have hge := zeta1Order_ge_one (by
          obtain ⟨hball, hz1⟩ := (zetaZeroBallFin_spec R hR ρ).mp hρZ
          exact hz1)
        exact_mod_cast hge
      have : (zeta1Order ρ : ℝ) = 0 := by rw [hpt', hzero]
      linarith
    · intro ρ _ _; exact hgnn ρ
  calc (∑ ρ ∈ S, (zeta1Order ρ : ℝ))
      = ∑ ρ ∈ S, g ρ := Finset.sum_congr rfl (fun ρ hρ => hpt ρ hρ)
    _ ≤ ∑ᶠ u, g u := hstep
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor xiZfun
          (Metric.closedBall 0 R)) u : ℤ) : ℝ)) := by
        apply finsum_congr; intro u; simp only [hg]
    _ ≤ cxi * R * (Real.log (R + 2) + 2) := hcxi R hR2

/-- **Trivial part**: for `R ≥ 2` the `ζ₁`-zeros with `Re ≤ 0` inside `|s| ≤ R` are the trivial
zeros, each of multiplicity one, and there are at most `R` of them. -/
lemma zeta1_trivial_sum_le (R : ℝ) (hR : 0 ≤ R) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ (zetaZeroBallFin R hR).filter (fun ρ => ¬ 0 < ρ.re), (zeta1Order ρ : ℝ)) ≤ R := by
  classical
  have hpt : ∀ ρ ∈ (zetaZeroBallFin R hR).filter (fun ρ => ¬ 0 < ρ.re),
      (zeta1Order ρ : ℝ) = 1 := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hρZ, hρre⟩ := hρ
    obtain ⟨hball, hz1⟩ := (zetaZeroBallFin_spec R hR ρ).mp hρZ
    have hρne1 : ρ ≠ 1 := by
      intro h; rw [h] at hρre; norm_num at hρre
    have hζ : riemannZeta ρ = 0 := by
      have hh := riemannZeta_eq_inv_sub_mul hρne1
      rw [hh, hz1, mul_zero]
    obtain ⟨n, hn⟩ := trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos hζ (not_lt.mp hρre)
    rw [hn]
    exact_mod_cast zeta1Order_neg_two_mul_succ n
  have hcard : (∑ ρ ∈ (zetaZeroBallFin R hR).filter (fun ρ => ¬ 0 < ρ.re), (zeta1Order ρ : ℝ))
      = (((zetaZeroBallFin R hR).filter (fun ρ => ¬ 0 < ρ.re)).card : ℝ) := by
    have h1 : (∑ ρ ∈ (zetaZeroBallFin R hR).filter (fun ρ => ¬ 0 < ρ.re), (zeta1Order ρ : ℝ))
        = ∑ ρ ∈ (zetaZeroBallFin R hR).filter (fun ρ => ¬ 0 < ρ.re), (1 : ℝ) :=
      Finset.sum_congr rfl hpt
    rw [h1]; simp
  rw [hcard]
  have hsub : (zetaZeroBallFin R hR).filter (fun ρ => ¬ 0 < ρ.re) ⊆
      (Finset.Icc 1 (Nat.ceil (R / 2))).image (fun m : ℕ => -((2 : ℂ) * (m : ℂ))) := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hρZ, hρre⟩ := hρ
    obtain ⟨hball, hz1⟩ := (zetaZeroBallFin_spec R hR ρ).mp hρZ
    have hnorm : ‖ρ‖ ≤ R := by rwa [Metric.mem_closedBall, dist_zero_right] at hball
    have hρne1 : ρ ≠ 1 := by
      intro h; rw [h] at hρre; norm_num at hρre
    have hζ : riemannZeta ρ = 0 := by
      have hh := riemannZeta_eq_inv_sub_mul hρne1
      rw [hh, hz1, mul_zero]
    obtain ⟨n, hn⟩ := trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos hζ (not_lt.mp hρre)
    refine Finset.mem_image.mpr ⟨n + 1, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      refine ⟨Nat.le_add_left 1 n, ?_⟩
      have hnorm2 : (2 : ℝ) * ((n : ℝ) + 1) ≤ R := by
        have h1 : |ρ.re| ≤ ‖ρ‖ := Complex.abs_re_le_norm ρ
        have h2 : ρ.re = -(2 * ((n : ℝ) + 1)) := by rw [hn]; simp
        rw [h2, abs_neg, abs_of_nonneg (by positivity)] at h1
        linarith
      have h1 : ((n : ℝ) + 1) ≤ R / 2 := by linarith
      have h2 : ((n + 1 : ℕ) : ℝ) ≤ (Nat.ceil (R / 2) : ℝ) := by
        push_cast
        exact le_trans h1 (Nat.le_ceil (R / 2))
      exact Nat.cast_le.mp h2
    · rw [hn]
      push_cast
      ring
  calc (((zetaZeroBallFin R hR).filter (fun ρ => ¬ 0 < ρ.re)).card : ℝ)
      ≤ ((((Finset.Icc 1 (Nat.ceil (R / 2))).image (fun m : ℕ => -((2 : ℂ) * (m : ℂ))))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((Finset.Icc 1 (Nat.ceil (R / 2))).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
    _ = (Nat.ceil (R / 2) : ℝ) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ R := by
        have h1 : (Nat.ceil (R / 2) : ℝ) < R / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
        linarith

/-- Monotonicity of the ball-sum in the radius. -/
lemma zeta1_ball_sum_mono {R R' : ℝ} (hR : 0 ≤ R) (hR' : 0 ≤ R') (h : R ≤ R') :
    (∑ ρ ∈ zetaZeroBallFin R hR, (zeta1Order ρ : ℝ)) ≤
      (∑ ρ ∈ zetaZeroBallFin R' hR', (zeta1Order ρ : ℝ)) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    rw [zetaZeroBallFin_spec] at hρ ⊢
    exact ⟨by
      rw [Metric.mem_closedBall, dist_zero_right] at hρ ⊢
      linarith, hρ.2⟩
  · intro ρ _ _; exact Nat.cast_nonneg _

/-- The radius function `R ↦ R(log(R+2)+2)` is monotone on `[0,∞)`. -/
lemma mul_log_mono {R R' : ℝ} (hR : 0 ≤ R) (h : R ≤ R') :
    R * (Real.log (R + 2) + 2) ≤ R' * (Real.log (R' + 2) + 2) := by
  have hR' : 0 ≤ R' := le_trans hR h
  have hlog : Real.log (R + 2) ≤ Real.log (R' + 2) := Real.log_le_log (by linarith) (by linarith)
  have hA : 0 ≤ Real.log (R + 2) + 2 := by
    have : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    linarith
  have hB : 0 ≤ Real.log (R' + 2) + 2 := by
    have : 0 ≤ Real.log (R' + 2) := Real.log_nonneg (by linarith)
    linarith
  calc R * (Real.log (R + 2) + 2) ≤ R * (Real.log (R' + 2) + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hR
    _ ≤ R' * (Real.log (R' + 2) + 2) := mul_le_mul_of_nonneg_right h hB

theorem zeta1_zeroBall_multiplicity_sum_le :
    ∃ c : ℝ, ∀ R : ℝ, (hR : 0 ≤ R) →
      (∑ ρ ∈ Commons.NumberTheory.Zeta.zetaZeroBallFin R hR,
          (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ))
        ≤ c * R * (Real.log (R + 2) + 2) := by
  classical
  -- the constant of `xiE_zeroCount`
  obtain ⟨cxi, hcxi⟩ := xiE_zeroCount
  -- a zero-free ball around the origin
  obtain ⟨δ, hδpos, hδne⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℂ, ‖ρ‖ < δ → riemannZeta₁ ρ ≠ 0 := by
    have hcont : Continuous riemannZeta₁ := differentiable_riemannZeta₁.continuous
    have h0 : riemannZeta₁ (0 : ℂ) ≠ 0 := by rw [riemannZeta₁_zero]; norm_num
    have hnhd : {z : ℂ | riemannZeta₁ z ≠ 0} ∈ 𝓝 (0 : ℂ) :=
      hcont.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds h0)
    obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp hnhd
    exact ⟨δ, hδpos, fun ρ hρ => hδball (by
      simpa [Metric.mem_ball, dist_zero_right] using hρ)⟩
  -- the estimate at `R = 2`
  have hB2raw : (∑ ρ ∈ zetaZeroBallFin 2 (by norm_num), (zeta1Order ρ : ℝ))
      ≤ (cxi + 1) * (2 * (Real.log (2 + 2) + 2)) := by
    have hdec : (∑ ρ ∈ zetaZeroBallFin 2 (by norm_num), (zeta1Order ρ : ℝ))
        = (∑ ρ ∈ (zetaZeroBallFin 2 (by norm_num)).filter (fun ρ => 0 < ρ.re),
            (zeta1Order ρ : ℝ))
          + (∑ ρ ∈ (zetaZeroBallFin 2 (by norm_num)).filter (fun ρ => ¬ 0 < ρ.re),
              (zeta1Order ρ : ℝ)) :=
      (Finset.sum_filter_add_sum_filter_not (zetaZeroBallFin 2 (by norm_num))
        (fun ρ : ℂ => 0 < ρ.re) (fun ρ => (zeta1Order ρ : ℝ))).symm
    rw [hdec]
    have hnt := zeta1_nontrivial_sum_le (cxi := cxi) (R := 2) (by norm_num) (by norm_num) hcxi
    have htr := zeta1_trivial_sum_le 2 (by norm_num) (by norm_num)
    have hE : (2 : ℝ) ≤ 2 * (Real.log (2 + 2) + 2) := by
      have : 0 ≤ Real.log (2 + 2) := Real.log_nonneg (by norm_num)
      linarith
    nlinarith [hnt, htr, hE]
  -- the final constant
  let B2 : ℝ := max 0 ((cxi + 1) * (2 * (Real.log (2 + 2) + 2)))
  let c : ℝ := max (cxi + 1) (B2 / (δ * (Real.log (δ + 2) + 2)))
  have hδEpos : 0 < δ * (Real.log (δ + 2) + 2) := by
    have : 0 < Real.log (δ + 2) + 2 := by
      have : 0 ≤ Real.log (δ + 2) := Real.log_nonneg (by linarith)
      linarith
    positivity
  have hB2le : (∑ ρ ∈ zetaZeroBallFin 2 (by norm_num), (zeta1Order ρ : ℝ)) ≤ B2 :=
    le_trans hB2raw (le_max_right _ _)
  have hB2nn : 0 ≤ B2 := le_max_left _ _
  have hc_ge : B2 / (δ * (Real.log (δ + 2) + 2)) ≤ c := le_max_right _ _
  have hc_nn : 0 ≤ c := le_trans (div_nonneg hB2nn (le_of_lt hδEpos)) hc_ge
  refine ⟨c, ?_⟩
  intro R hR
  by_cases hR2 : 2 ≤ R
  · -- large radius: nontrivial + trivial parts
    have hdec : (∑ ρ ∈ zetaZeroBallFin R hR, (zeta1Order ρ : ℝ))
        = (∑ ρ ∈ (zetaZeroBallFin R hR).filter (fun ρ => 0 < ρ.re), (zeta1Order ρ : ℝ))
          + (∑ ρ ∈ (zetaZeroBallFin R hR).filter (fun ρ => ¬ 0 < ρ.re),
              (zeta1Order ρ : ℝ)) :=
      (Finset.sum_filter_add_sum_filter_not (zetaZeroBallFin R hR)
        (fun ρ : ℂ => 0 < ρ.re) (fun ρ => (zeta1Order ρ : ℝ))).symm
    rw [hdec]
    have hnt := zeta1_nontrivial_sum_le (cxi := cxi) (R := R) hR hR2 hcxi
    have htr := zeta1_trivial_sum_le R hR hR2
    have hE : R ≤ R * (Real.log (R + 2) + 2) := by
      have : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
      nlinarith [hR]
    have hc1 : cxi + 1 ≤ c := le_max_left _ _
    have hRt : 0 ≤ R * (Real.log (R + 2) + 2) :=
      mul_nonneg hR (by have := Real.log_nonneg (by linarith : (1:ℝ) ≤ R + 2); linarith)
    have hfin : cxi * R * (Real.log (R + 2) + 2) + R
        ≤ c * R * (Real.log (R + 2) + 2) := by
      have h2 := mul_le_mul_of_nonneg_right hc1 hRt
      nlinarith [h2, hE]
    linarith
  · push_neg at hR2
    by_cases hRδ : R < δ
    · -- radius below the zero-free ball: the ball has no zeros
      have hzero : (∑ ρ ∈ zetaZeroBallFin R hR, (zeta1Order ρ : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro ρ hρ
        obtain ⟨hball, hz1⟩ := (zetaZeroBallFin_spec R hR ρ).mp hρ
        have hnorm : ‖ρ‖ < δ := by
          rw [Metric.mem_closedBall, dist_zero_right] at hball
          linarith
        rw [zeta1Order, dif_neg (hδne ρ hnorm)]
        norm_num
      rw [hzero]
      have h3 : 0 ≤ Real.log (R + 2) + 2 := by
        have : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
        linarith
      exact mul_nonneg (mul_nonneg hc_nn hR) h3
    · push_neg at hRδ
      -- `δ ≤ R < 2`
      have hmono : (∑ ρ ∈ zetaZeroBallFin R hR, (zeta1Order ρ : ℝ))
          ≤ (∑ ρ ∈ zetaZeroBallFin 2 (by norm_num), (zeta1Order ρ : ℝ)) :=
        zeta1_ball_sum_mono hR (by norm_num) (le_of_lt hR2)
      have hER : δ * (Real.log (δ + 2) + 2) ≤ R * (Real.log (R + 2) + 2) :=
        mul_log_mono (le_of_lt hδpos) hRδ
      have hERnn : 0 ≤ R * (Real.log (R + 2) + 2) :=
        mul_nonneg hR (by have := Real.log_nonneg (by linarith : (1:ℝ) ≤ R + 2); linarith)
      calc (∑ ρ ∈ zetaZeroBallFin R hR, (zeta1Order ρ : ℝ))
          ≤ B2 := le_trans hmono hB2le
        _ = (B2 / (δ * (Real.log (δ + 2) + 2))) * (δ * (Real.log (δ + 2) + 2)) :=
              (div_mul_cancel₀ B2 (ne_of_gt hδEpos)).symm
        _ ≤ c * (δ * (Real.log (δ + 2) + 2)) :=
              mul_le_mul_of_nonneg_right hc_ge (le_of_lt hδEpos)
        _ ≤ c * (R * (Real.log (R + 2) + 2)) :=
              mul_le_mul_of_nonneg_left hER hc_nn
        _ = c * R * (Real.log (R + 2) + 2) := by ring

end

end Commons.NumberTheory.Zeta
