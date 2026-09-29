import Mathlib
import Submission.Commons.Analysis.Complex.divisor_subBall_factor
import Submission.Work.Analysis.Complex.circleIntegral_logDeriv_finprod

open Complex Metric MeromorphicOn Filter Function Set Topology
open scoped Topology BigOperators

namespace Work.ANum3

noncomputable section

variable {R ρ : ℝ} {f g : ℂ → ℂ}

/-!
# The argument principle, local proof

`∮_{|z|=ρ} logDeriv f = 2πi · ∑ᶠ_u (divisor of `f` on `closedBall 0 ρ` at `u`)` for `f` analytic on
`ball 0 R`, zero-free on the sphere of radius `ρ < R`.  Assembled here from:
* `Work.Analysis.Complex.circleIntegral_logDeriv_finprod` (residue form for a finite product),
* `Commons.Analysis.Complex.factor_subBall_divisor` (factorisation against the divisor),
* Cauchy–Goursat on the disc (`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`).
-/

/-- **(L2)** The circle integral of `logDeriv` of a zero-free analytic function vanishes. -/
lemma logDeriv_integral_eq_zero_of_zeroFree (hρ : 0 < ρ) (hρR : ρ < R)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R))
    (hgne : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, g z ≠ 0) :
    circleIntegral (fun z => logDeriv g z) 0 ρ = 0 := by
  have hdiffAt : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ,
      DifferentiableAt ℂ (fun z => deriv g z / g z) z := by
    intro z hz
    have hzR : z ∈ Metric.ball (0 : ℂ) R := Metric.closedBall_subset_ball hρR hz
    exact ((hg z hzR).deriv.differentiableAt).div (hg z hzR).differentiableAt (hgne z hz)
  have hEqOn : Set.EqOn (fun z : ℂ => logDeriv g z) (fun z => deriv g z / g z)
      (Metric.sphere (0 : ℂ) ρ) := fun z _ => logDeriv_apply g z
  rw [circleIntegral.integral_congr hρ.le hEqOn]
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le (s := (∅ : Set ℂ))
    (by simp) (fun z hz => (hdiffAt z hz).continuousAt.continuousWithinAt)
    (fun z hz => hdiffAt z (Metric.ball_subset_closedBall hz.1))

/-- **(L4)** Factorization of `f` against its divisor on `closedBall 0 ρ`: there is `g`, analytic
on `ball 0 R` and zero-free on `closedBall 0 ρ`, with
`f = (∏ᶠ u, (· - u) ^ (divisor f (closedBall 0 ρ) u)) * g` on `ball 0 R`. -/
lemma exists_factorization_closedBall (hρ : 0 < ρ) (hρR : ρ < R)
    (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) R))
    (hne : ∀ z : ℂ, ‖z‖ = ρ → f z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R) ∧
      (∀ u ∈ Metric.closedBall (0 : ℂ) ρ, g u ≠ 0) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R,
        f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) ρ)) u : ℤ)) * g z := by
  have hVU : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) R :=
    Metric.closedBall_subset_ball hρR
  have h₂f : ∀ z ∈ Metric.ball (0 : ℂ) R, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz
    have hρmem : (ρ : ℂ) ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : ‖(ρ : ℂ) - 0‖ = ρ := by simp [abs_of_pos hρ]
      rw [h1]; exact hρR
    have hρnz : f (ρ : ℂ) ≠ 0 := by
      apply hne
      simp [abs_of_pos hρ]
    have hordρ : analyticOrderAt f (ρ : ℂ) ≠ ⊤ := by
      have h0 : analyticOrderAt f (ρ : ℂ) = 0 :=
        ((hf (ρ : ℂ) hρmem).analyticOrderAt_eq_zero).mpr hρnz
      rw [h0]; exact ENat.zero_ne_top
    have hz_top : analyticOrderAt f z ≠ ⊤ :=
      AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hf Metric.isPreconnected_ball
        hρmem hz hordρ
    rw [(hf z hz).meromorphicOrderAt_eq]
    intro htop
    exact hz_top (ENat.map_eq_top_iff.mp htop)
  have h₃f : (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) ρ)).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset (f := f)
      (U := Metric.closedBall (0 : ℂ) ρ) (V := Metric.closedBall (0 : ℂ) ρ)
      (hf.mono hVU).meromorphicOn (isCompact_closedBall (0 : ℂ) ρ) (subset_refl _)
  exact Commons.Analysis.Complex.factor_subBall_divisor hVU hf.meromorphicOn h₂f hf h₃f

/-- **(L5)** `logDeriv` of the factorisation, in terms of the finitary product `P`. -/
lemma logDeriv_factorization (hρ : 0 < ρ) (hρR : ρ < R)
    (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) R))
    (hfac : ∀ z ∈ Metric.ball (0 : ℂ) R,
      f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) ρ)) u : ℤ)) * g z)
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R))
    {x : ℂ} (hx : x ∈ Metric.ball (0 : ℂ) R) (hfx : f x ≠ 0) (hgx : g x ≠ 0) :
    logDeriv f x =
      logDeriv (fun w : ℂ => ∏ᶠ u : ℂ,
        (w - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) ρ)) u : ℤ)) x + logDeriv g x := by
  set P : ℂ → ℂ := fun w => ∏ᶠ u : ℂ,
    (w - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) ρ)) u : ℤ) with hPdef
  have hfx_eq : f x = P x * g x := by rw [hPdef]; exact hfac x hx
  have hP0 : P x ≠ 0 := by
    intro h; exact hfx (by rw [hfx_eq, h, zero_mul])
  have hPg_eq_f : (fun w : ℂ => P w * g w) =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with w hw
    rw [hPdef]; exact (hfac w hw).symm
  have hL2 : logDeriv f x = logDeriv (fun w : ℂ => P w * g w) x := by
    have hdv : deriv (fun w : ℂ => P w * g w) x = deriv f x := hPg_eq_f.deriv_eq
    rw [logDeriv_apply, logDeriv_apply, ← hdv, hfx_eq]
  have hPdiv : (fun w : ℂ => f w / g w) =ᶠ[𝓝 x] P := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx,
      (hg x hx).continuousAt.eventually_ne hgx] with w hw hgw
    have h1 : f w = P w * g w := by rw [hPdef]; exact hfac w hw
    rw [h1]
    exact mul_div_cancel_right₀ _ hgw
  have hdiffP : DifferentiableAt ℂ P x :=
    (((hf x hx).differentiableAt.div (hg x hx).differentiableAt hgx).congr_of_eventuallyEq hPdiv.symm)
  have hL3 : logDeriv (fun w : ℂ => P w * g w) x = logDeriv P x + logDeriv g x :=
    logDeriv_mul x hP0 hgx hdiffP (hg x hx).differentiableAt
  rw [hL2, hL3]

/-- The argument principle (fallback proof). -/
theorem argument_principle_fallback (hρ : 0 < ρ) (hρR : ρ < R)
    (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) R))
    (hne : ∀ z : ℂ, ‖z‖ = ρ → f z ≠ 0) :
    circleIntegral (fun z => logDeriv f z) 0 ρ =
      2 * (Real.pi : ℂ) * Complex.I *
        (∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) ρ) u : ℤ) : ℂ)) := by
  classical
  obtain ⟨g, hg_an, hg_nz, hfac⟩ := exists_factorization_closedBall hρ hρR hf hne
  set d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) ρ) u with hddef
  set P : ℂ → ℂ := fun w => ∏ᶠ u : ℂ, (w - u) ^ (d u) with hPdef
  have hρnn : 0 ≤ ρ := hρ.le
  have hsphere_ball : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) ρ → z ∈ Metric.ball (0 : ℂ) R := by
    intro z hz
    have hzρ : ‖z‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hzρ]; exact hρR
  have hsphere_closed : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) ρ → z ∈ Metric.closedBall (0 : ℂ) ρ := by
    intro z hz
    have hzρ : ‖z‖ = ρ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hzρ]
  have hnz_sphere : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) ρ → f z ≠ 0 := by
    intro z hz
    exact hne z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz)
  -- pointwise split
  have hsplit : Set.EqOn (fun z => logDeriv f z) (fun z => logDeriv P z + logDeriv g z)
      (Metric.sphere (0 : ℂ) ρ) := by
    intro z hz
    have hfac' : ∀ w ∈ Metric.ball (0 : ℂ) R,
        f w = (∏ᶠ u : ℂ, (w - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) ρ)) u : ℤ)) * g w := hfac
    have := logDeriv_factorization hρ hρR hf hfac' hg_an (hsphere_ball z hz) (hnz_sphere z hz)
      (hg_nz z (hsphere_closed z hz))
    simpa [hPdef, hddef] using this
  -- analyticity of P near the sphere
  have hPan : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) ρ → AnalyticAt ℂ P z := by
    intro z hz
    have hzR : z ∈ Metric.ball (0 : ℂ) R := hsphere_ball z hz
    have hgz : g z ≠ 0 := hg_nz z (hsphere_closed z hz)
    have hPdiv : P =ᶠ[𝓝 z] (fun w : ℂ => f w / g w) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzR,
        (hg_an z hzR).continuousAt.eventually_ne hgz] with w hw hgw
      have h1 : f w = P w * g w := by rw [hPdef]; rw [hddef]; exact hfac w hw
      rw [h1]
      exact (mul_div_cancel_right₀ _ hgw).symm
    exact (AnalyticAt.div (hf z hzR) (hg_an z hzR) hgz).congr hPdiv.symm
  have hPz_ne : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) ρ → P z ≠ 0 := by
    intro z hz
    have h1 : f z = P z * g z := by
      rw [hPdef]; rw [hddef]; exact hfac z (hsphere_ball z hz)
    intro h; exact hnz_sphere z hz (by rw [h1, h, zero_mul])
  -- integrability of the two summands
  have hciP : CircleIntegrable (fun z => logDeriv P z) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρnn ?_
    intro z hz
    have hzR : z ∈ Metric.ball (0 : ℂ) R := hsphere_ball z hz
    have hz_an : AnalyticAt ℂ P z := hPan z hz
    have hd : DifferentiableAt ℂ (fun w : ℂ => deriv P w / P w) z :=
      (hz_an.deriv).differentiableAt.div hz_an.differentiableAt (hPz_ne z hz)
    have hev : logDeriv P =ᶠ[𝓝 z] (fun w : ℂ => deriv P w / P w) := by
      filter_upwards with w
      exact logDeriv_apply P w
    exact (hd.congr_of_eventuallyEq hev).continuousAt.continuousWithinAt
  have hciG : CircleIntegrable (fun z => logDeriv g z) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρnn ?_
    intro z hz
    have hzR : z ∈ Metric.ball (0 : ℂ) R := hsphere_ball z hz
    have hd : DifferentiableAt ℂ (fun w : ℂ => deriv g w / g w) z :=
      ((hg_an z hzR).deriv.differentiableAt).div (hg_an z hzR).differentiableAt
        (hg_nz z (hsphere_closed z hz))
    have hev : logDeriv g =ᶠ[𝓝 z] (fun w : ℂ => deriv g w / g w) := by
      filter_upwards with w
      exact logDeriv_apply g w
    exact (hd.congr_of_eventuallyEq hev).continuousAt.continuousWithinAt
  -- finiteness and location of the divisor support
  have hd_supp : (Function.support d).Finite := by
    rw [hddef]
    exact MeromorphicOn.divisor_support_finite_of_subset
      (hf.mono (Metric.closedBall_subset_ball hρR)).meromorphicOn
      (isCompact_closedBall (0 : ℂ) ρ) (subset_refl _)
  have hd_sub : Function.support d ⊆ Metric.ball (0 : ℂ) ρ := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have hu' : MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) ρ) u ≠ 0 := hu
    have hfB : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) ρ) :=
      hf.mono (Metric.closedBall_subset_ball hρR)
    have hB : u ∈ Metric.closedBall (0 : ℂ) ρ := by
      by_contra hout
      rw [MeromorphicOn.divisor_def] at hu'
      simp [hout] at hu'
    have hfu : f u = 0 := by
      have h1 := MeromorphicOn.AnalyticOnNhd.divisor_apply hfB hB
      rw [h1] at hu'
      have h2 : analyticOrderAt f u ≠ 0 := by
        intro h0
        exact hu' (by rw [h0]; simp)
      exact apply_eq_zero_of_analyticOrderAt_ne_zero h2
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hB
    exact lt_of_le_of_ne hB (fun h => hne u h hfu)
  rw [circleIntegral.integral_congr hρnn hsplit, circleIntegral.integral_add hciP hciG,
    logDeriv_integral_eq_zero_of_zeroFree hρ hρR hg_an hg_nz, add_zero]
  exact Work.Analysis.Complex.circleIntegral_logDeriv_finprod hρ hd_supp hd_sub

end

end Work.ANum3
