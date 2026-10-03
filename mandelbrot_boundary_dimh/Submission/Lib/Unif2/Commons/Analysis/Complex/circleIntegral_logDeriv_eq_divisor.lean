import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.zeroFactor_g
import Submission.Lib.Unif2.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Lib.Unif2.Commons.Analysis.Complex.logDeriv_eq_finsum_of_factorization
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleIntegral_finset_sum_sub_inv
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleIntegral_logDeriv_eq_zero_of_analyticOnNhd_ball

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Real Topology BigOperators

namespace Commons.Analysis.Complex



theorem circleIntegral_logDeriv_eq_divisor {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball (0:ℂ) R))
    (hne : ∀ z ∈ Metric.sphere (0:ℂ) ρ, f z ≠ 0) :
    circleIntegral (fun z => logDeriv f z) 0 ρ =
      (2 * Real.pi * Complex.I) *
        ((∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ)) u : ℤ)) : ℂ) := by
  classical
  set R' : ℝ := (ρ + R) / 2 with hR'def
  have hρR' : ρ < R' := by rw [hR'def]; linarith
  have hR'R : R' < R := by rw [hR'def]; linarith
  have hR'pos : 0 < R' := lt_trans hρ hρR'
  have hfR' : AnalyticOnNhd ℂ f (Metric.ball (0:ℂ) R') :=
    hf.mono (Metric.ball_subset_ball hR'R.le)
  -- basic norm facts
  have hρ_norm : ‖((ρ : ℝ) : ℂ)‖ = ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hρsph : ((ρ : ℝ) : ℂ) ∈ Metric.sphere (0:ℂ) ρ := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hρ_norm
  have hρmem' : ((ρ : ℝ) : ℂ) ∈ Metric.ball (0:ℂ) R' := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact lt_of_eq_of_lt hρ_norm hρR'
  -- finite order on ball 0 R'
  have horder : ∀ z ∈ Metric.ball (0:ℂ) R', meromorphicOrderAt f z ≠ ⊤ := by
    have hconn : IsConnected (Metric.ball (0:ℂ) R') := isConnected_ball hR'pos
    refine (MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall_mem
      hfR'.meromorphicOn hconn).mp ?_
    exact ⟨(ρ : ℂ), hρmem', meromorphicOrderAt_ne_top_of_analytic_ne_zero
      (hfR' _ hρmem') (hne _ hρsph)⟩
  -- finite support of the divisor on ball 0 R'
  have hsupp : (MeromorphicOn.divisor f (Metric.ball (0:ℂ) R')).support.Finite := by
    have hmer : MeromorphicOn f (Metric.closedBall (0:ℂ) R') :=
      (hf.mono (Metric.closedBall_subset_ball hR'R)).meromorphicOn
    exact MeromorphicOn.divisor_support_finite_of_subset (U := Metric.closedBall (0:ℂ) R')
      (V := Metric.ball (0:ℂ) R') hmer (isCompact_closedBall _ _) Metric.ball_subset_closedBall
  -- factorisation
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ :=
    factor_pointwise (U := Metric.ball (0:ℂ) R') hfR'.meromorphicOn horder hsupp hfR'
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.ball (0:ℂ) R') u
  have hd : d.HasFiniteSupport := by
    simpa [d, Function.HasFiniteSupport] using hsupp
  let S : Finset ℂ := hsupp.toFinset
  have hS_coe : (S : Set ℂ) = Function.support d := by
    simpa [S, d, Function.HasFiniteSupport] using hsupp.coe_toFinset
  -- u in S has ‖u‖ ≠ ρ
  have hSne : ∀ u ∈ S, ‖u‖ ≠ ρ := by
    intro u hu hnorm
    have hu_supp : u ∈ Function.support d := by rw [← hS_coe]; exact hu
    have hd_ne : d u ≠ 0 := by simpa [Function.mem_support] using hu_supp
    have hu_ball : u ∈ Metric.ball (0:ℂ) R' := by
      by_contra hnot
      have hcond : ¬ (MeromorphicOn f (Metric.ball (0:ℂ) R') ∧ u ∈ Metric.ball (0:ℂ) R') :=
        fun hh => hnot hh.2
      exact hd_ne (by
        change MeromorphicOn.divisor f (Metric.ball (0:ℂ) R') u = 0
        rw [MeromorphicOn.divisor_def, if_neg hcond])
    have hdu : d u = (meromorphicOrderAt f u).untop₀ := by
      simpa [d] using MeromorphicOn.divisor_apply hfR'.meromorphicOn hu_ball
    have hun : (meromorphicOrderAt f u).untop₀ ≠ 0 := fun h => hd_ne (hdu.trans h)
    have hord_ne : meromorphicOrderAt f u ≠ 0 := by
      intro h0; exact hun (by simp [h0])
    have hfu : f u = 0 := by
      by_contra hfne
      exact hord_ne (meromorphicOrderAt_eq_zero_of_ne_zero (hfR' u hu_ball) hfne)
    have husph : u ∈ Metric.sphere (0:ℂ) ρ := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hnorm
    exact hne u husph hfu
  -- decomposition of logDeriv f on the sphere
  have hdec : ∀ z ∈ Metric.sphere (0:ℂ) ρ,
      logDeriv f z = (∑ᶠ u : ℂ, (d u : ℂ) * (1 / (z - u))) + logDeriv g z := by
    intro z hz
    have hzR' : z ∈ Metric.ball (0:ℂ) R' := by
      have hzn : ‖z‖ = ρ := by
        have := Metric.mem_sphere.mp hz; rwa [dist_eq_norm, sub_zero] at this
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact lt_of_eq_of_lt hzn hρR'
    exact logDeriv_eq_finsum_of_factorization Metric.isOpen_ball hd hfR' hg_an hg_ne
      (fun w hw => by simpa [d] using hg_eq w hw) hzR' (hne z hz)
  -- the auxiliary function L (finite sum)
  let L : ℂ → ℂ := fun z => ∑ u ∈ S, (d u : ℂ) * (1 / (z - u))
  have hLfinsum : ∀ z : ℂ, (∑ᶠ u : ℂ, (d u : ℂ) * (1 / (z - u))) = L z := by
    intro z
    dsimp [L]
    rw [finsum_eq_sum_of_support_subset
      (f := fun u : ℂ => (d u : ℂ) * (1 / (z - u))) (s := S) ?_]
    intro u hu
    rw [Function.mem_support] at hu
    have hd_ne : d u ≠ 0 := by intro h0; exact hu (by simp [h0])
    rw [hS_coe, Function.mem_support]; exact hd_ne
  -- circle-integrability
  have hL_int : CircleIntegrable L 0 ρ := by
    apply ContinuousOn.circleIntegrable hρ.le
    dsimp [L]
    refine continuousOn_finsetSum S (fun u hu => ?_)
    have hu_ne : ∀ z ∈ Metric.sphere (0:ℂ) ρ, z - u ≠ 0 := by
      intro z hz hzu
      have hzn : ‖z‖ = ρ := by
        have := Metric.mem_sphere.mp hz; rwa [dist_eq_norm, sub_zero] at this
      have hzu' : z = u := sub_eq_zero.mp hzu
      exact hSne u hu (by rw [← hzu']; exact hzn)
    have h1 : ContinuousOn (fun z : ℂ => 1 / (z - u)) (Metric.sphere (0:ℂ) ρ) :=
      ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
        (fun z hz => hu_ne z hz)
    exact continuousOn_const.mul h1
  have hsub : Metric.sphere (0:ℂ) ρ ⊆ Metric.ball (0:ℂ) R' := by
    intro z hz
    have hzn : ‖z‖ = ρ := by
      have := Metric.mem_sphere.mp hz; rwa [dist_eq_norm, sub_zero] at this
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact lt_of_eq_of_lt hzn hρR'
  have hg_int : CircleIntegrable (fun z => logDeriv g z) 0 ρ := by
    have hcd : ContinuousOn (deriv g) (Metric.sphere (0:ℂ) ρ) :=
      (hg_an.deriv.continuousOn).mono hsub
    have hcg : ContinuousOn g (Metric.sphere (0:ℂ) ρ) := hg_an.continuousOn.mono hsub
    have hgne' : ∀ z ∈ Metric.sphere (0:ℂ) ρ, g z ≠ 0 := fun z hz => hg_ne z (hsub hz)
    rw [show (fun z => logDeriv g z) = deriv g / g from by
      ext z; rw [logDeriv_apply, Pi.div_apply]]
    exact (hcd.div hcg hgne').circleIntegrable hρ.le
  -- Step 1: rewrite on the sphere
  have hstep1 : circleIntegral (fun z => logDeriv f z) 0 ρ
      = circleIntegral (fun z => L z + logDeriv g z) 0 ρ := by
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    rw [hdec z hz, hLfinsum z]
  have hstep2 : circleIntegral (fun z => L z + logDeriv g z) 0 ρ
      = circleIntegral L 0 ρ + circleIntegral (fun z => logDeriv g z) 0 ρ :=
    circleIntegral.integral_add hL_int hg_int
  have hstep3 : circleIntegral (fun z => logDeriv g z) 0 ρ = 0 :=
    circleIntegral_logDeriv_eq_zero_of_analyticOnNhd_ball hρ hρR' hg_an hg_ne
  have hLi : circleIntegral L 0 ρ
      = (2 * Real.pi * Complex.I) * (∑ u ∈ S, if ‖u‖ < ρ then (d u : ℂ) else 0) := by
    have h := circleIntegral_finset_sum_sub_inv (ρ := ρ) hρ (S := S)
      (c := fun u => (d u : ℂ)) hSne
    simpa [L] using h
  -- relate the finite sums
  have he_eq : (fun u : ℂ => (if ‖u‖ < ρ then d u else 0 : ℤ))
      = MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ) := by
    funext u
    by_cases h : ‖u‖ < ρ
    · have humem : u ∈ Metric.ball (0:ℂ) ρ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact h
      have humem' : u ∈ Metric.ball (0:ℂ) R' := Metric.ball_subset_ball hρR'.le humem
      have hd1 : d u = (meromorphicOrderAt f u).untop₀ :=
        MeromorphicOn.divisor_apply hfR'.meromorphicOn humem'
      have hd2 : MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ) u
          = (meromorphicOrderAt f u).untop₀ :=
        MeromorphicOn.divisor_apply
          (hfR'.meromorphicOn.mono_set (Metric.ball_subset_ball hρR'.le)) humem
      rw [if_pos h, hd1, hd2]
    · have humem : u ∉ Metric.ball (0:ℂ) ρ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact not_lt.mpr (le_of_not_gt h)
      have hcond : ¬ (MeromorphicOn f (Metric.ball (0:ℂ) ρ) ∧ u ∈ Metric.ball (0:ℂ) ρ) :=
        fun hh => humem hh.2
      rw [if_neg h, MeromorphicOn.divisor_def, if_neg hcond]
  have ha_supp : (Function.support (fun u : ℂ =>
      MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ) u)).Finite := by
    have hmer : MeromorphicOn f (Metric.closedBall (0:ℂ) ρ) :=
      (hf.mono (Metric.closedBall_subset_ball hρR)).meromorphicOn
    exact MeromorphicOn.divisor_support_finite_of_subset (U := Metric.closedBall (0:ℂ) ρ)
      (V := Metric.ball (0:ℂ) ρ) hmer (isCompact_closedBall _ _) Metric.ball_subset_closedBall
  have hbSsum : (∑ u ∈ S, if ‖u‖ < ρ then (d u : ℂ) else 0)
      = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ)) u) : ℂ) := by
    have h1 : (∑ u ∈ S, if ‖u‖ < ρ then (d u : ℂ) else 0)
        = ∑ u ∈ S, (((if ‖u‖ < ρ then d u else 0 : ℤ)) : ℂ) := by
      apply Finset.sum_congr rfl
      intro u hu
      by_cases h : ‖u‖ < ρ <;> simp [h]
    rw [h1]
    have h2 : (∑ u ∈ S, (((if ‖u‖ < ρ then d u else 0 : ℤ)) : ℂ))
        = ∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ) u : ℤ) : ℂ) := by
      rw [finsum_eq_sum_of_support_subset
        (f := fun u : ℂ => ((MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ) u : ℤ) : ℂ))
        (s := S) ?_]
      · apply Finset.sum_congr rfl
        intro u hu
        rw [← congrFun he_eq u]
      · intro u hu
        rw [Function.mem_support] at hu
        have hne' : MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ) u ≠ 0 := by
          intro h0; exact hu (by simp [h0])
        have hdu : d u ≠ 0 := by
          have hcong := congrFun he_eq u
          by_cases h : ‖u‖ < ρ
          · rw [if_pos h] at hcong; rw [hcong]; exact hne'
          · rw [if_neg h] at hcong; exact absurd hcong.symm hne'
        rw [hS_coe, Function.mem_support]; exact hdu
    rw [h2]
  have hLi' : circleIntegral L 0 ρ
      = (2 * Real.pi * Complex.I) *
        ((∑ᶠ u : ℂ, (MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ)) u) : ℂ) := by
    rw [hLi, hbSsum]
  simpa only [hstep1, hstep2, hstep3, hLi', add_zero]

end Commons.Analysis.Complex
