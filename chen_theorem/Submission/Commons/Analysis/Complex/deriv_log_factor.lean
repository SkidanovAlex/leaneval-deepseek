import Mathlib
import Submission.Commons.Analysis.Complex.zeroFactor_g

noncomputable section

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Topology BigOperators

namespace Commons.Analysis.Complex

/-- The `logDeriv`-identity behind `deriv_log_factor`, with the closed ball written as
`Metric.closedBall a R` (no absolute value on `R`). -/
private theorem deriv_log_factor_R {a : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hfac : ∀ z ∈ Metric.closedBall a R,
        f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall a R)) u : ℤ)) * g z)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a R))
    (hg : DifferentiableAt ℂ g a) (hg0 : g a ≠ 0)
    (hfa : f a ≠ 0)
    (_hsphere : ∀ u, ‖u - a‖ = R → f u ≠ 0) :
    (deriv f a / f a).re =
      (deriv g a / g a).re +
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall a R)) u : ℤ) : ℝ) *
          (1 / (a - u)).re := by
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall a R) u
  let P : ℂ → ℂ := fun z => ∏ᶠ u : ℂ, (z - u) ^ (d u)
  have haB : a ∈ Metric.closedBall a R := Metric.mem_closedBall_self (le_of_lt hR)
  have hfac_d : ∀ z ∈ Metric.closedBall a R,
      f z = (∏ᶠ u : ℂ, (z - u) ^ (d u)) * g z := by
    intro z hz
    dsimp [d]
    exact hfac z hz
  have hsupp : (support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset hf.meromorphicOn
      (isCompact_closedBall a R) (by simp)
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf) u
  have hda : d a = 0 := by
    dsimp [d]
    rw [MeromorphicOn.divisor_apply hf.meromorphicOn haB]
    have hord : meromorphicOrderAt f a = 0 :=
      meromorphicOrderAt_eq_zero_of_ne_zero (hf a haB) hfa
    simp [hord]
  let S : Finset ℂ := hsupp.toFinset
  have hS_coe : (S : Set ℂ) = support d := by
    exact hsupp.coe_toFinset
  have hP_eq : ∀ z : ℂ, P z = ∏ u ∈ S, (z - u) ^ (d u) := by
    intro z
    dsimp [P]
    have hsub : mulSupport (fun u : ℂ => (z - u) ^ (d u)) ⊆ (S : Set ℂ) := by
      intro u hu
      have hd_ne : d u ≠ 0 := by
        intro hd0
        have : (z - u) ^ (d u) = 1 := by simp [hd0]
        exact hu this
      rw [hS_coe]
      exact hd_ne
    rw [finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (z - u) ^ (d u)) hsub]
  have hP_fun : P = (fun z : ℂ => ∏ u ∈ S, (z - u) ^ (d u)) := funext hP_eq
  have hfac0 : ∀ u ∈ S, (a - u) ^ (d u) ≠ 0 := by
    intro u hu
    have hd_ne : d u ≠ 0 := by
      have huS : u ∈ (S : Set ℂ) := by simpa using hu
      rw [hS_coe] at huS
      exact huS
    have ha_ne : a ≠ u := by
      intro h
      have : d a = d u := by rw [h]
      exact hd_ne (by simpa [hda] using this.symm)
    exact zpow_ne_zero (d u) (sub_ne_zero.mpr ha_ne)
  have hdiff : ∀ u ∈ S, DifferentiableAt ℂ (fun z : ℂ => (z - u) ^ (d u)) a := by
    intro u hu
    have hdf : DifferentiableAt ℂ (fun z : ℂ => z - u) a := by fun_prop
    exact hdf.zpow (Or.inr (hd_nonneg u))
  have hdiffP : DifferentiableAt ℂ P a := by
    rw [hP_fun]
    simpa using (DifferentiableAt.fun_finsetProd (u := S) (f := fun u z => (z - u) ^ (d u))
      (x := a) hdiff)
  have hP0 : P a ≠ 0 := by
    intro hP0
    have hfac_a : f a = P a * g a := by
      simpa [P] using (hfac_d a haB)
    have hprod0 : (∏ᶠ u : ℂ, (a - u) ^ (d u)) = 0 := by
      simpa [P] using hP0
    have hf0 : f a = 0 := by
      rw [hfac_a]
      have hPafin : P a = ∏ᶠ u : ℂ, (a - u) ^ (d u) := by rfl
      rw [hPafin, hprod0]
      simp
    exact hfa hf0
  have hPg_eq_f : (fun z : ℂ => P z * g z) =ᶠ[𝓝 a] f := by
    filter_upwards [Metric.ball_mem_nhds a hR] with z hz
    have hzB : z ∈ Metric.closedBall a R := Metric.ball_subset_closedBall hz
    simpa [P] using (hfac_d z hzB).symm
  have hL2 : logDeriv f a = logDeriv (fun z : ℂ => P z * g z) a := by
    have hdv : deriv (fun z : ℂ => P z * g z) a = deriv f a := hPg_eq_f.deriv_eq
    have hfa_eq : f a = P a * g a := by
      simpa [P] using (hfac_d a haB)
    rw [logDeriv_apply, logDeriv_apply]
    rw [← hdv]
    rw [hfa_eq]
  have hlogP : logDeriv P a = ∑ u ∈ S, (d u : ℂ) * (1 / (a - u)) := by
    calc
      logDeriv P a = logDeriv (fun z : ℂ => ∏ u ∈ S, (z - u) ^ (d u)) a := by
          rw [hP_fun]
      _ = ∑ u ∈ S, logDeriv (fun z : ℂ => (z - u) ^ (d u)) a := by
          simpa only [Finset.prod_fn] using
            logDeriv_prod (f := fun (u : ℂ) (z : ℂ) => (z - u) ^ (d u)) hfac0 hdiff
      _ = ∑ u ∈ S, (d u : ℂ) * (1 / (a - u)) := by
          apply Finset.sum_congr rfl
          intro u hu
          calc
            logDeriv (fun z : ℂ => (z - u) ^ (d u)) a
                = (d u : ℂ) * logDeriv (fun z : ℂ => z - u) a := by
                    exact logDeriv_fun_zpow (by fun_prop) (d u)
            _ = (d u : ℂ) * (1 / (a - u)) := by
                    congr 1
                    rw [logDeriv_apply]
                    rw [deriv_sub_const u]
                    simp
  have hL3 : logDeriv (fun z : ℂ => P z * g z) a = logDeriv P a + logDeriv g a := by
    exact logDeriv_mul a hP0 hg0 hdiffP hg
  have hmain : (deriv f a / f a).re = (deriv g a / g a).re + (logDeriv P a).re := by
    calc
      (deriv f a / f a).re = (logDeriv f a).re := by rw [← logDeriv_apply f a]
      _ = (logDeriv (fun z : ℂ => P z * g z) a).re := by rw [hL2]
      _ = (logDeriv P a).re + (logDeriv g a).re := by
            rw [hL3, Complex.add_re]
      _ = (deriv g a / g a).re + (logDeriv P a).re := by
            rw [← logDeriv_apply g a]
            ring
  have hreP : (logDeriv P a).re = ∑ u ∈ S, ((d u : ℤ) : ℝ) * (1 / (a - u)).re := by
    rw [hlogP]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [← Complex.ofReal_intCast (d u)]
    exact Complex.re_ofReal_mul (d u : ℝ) (1 / (a - u))
  have hfin_sum : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) * (1 / (a - u)).re) =
      ∑ u ∈ S, ((d u : ℤ) : ℝ) * (1 / (a - u)).re := by
    rw [finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℝ) * (1 / (a - u)).re)
      (s := S) ?_]
    · intro u hu
      have hd_ne : d u ≠ 0 := by
        intro hd0
        have : ((d u : ℤ) : ℝ) * (1 / (a - u)).re = 0 := by simp [hd0]
        exact hu this
      rw [hS_coe]
      exact hd_ne
  rw [hfin_sum]
  rw [hmain]
  rw [hreP]

/--
The real part of the logarithmic derivative of `f` at the center of the disk equals the real part
of the logarithmic derivative of `g` (the zero-free factor in the canonical factorization) plus the
weighted sum of the real parts `(1 / (a - u)).re` over the divisor points `u` of `f`.
-/
theorem deriv_log_factor {a : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hfac : ∀ z ∈ Metric.closedBall a R,
        f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ)) * g z)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a |R|))
    (hg : DifferentiableAt ℂ g a) (hg0 : g a ≠ 0)
    (hfa : f a ≠ 0)
    (hsphere : ∀ u, ‖u - a‖ = R → f u ≠ 0) :
    (deriv f a / f a).re =
      (deriv g a / g a).re +
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) *
          (1 / (a - u)).re := by
  have hB : Metric.closedBall a |R| = Metric.closedBall a R := by
    rw [abs_of_pos hR]
  rw [hB]
  rw [hB] at hfac
  rw [hB] at hf
  exact deriv_log_factor_R hR hfac hf hg hg0 hfa hsphere

end Commons.Analysis.Complex
