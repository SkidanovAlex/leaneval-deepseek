import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_eq_lim_log_sub_sum_inv
import Submission.Work.LinnikAreas.FarRepel.tendstoLocallyUniformlyOnIterateDeriv
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeriesSummable

open Filter

namespace Work.LinnikAreas.FarRepel

/-!
# Derivatives of the digamma function

We prove the Hurwitz-zeta type series representation of the derivatives of the digamma function
`Complex.digamma = logDeriv Γ`: for `m ≥ 1` and `Re w > 0`,

`∑_{n ≥ 0} (-1)^{m+1} m! (1/(w+n))^{m+1} = ψ^{(m)}(w)`.

The proof follows Gauss' limit formula: the log-derivative of the Euler partial product `Γ_N` is
`log N - ∑_{k ≤ N} (z + k)^{-1}`, the `Γ_N` converge locally uniformly to `Γ` on the right
half-plane, and hence (Weierstrass) so do all their derivatives; the `m`-th derivative of the
Euler partial product can be computed explicitly, and its limit is the stated series.  Absolute
convergence of the series is checked separately (`digammaDerivSeriesSummable`), which upgrades
convergence of the partial sums to `HasSum`.

## Main results

* `iteratedDeriv_inv_add_const`: the `m`-th derivative of `z ↦ (z + c)⁻¹`.
* `iteratedDeriv_logDeriv_GammaSeq`: the `m`-th derivative of the log-derivative of `Γ_N`.
* `digammaDerivSeries`: the series representation of `ψ^{(m)}(w)`.
-/

/-- The `m`-th derivative of `z ↦ (z + c)⁻¹` at `w` is `(-1)^m m! (1/(w+c))^(m+1)`. -/
lemma iteratedDeriv_inv_add_const (m : ℕ) (c w : ℂ) :
    iteratedDeriv m (fun z : ℂ => (z + c)⁻¹) w
      = (-1 : ℂ)^m * (m.factorial : ℂ) * (1 / (w + c))^(m+1) := by
  rw [iteratedDeriv_comp_add_const]
  simp only
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [show (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) by omega]
  rw [zpow_neg, zpow_natCast]
  simp only [one_div, inv_pow]

/-- The `m`-th derivative of the finite sum `z ↦ ∑_{k ≤ N} (z + k)⁻¹`. -/
lemma iteratedDeriv_sum_inv_add_const (m : ℕ) (w : ℂ) (N : ℕ) (hw : 0 < w.re) :
    iteratedDeriv m (fun z : ℂ => ∑ k ∈ Finset.range (N+1), (z + (k:ℂ))⁻¹) w
      = ∑ k ∈ Finset.range (N+1),
          ((-1 : ℂ)^m * (m.factorial : ℂ) * (1/(w + (k:ℂ)))^(m+1)) := by
  rw [show (fun z : ℂ => ∑ k ∈ Finset.range (N+1), (z + (k:ℂ))⁻¹)
      = ∑ k ∈ Finset.range (N+1), (fun z : ℂ => (z + (k:ℂ))⁻¹) from by
        funext z; simp [Finset.sum_apply]]
  rw [iteratedDeriv_sum]
  · exact Finset.sum_congr rfl (fun k hk => iteratedDeriv_inv_add_const m (k:ℂ) w)
  · intro k hk
    exact (contDiffAt_id.add contDiffAt_const).inv (by
      intro h
      have h2 : (w + (k:ℂ)).re = 0 := by simpa using congrArg Complex.re h
      have h3 : 0 < (w + (k:ℂ)).re := by
        rw [Complex.add_re]
        have h4 : 0 ≤ ((k:ℂ).re) := by simp
        linarith
      linarith)

/-- `GammaSeq z n` vanishes only at the poles of the Euler product: for `Re z > 0` and `n ≠ 0`
it is nonzero. -/
lemma GammaSeq_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    Complex.GammaSeq z n ≠ 0 := by
  rw [Complex.GammaSeq, div_ne_zero_iff]
  constructor
  · apply mul_ne_zero
    · rw [Complex.cpow_ne_zero_iff]; exact Or.inl (by exact_mod_cast hn)
    · exact_mod_cast Nat.factorial_ne_zero n
  · rw [Finset.prod_ne_zero_iff]
    intro j hj h
    have h2 : 0 < (z + (j : ℂ)).re := by
      rw [Complex.add_re]
      have h3 : 0 ≤ ((j : ℂ).re) := by simp
      linarith
    have h4 : (z + (j : ℂ)).re = 0 := by simpa using congrArg Complex.re h
    linarith

/-- The logarithmic derivative of the Euler partial product is holomorphic on the right
half-plane. -/
lemma differentiableOn_logDeriv_GammaSeq (n : ℕ) (hn : n ≠ 0) :
    DifferentiableOn ℂ (fun z : ℂ => logDeriv (fun z : ℂ => Complex.GammaSeq z n) z)
      {z : ℂ | 0 < z.re} := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (fun z => Complex.GammaSeq z n) {z : ℂ | 0 < z.re} :=
    Commons.Analysis.SpecialFunctions.Gamma.GammaSeq_differentiableOn n hn
  have hne : ∀ z ∈ {z : ℂ | 0 < z.re}, Complex.GammaSeq z n ≠ 0 := fun z hz =>
    GammaSeq_ne_zero_of_re_pos hz hn
  have h1 : DifferentiableOn ℂ
      (deriv (fun z => Complex.GammaSeq z n) / fun z => Complex.GammaSeq z n)
      {z : ℂ | 0 < z.re} := (hdiff.deriv hU).div hdiff hne
  refine h1.congr ?_
  intro z hz
  simp [logDeriv_apply]

/-- The `m`-th derivative (`m ≥ 1`) of the log-derivative of the `N`-th Euler partial product is
the finite sum `∑_{k ≤ N} (-1)^{m+1} m! (1/(w+k))^{m+1}`. -/
lemma iteratedDeriv_logDeriv_GammaSeq (m : ℕ) (hm : 1 ≤ m) {w : ℂ} (hw : 0 < w.re)
    (N : ℕ) (hN : 1 ≤ N) :
    iteratedDeriv m (fun z : ℂ => logDeriv (fun z : ℂ => Complex.GammaSeq z N) z) w
      = ∑ k ∈ Finset.range (N+1),
          ((-1 : ℂ)^(m+1) * (m.factorial : ℂ) * (1/(w + (k:ℂ)))^(m+1)) := by
  have hm0 : 0 < m := by omega
  have hN0 : N ≠ 0 := by omega
  have hr : (0:ℝ) < w.re / 2 := by linarith
  -- on a neighbourhood of `w` the log-derivative of the Euler product is the explicit sum
  have hEv : (fun z : ℂ => logDeriv (fun z : ℂ => Complex.GammaSeq z N) z) =ᶠ[nhds w]
      (fun z : ℂ => (Real.log (N : ℝ) : ℂ) - ∑ k ∈ Finset.range (N+1), (z + (k:ℂ))⁻¹) := by
    filter_upwards [Metric.ball_mem_nhds w hr] with z hz
    exact Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaSeq_eq z N
      (Commons.Analysis.SpecialFunctions.Gamma.re_pos_of_mem_ball hz (by linarith)) hN0
  rw [hEv.iteratedDeriv_eq m]
  rw [iteratedDeriv_const_sub hm0]
  change iteratedDeriv m (fun z : ℂ => -(∑ k ∈ Finset.range (N+1), (z + (k:ℂ))⁻¹)) w
      = ∑ k ∈ Finset.range (N+1),
          ((-1 : ℂ)^(m+1) * (m.factorial : ℂ) * (1/(w + (k:ℂ)))^(m+1))
  rw [iteratedDeriv_fun_neg, iteratedDeriv_sum_inv_add_const m w N hw,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [pow_succ]
  ring

/-- The log-derivatives of the Euler partial products converge locally uniformly to
`logDeriv Γ = digamma` on any open set of the right half-plane. -/
lemma tendstoLocallyUniformlyOn_logDeriv_GammaSeq {U : Set ℂ} (hU : IsOpen U)
    (hLU : TendstoLocallyUniformlyOn (fun N z => Complex.GammaSeq z N) Complex.Gamma atTop U)
    (hF0 : ∀ᶠ N in atTop, DifferentiableOn ℂ (fun z => Complex.GammaSeq z N) U)
    (hre : ∀ z ∈ U, 0 < z.re) :
    TendstoLocallyUniformlyOn (fun N z => logDeriv (fun z => Complex.GammaSeq z N) z)
      (logDeriv Complex.Gamma) atTop U := by
  -- `Γ` is differentiable (hence continuous) on the right half-plane, and so is `Γ'`
  have hdg : DifferentiableOn ℂ Complex.Gamma U := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have h1 : z.re = -((m : ℝ)) := by
      have := congrArg Complex.re hm
      simpa using this
    have h2 := hre z hz
    have h3 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hderiv := hLU.deriv hF0 hU
  have hcont_g : ContinuousOn Complex.Gamma U := hdg.continuousOn
  have hcont_d : ContinuousOn (deriv Complex.Gamma) U := (hdg.deriv hU).continuousOn
  have hg0 : ∀ z ∈ U, Complex.Gamma z ≠ 0 := fun z hz =>
    Complex.Gamma_ne_zero_of_re_pos (hre z hz)
  -- `logDeriv Γ_N = (Γ_N)'/Γ_N → Γ'/Γ = logDeriv Γ`, locally uniformly
  have h1 : TendstoLocallyUniformlyOn
      (fun N => deriv (fun z => Complex.GammaSeq z N) / fun z => Complex.GammaSeq z N)
      (deriv Complex.Gamma / Complex.Gamma) atTop U := hderiv.div₀ hLU hcont_d hcont_g hg0
  have h2 : TendstoLocallyUniformlyOn (fun N z => logDeriv (fun z => Complex.GammaSeq z N) z)
      (deriv Complex.Gamma / Complex.Gamma) atTop U :=
    h1.congr (fun N z hz => by simp [logDeriv_apply])
  exact h2.congr_right (fun z hz => by simp [logDeriv_apply])

/-- **Derivatives of the digamma function: the Hurwitz-zeta series.** (module `Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries`; import `Mathlib` and the Gamma modules cited below; declare in `namespace Work.LinnikAreas.FarRepel`.)

For `m ≥ 1` and `Re w > 0`, the series `∑_{n≥0} (-1)^{m+1} m! (1/(w+n))^{m+1}` has sum `ψ^{(m)}(w)`,
i.e. `HasSum (fun n => (-1 : ℂ)^(m+1) * (m.factorial : ℂ) * (1/(w + n))^(m+1)) (iteratedDeriv m Complex.digamma w)`.
(`HasSum` also supplies the summability of the series.)  For `m = 0` the analogous statement is
false (harmonic divergence), which is why `1 ≤ m` is required.

PROOF ROUTE: `Complex.digamma = logDeriv Gamma` (`Complex.digamma_def`). The classical Gauss
limit is available, proved, in this workspace as `Commons.Analysis.SpecialFunctions.Gamma.digamma_partialSum`
(`Tendsto (fun N => log(N+1) - ∑_{k<N+2} (z+k)⁻¹) atTop (𝓝 (digamma z))` for `0 < z.re`), together
with local-uniformity inputs `Commons.Analysis.SpecialFunctions.Gamma.gammaSeq_locallyUniform_halfPlane`
and `...GammaSeq_tendstoUniformlyOn_closedBall` (also `digamma_eq_lim_log_sub_sum_inv`). Differentiate
the partial sums `m` times (the derivatives are the finite sums `∑_{k<N+2} (-1)^{m+1} m! (z+k)^{-(m+1)}`)
and pass to the limit by local uniform convergence of the `m`-th derivatives on a compact
neighbourhood of `w` inside `Re > 0` (Weierstrass / `Mathlib.Analysis.Complex.LocallyUniformLimit`).
The limit of the finite sums is the stated series. -/
theorem digammaDerivSeries (m : ℕ) (hm : 1 ≤ m) {w : ℂ} (hw : 0 < w.re) :
    HasSum (fun n : ℕ =>
        (-1 : ℂ) ^ (m + 1) * (m.factorial : ℂ) * (1 / (w + (n : ℂ))) ^ (m + 1))
      (iteratedDeriv m Complex.digamma w) := by
  -- a small ball around `w` inside the right half-plane
  have hr : (0:ℝ) < w.re / 2 := by linarith
  have hU : IsOpen (Metric.ball w (w.re / 2)) := Metric.isOpen_ball
  have hwU : w ∈ Metric.ball w (w.re / 2) := by simp [Metric.mem_ball, hr]
  have hre : ∀ z ∈ Metric.ball w (w.re / 2), 0 < z.re := fun z hz =>
    Commons.Analysis.SpecialFunctions.Gamma.re_pos_of_mem_ball hz (by linarith)
  -- the Euler products converge uniformly (hence locally uniformly) to `Γ`
  have hunif : TendstoUniformlyOn (fun N z => Complex.GammaSeq z N) Complex.Gamma atTop
      (Metric.closedBall w (w.re / 2)) :=
    Commons.Analysis.SpecialFunctions.Gamma.GammaSeq_tendstoUniformlyOn_closedBall w (w.re/2) hr
      (by linarith)
  have hLU : TendstoLocallyUniformlyOn (fun N z => Complex.GammaSeq z N) Complex.Gamma atTop
      (Metric.ball w (w.re / 2)) :=
    (hunif.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hF0 : ∀ᶠ N in atTop, DifferentiableOn ℂ (fun z => Complex.GammaSeq z N)
      (Metric.ball w (w.re / 2)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (Commons.Analysis.SpecialFunctions.Gamma.GammaSeq_differentiableOn N (by omega)).mono hre
  -- and so do their log-derivatives
  have hLU1 : TendstoLocallyUniformlyOn (fun N z => logDeriv (fun z => Complex.GammaSeq z N) z)
      (logDeriv Complex.Gamma) atTop (Metric.ball w (w.re / 2)) :=
    tendstoLocallyUniformlyOn_logDeriv_GammaSeq hU hLU hF0 hre
  have hF1 : ∀ᶠ N in atTop, DifferentiableOn ℂ
      (fun z => logDeriv (fun z => Complex.GammaSeq z N) z) (Metric.ball w (w.re / 2)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (differentiableOn_logDeriv_GammaSeq N (by omega)).mono hre
  -- Weierstrass: the `m`-th derivatives converge locally uniformly to the `m`-th derivative
  have hLU2 := tendstoLocallyUniformlyOnIterateDeriv hU hF1 hLU1 m
  have hconv := hLU2.tendsto_at hwU
  -- the partial sums, evaluated at `w`
  have hev : ∀ᶠ N in atTop, deriv^[m] (fun z => logDeriv (fun z => Complex.GammaSeq z N) z) w
      = ∑ k ∈ Finset.range (N+1),
          ((-1 : ℂ)^(m+1) * (m.factorial : ℂ) * (1/(w + (k:ℂ)))^(m+1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_logDeriv_GammaSeq m hm hw N hN
  have hconv2 := hconv.congr' hev
  have hL : deriv^[m] (logDeriv Complex.Gamma) w = iteratedDeriv m Complex.digamma w := by
    rw [iteratedDeriv_eq_iterate, ← Complex.digamma_def]
  rw [hL] at hconv2
  -- reindex the partial sums from `range (N+1)` to `range M`
  have hshift : Tendsto (fun N : ℕ => (fun M => ∑ k ∈ Finset.range M,
      ((-1 : ℂ)^(m+1) * (m.factorial : ℂ) * (1/(w + (k:ℂ)))^(m+1))) (N+1)) atTop
      (nhds (iteratedDeriv m Complex.digamma w)) := by
    simpa only using hconv2
  have hrange : Tendsto (fun M => ∑ k ∈ Finset.range M,
      ((-1 : ℂ)^(m+1) * (m.factorial : ℂ) * (1/(w + (k:ℂ)))^(m+1))) atTop
      (nhds (iteratedDeriv m Complex.digamma w)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mp hshift
  -- summability upgrades convergence of the partial sums to `HasSum`
  exact (Summable.hasSum_iff_tendsto_nat (digammaDerivSeriesSummable m hm hw)).mpr hrange

end Work.LinnikAreas.FarRepel
