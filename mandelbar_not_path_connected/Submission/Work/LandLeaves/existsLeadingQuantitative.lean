import Mathlib
import Submission.Work.LandLeaves.exists_leading_coeff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology

/-- **Quantitative leading term of a germ tangent to the identity.**  If `H` is analytic at `0`
with `H 0 = 0`, `deriv H 0 = 1` and `H` is not the identity near `0`, then there are `r ≥ 2`,
`c ≠ 0`, `ρ > 0` and `A ≥ 0` with `‖H z - z - c * z^r‖ ≤ A * ‖z‖^(r+1)` for `‖z‖ < ρ`.

Hint. `Work.LandLeaves.exists_leading_coeff` (in
`Submission/Work/LandLeaves/exists_leading_coeff.lean`) gives `r = n + 1 ≥ 2`, `c ≠ 0` and
`H z - z - c z^r = o(z^r)` at `0`; analyticity upgrades this by one order, since the quotient
`(H z - z - c z^r) / z^r` is analytic at `0` and vanishes there.  The conclusion is exactly the
hypothesis consumed by `Work.LandLeaves.chart_descent_bound`. -/
theorem existsLeadingQuantitative {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) (h0 : H 0 = 0)
    (hder : deriv H 0 = 1) (hlin : ¬ (Filter.EventuallyEq (nhds 0) H fun w => w)) :
    ∃ (r : ℕ) (c : ℂ), 2 ≤ r ∧ c ≠ 0 ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ z : ℂ, ‖z‖ < ρ → ‖H z - z - c * z ^ r‖ ≤ A * ‖z‖ ^ (r + 1) := by
  -- The nonlinear part `N = H - id`.
  set N : ℂ → ℂ := fun w => H w - w with hNdef
  have hNa : AnalyticAt ℂ N 0 := by
    rw [hNdef]; exact hH.sub (by fun_prop)
  have hN0 : N 0 = 0 := by rw [hNdef]; simp [h0]
  have hNder : deriv N 0 = 0 := by
    rw [hNdef]
    have h1 : deriv (fun w : ℂ => H w - w) 0 = deriv H 0 - deriv (fun w : ℂ => w) 0 :=
      deriv_sub hH.differentiableAt differentiableAt_id
    rw [h1, hder]; simp
  -- `N ≢ 0` near `0`, because `H` is not the identity there.
  have hNne : ¬ ∀ᶠ w in 𝓝 (0:ℂ), N w = 0 := by
    intro h
    apply hlin
    filter_upwards [h] with w hw
    rw [hNdef] at hw
    exact sub_eq_zero.mp hw
  have htop : analyticOrderAt N 0 ≠ ⊤ := by
    intro h
    exact hNne ((analyticOrderAt_eq_top).mp h)
  -- Structural factorization `N z = z^m · g z` with `g` analytic and `g 0 ≠ 0`.
  obtain ⟨g, hga, hg0ne, hgeq⟩ := (AnalyticAt.analyticOrderAt_ne_top hNa).mp htop
  -- The vanishing order `m` of `N` is at least `2`.
  have hm2 : 2 ≤ analyticOrderNatAt N 0 := by
    have h2 : (2:ℕ∞) ≤ analyticOrderAt N 0 :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hNa).mpr (by
        intro i hi
        interval_cases i
        · simpa using hN0
        · simpa [iteratedDeriv_one] using hNder)
    rw [← Nat.cast_analyticOrderNatAt htop] at h2
    exact_mod_cast h2
  have hgeq' : ∀ᶠ z in 𝓝 (0:ℂ), N z = z ^ (analyticOrderNatAt N 0) * g z := by
    filter_upwards [hgeq] with z hz
    simpa using hz
  -- Taylor expansion of `g` at order one: `g z = g 0 + z · F z` with `F` analytic at `0`.
  obtain ⟨F, hFa, hFeq⟩ := hga.exists_eq_sum_add_pow_mul 1
  have hFeq' : ∀ z, g z - g 0 = z * F z := by
    intro z
    have := hFeq z
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, iteratedDeriv_zero, pow_one, one_smul] at this
    rw [this]; ring
  -- `F` is bounded near `0`.
  have hV : ∀ᶠ z in 𝓝 (0:ℂ), ‖F z‖ ≤ ‖F 0‖ + 1 := by
    have ht : Tendsto (fun z : ℂ => ‖F z‖) (𝓝 (0:ℂ)) (𝓝 ‖F 0‖) := hFa.continuousAt.norm
    have := ht.eventually (isOpen_Iio.mem_nhds (lt_add_one (‖F 0‖)))
    filter_upwards [this] with z hz using le_of_lt hz
  -- Combine the two eventual statements into a ball around `0`.
  obtain ⟨U, hU0, hUU⟩ := Filter.eventually_iff_exists_mem.mp (hgeq'.and hV)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hU0
  refine ⟨analyticOrderNatAt N 0, g 0, hm2, hg0ne, ρ, hρpos, ‖F 0‖ + 1, by positivity, ?_⟩
  intro z hz
  have hzU : z ∈ U := hρsub (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  obtain ⟨hNz, hFz⟩ := hUU z hzU
  calc ‖H z - z - g 0 * z ^ (analyticOrderNatAt N 0)‖
      = ‖z ^ (analyticOrderNatAt N 0) * (g z - g 0)‖ := by
        congr 1
        rw [show H z - z = N z from by rw [hNdef]]
        rw [hNz]; ring
    _ = ‖z‖ ^ (analyticOrderNatAt N 0) * ‖g z - g 0‖ := by
        rw [norm_mul, norm_pow]
    _ = ‖z‖ ^ (analyticOrderNatAt N 0) * (‖z‖ * ‖F z‖) := by
        rw [hFeq' z, norm_mul]
    _ ≤ ‖z‖ ^ (analyticOrderNatAt N 0) * (‖z‖ * (‖F 0‖ + 1)) := by
        gcongr
    _ = (‖F 0‖ + 1) * ‖z‖ ^ (analyticOrderNatAt N 0 + 1) := by
        rw [pow_succ]; ring

end Work.LandLeaves
