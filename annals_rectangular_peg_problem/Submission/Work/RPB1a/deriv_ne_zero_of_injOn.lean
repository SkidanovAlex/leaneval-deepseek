import Mathlib
import Submission.Work.RPB1a.exists_local_log
import Submission.Work.RPB1a.exists_pow_eq_one_ne_one
import Submission.Work.RPB1a.hasStrictDerivAt_self_mul_exp_div

namespace Work.RPB1a

open Complex Set Metric Filter
open scoped ContDiff Real Topology

/-- An injective holomorphic function on an open set has nonvanishing derivative everywhere.

Suggested route: suppose `deriv f z₀ = 0` with `z₀ ∈ U`.  `hd` on the open set `U` makes `f`
`AnalyticAt ℂ` at `z₀`, and injectivity on the open `U` (which has more than one point near `z₀`)
rules out `f` being eventually constant.  Using the local normal form
(`AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`, or `AnalyticAt.analyticOrderAt_ne_top`) with
`F := f - f z₀` one gets `k ≥ 2` and `G` analytic near `z₀` with `G z₀ ≠ 0` and
`F =ᶠ[𝓝 z₀] (· - z₀)^k * G`.

Then on a small ball `B` around `z₀` contained in `U` where `G` does not vanish, take a primitive
`L` of `G' / G` on `B` (a disc is convex/simply connected: `DifferentiableOn.isExactOn_ball`, or
`DifferentiableOn.hasPrimitive`), normalised by `L z₀ = 0`.  Then `G * exp (-L)` has vanishing
derivative on the (pre)connected `B`, hence is constant: `G = G z₀ * exp L` on `B`.  Put
`w z := (z - z₀) * exp (L z / k)`; then `F = (G z₀) * w^k` on `B`, `w z₀ = 0` and
`deriv w z₀ = 1 ≠ 0`, so `w` has a local inverse `r` at `z₀`
(`AnalyticAt.hasStrictDerivAt`, `HasStrictFDerivAt.localInverse`, `eventually_right_inverse`).

Finally pick `ζ ≠ 1` with `ζ ^ k = 1` (possible since `k ≥ 2`, e.g. `ζ = Complex.exp (2 * π * I / k)`)
and `t > 0` small; the points `z₁ = r t`, `z₂ = r (t * ζ)` lie in `U`, are distinct (their `w`-images
are `t` and `t * ζ ≠ t`) and satisfy `f z₁ = f z₂`, contradicting `InjOn f U`. -/
theorem deriv_ne_zero_of_injOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f U) (hi : InjOn f U) : ∀ z ∈ U, deriv f z ≠ 0 := by
  intro z₀ hz₀U hderiv
  have hf_an : AnalyticAt ℂ f z₀ := hd.analyticOnNhd hU z₀ hz₀U
  have hF_an : AnalyticAt ℂ (fun z => f z - f z₀) z₀ := hf_an.sub analyticAt_const
  -- `F = f - f z₀` is not eventually zero near `z₀`: that would make `f` non-injective on `U`.
  have hF_ne : ¬ ∀ᶠ z in 𝓝 z₀, f z - f z₀ = 0 := by
    intro hF0
    have hset : {z : ℂ | f z - f z₀ = 0} ∩ U ∈ 𝓝 z₀ :=
      Filter.inter_mem hF0 (hU.mem_nhds hz₀U)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hset
    have hmem : z₀ + ((ε / 2 : ℝ) : ℂ) ∈ ball z₀ ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (half_pos hε).le]
      linarith
    obtain ⟨hFz, hzU⟩ := hεsub hmem
    have hzne : z₀ + ((ε / 2 : ℝ) : ℂ) ≠ z₀ := by
      intro h
      have h2 : ((ε / 2 : ℝ) : ℂ) = 0 := by
        have h' : z₀ + ((ε / 2 : ℝ) : ℂ) = z₀ + 0 := by simpa using h
        exact add_left_cancel h'
      have h3 : (ε / 2 : ℝ) = 0 := Complex.ofReal_eq_zero.mp h2
      linarith
    exact hzne (hi hzU hz₀U (sub_eq_zero.mp hFz))
  have hF_ne_top : analyticOrderAt (fun z => f z - f z₀) z₀ ≠ ⊤ :=
    fun h => hF_ne (analyticOrderAt_eq_top.mp h)
  -- Local normal form of `F` at `z₀`.
  obtain ⟨k, G, hG_an, hG_ne, hFG⟩ :=
    (hF_an.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hF_ne
  -- `k` is the analytic order of `F` at `z₀` (uniqueness of the exponent).
  have hord_repr : ∃ g, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, (fun z => f z - f z₀) z =
        (z - z₀) ^ (analyticOrderNatAt (fun z => f z - f z₀) z₀) • g z :=
    hF_an.analyticOrderAt_ne_top.mp hF_ne_top
  have huniq : k = analyticOrderNatAt (fun z => f z - f z₀) z₀ :=
    AnalyticAt.unique_eventuallyEq_pow_smul_nonzero ⟨G, hG_an, hG_ne, hFG⟩ hord_repr
  -- `deriv f z₀ = 0` and `F z₀ = 0` give order at least `2`.
  have hord2 : (2 : ℕ∞) ≤ analyticOrderAt (fun z => f z - f z₀) z₀ := by
    refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2) hF_an).mpr ?_
    intro i hi
    interval_cases i
    · rw [iteratedDeriv_zero]; simp
    · rw [iteratedDeriv_one]
      have hdf : DifferentiableAt ℂ f z₀ := hd.differentiableAt (hU.mem_nhds hz₀U)
      have hder : deriv (fun z => f z - f z₀) z₀ = deriv f z₀ :=
        (hdf.hasDerivAt.sub_const (f z₀)).deriv
      rw [hder, hderiv]
  have hk2 : 2 ≤ k := by
    rw [huniq]
    have : (2 : ℕ∞) ≤ (analyticOrderNatAt (fun z => f z - f z₀) z₀ : ℕ∞) := by
      rw [Nat.cast_analyticOrderNatAt hF_ne_top]
      exact hord2
    exact Nat.cast_le.mp this
  have hFG' : ∀ᶠ z in 𝓝 z₀, f z - f z₀ = (z - z₀) ^ k * G z := by
    filter_upwards [hFG] with z hz
    simpa [smul_eq_mul] using hz
  -- Choose a ball on which all the local properties hold.
  have hGne_ev : ∀ᶠ z in 𝓝 z₀, G z ≠ 0 := hG_an.continuousAt.eventually_ne hG_ne
  have hGan_ev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ G z := (isOpen_analyticAt ℂ G).mem_nhds hG_an
  have hAll : ∀ᶠ z in 𝓝 z₀,
      z ∈ U ∧ f z - f z₀ = (z - z₀) ^ k * G z ∧ G z ≠ 0 ∧ AnalyticAt ℂ G z := by
    filter_upwards [hU.mem_nhds hz₀U, hFG', hGne_ev, hGan_ev] with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨r, hr, hBsub⟩ := Metric.mem_nhds_iff.mp hAll
  have hzU : ∀ z ∈ ball z₀ r, z ∈ U := fun z hz => (hBsub hz).1
  have hzEq : ∀ z ∈ ball z₀ r, f z - f z₀ = (z - z₀) ^ k * G z :=
    fun z hz => (hBsub hz).2.1
  have hzGne : ∀ z ∈ ball z₀ r, G z ≠ 0 := fun z hz => (hBsub hz).2.2.1
  have hzGan : ∀ z ∈ ball z₀ r, AnalyticAt ℂ G z := fun z hz => (hBsub hz).2.2.2
  -- Holomorphic logarithm of `G` on the ball.
  obtain ⟨L, hL0, hLdiff, hLlog⟩ := exists_local_log hr hzGan hzGne
  -- The `k`-th root `w` of `F / G z₀` on the ball.
  set w : ℂ → ℂ := fun z => (z - z₀) * Complex.exp (L z / k) with hwdef
  have hwz₀ : w z₀ = 0 := by rw [hwdef]; simp
  have hw_strict : HasStrictDerivAt w 1 z₀ := by
    rw [hwdef]
    exact hasStrictDerivAt_self_mul_exp_div hr (by omega) hL0 hLdiff
  -- `w` maps the ball onto a neighbourhood of `0`.
  have hmap : map w (𝓝 z₀) = 𝓝 0 := by
    have h' := hw_strict.map_nhds_eq one_ne_zero
    rwa [hwz₀] at h'
  have hwB : w '' ball z₀ r ∈ 𝓝 0 := by
    rw [← hmap]
    exact image_mem_map (ball_mem_nhds z₀ hr)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hwB
  -- A nontrivial `k`-th root of unity.
  obtain ⟨ζ, hζk, hζne⟩ := exists_pow_eq_one_ne_one k hk2
  set t : ℝ := δ / (2 * (1 + ‖ζ‖)) with htdef
  have ht_pos : 0 < t := by rw [htdef]; positivity
  have ht_lt : t < δ := by
    rw [htdef, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg ζ, hδ]
  have ht_mem : (t : ℂ) ∈ ball 0 δ := by
    rw [mem_ball, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
    exact ht_lt
  have hu_lt : t * ‖ζ‖ < δ := by
    rw [htdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg ζ, hδ]
  have hu_mem : (t : ℂ) * ζ ∈ ball 0 δ := by
    rw [mem_ball, dist_eq_norm, sub_zero, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht_pos.le]
    exact hu_lt
  obtain ⟨z₁, hz₁B, hz₁w⟩ := hδsub ht_mem
  obtain ⟨z₂, hz₂B, hz₂w⟩ := hδsub hu_mem
  -- On the ball, `F` is the `k`-th power of `w`, up to the constant `G z₀`.
  have hFw : ∀ z ∈ ball z₀ r, f z - f z₀ = G z₀ * w z ^ k := by
    intro z hz
    have hkc : (k : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
    rw [hzEq z hz, hLlog z hz, hwdef, mul_pow, ← Complex.exp_nat_mul,
      show (↑k : ℂ) * (L z / ↑k) = L z from by field_simp]
    ring
  have hkey : G z₀ * w z₁ ^ k = G z₀ * w z₂ ^ k := by
    rw [hz₁w, hz₂w, mul_pow, hζk, mul_one]
  have hfeq : f z₁ = f z₂ := by
    have hsub : f z₁ - f z₀ = f z₂ - f z₀ := by rw [hFw z₁ hz₁B, hFw z₂ hz₂B, hkey]
    exact sub_left_injective hsub
  have hzneq : z₁ ≠ z₂ := by
    intro h
    have htmp : (t : ℂ) = (t : ℂ) * ζ :=
      calc (t : ℂ) = w z₁ := hz₁w.symm
        _ = w z₂ := by rw [h]
        _ = (t : ℂ) * ζ := hz₂w
    have ht_ne : (t : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact ht_pos.ne'
    have h1 : (1 : ℂ) = ζ := by
      apply mul_left_cancel₀ ht_ne
      rw [mul_one]; exact htmp
    exact hζne h1.symm
  exact hzneq (hi (hzU z₁ hz₁B) (hzU z₂ hz₂B) hfeq)

end Work.RPB1a
