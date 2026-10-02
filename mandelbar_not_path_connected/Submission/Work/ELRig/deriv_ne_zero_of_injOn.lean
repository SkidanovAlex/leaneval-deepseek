import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Filter Metric
open scoped Topology

theorem deriv_ne_zero_of_injOn {U : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hinj : Set.InjOn f U) {z : ℂ} (hz : z ∈ U) : deriv f z ≠ 0 := by
  intro hderiv
  have hf_an : AnalyticAt ℂ f z := (hf.analyticOn hU).analyticAt (hU.mem_nhds hz)
  set G : ℂ → ℂ := fun w => f w - f z with hGdef
  have hG_an : AnalyticAt ℂ G z := by
    have h := hf_an.sub (analyticAt_const (v := f z))
    rw [hGdef]
    exact h
  -- the order of vanishing of G at z is at least 2
  have h2le : (2 : ℕ∞) ≤ analyticOrderAt G z := by
    have hgoal : (((2 : ℕ)) : ℕ∞) ≤ analyticOrderAt G z := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hG_an]
      intro i hi
      interval_cases i
      · simp [hGdef]
      · rw [iteratedDeriv_one, hGdef, deriv_sub_const]
        exact hderiv
    exact hgoal
  -- G is not eventually zero near z, else injectivity fails at once
  have hne_top : analyticOrderAt G z ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hmem : U ∩ {w | G w = 0} ∈ 𝓝 z := Filter.inter_mem (hU.mem_nhds hz) htop
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hmem
    set w₀ : ℂ := z + ((δ / 2 : ℝ) : ℂ) with hw₀def
    have hw₀ball : w₀ ∈ ball z δ := by
      have hsub : w₀ - z = ((δ / 2 : ℝ) : ℂ) := by rw [hw₀def, add_sub_cancel_left]
      rw [Metric.mem_ball, dist_eq_norm, hsub]
      have hnorm : ‖(((δ / 2 : ℝ)) : ℂ)‖ = δ / 2 := by
        have h1 : (((δ / 2 : ℝ)) : ℂ) = (δ : ℂ) / 2 := by push_cast; ring
        rw [h1, norm_div]
        simp [abs_of_pos hδpos]
      rw [hnorm]
      linarith
    obtain ⟨hw₀U, hw₀G⟩ := hδsub hw₀ball
    have hfw : f w₀ = f z := by
      have h := hw₀G; rw [hGdef] at h; exact sub_eq_zero.mp h
    have hne : w₀ ≠ z := by
      intro h
      rw [hw₀def] at h
      have h2 : ((δ / 2 : ℝ) : ℂ) = 0 := by
        have := congrArg (fun x : ℂ => x - z) h
        simpa using this
      rw [Complex.ofReal_eq_zero] at h2
      linarith
    exact hne (hinj hw₀U hz hfw)
  -- factor G as (w - z)^n * u w with n >= 2 and u z != 0
  obtain ⟨u, hu_an, hu_ne, hG_eq0⟩ := (hG_an.analyticOrderAt_ne_top).mp hne_top
  set n : ℕ := analyticOrderNatAt G z with hndef
  have hG_eq : G =ᶠ[𝓝 z] fun w => (w - z) ^ n • u w := by
    filter_upwards [hG_eq0] with w hw
    rw [hw, hndef]
  have hn2 : 2 ≤ n := by
    have hcast : (2 : ℕ∞) ≤ (n : ℕ∞) := by
      rw [hndef, Nat.cast_analyticOrderNatAt hne_top]
      exact h2le
    exact ENat.natCast_le_natCast.mp hcast
  have hn0 : n ≠ 0 := by omega
  -- The complex constant `a` with a^n = u z
  set a : ℂ := u z ^ ((n : ℂ)⁻¹) with hadef
  have ha_pow : a ^ n = u z := by
    rw [hadef]; exact Complex.cpow_nat_inv_pow (u z) hn0
  have ha_ne : a ≠ 0 := by
    intro h
    have h' : a ^ n = 0 := by rw [h]; exact zero_pow hn0
    rw [ha_pow] at h'
    exact hu_ne h'
  -- the ratio h := (u - u z)/u z
  set h : ℂ → ℂ := fun w => (u w - u z) / u z with hhdef
  have hh_an : AnalyticAt ℂ h z := by
    have h1 : AnalyticAt ℂ (fun w => u w - u z) z := hu_an.sub (analyticAt_const (v := u z))
    have h2 : AnalyticAt ℂ (fun w => (u w - u z) / u z) z := h1.div_const
    simpa [hhdef] using h2
  have hh_z : h z = 0 := by simp [hhdef]
  -- R := (1 + ·)^(1/n)
  set R : ℂ → ℂ := fun w => (1 + w) ^ ((n : ℂ)⁻¹) with hRdef
  have hR_an : AnalyticAt ℂ R 0 := by
    have h := (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := (n : ℂ)⁻¹)).analyticAt
    simpa [hRdef] using h
  have hR0 : R 0 = 1 := by simp [hRdef]
  have hRcomp_an : AnalyticAt ℂ (fun w => R (h w)) z := by
    have hRz : AnalyticAt ℂ R (h z) := by rw [hh_z]; exact hR_an
    have := hRz.comp hh_an
    simpa [Function.comp_def] using this
  -- the local n-th root rho
  set ρ : ℂ → ℂ := fun w => (w - z) * (a * R (h w)) with hρdef
  have h2_an : AnalyticAt ℂ (fun w => a * R (h w)) z :=
    (analyticAt_const (v := a)).mul hRcomp_an
  have hρ_an : AnalyticAt ℂ ρ z := by
    have h1 : AnalyticAt ℂ (fun w => w - z) z := analyticAt_id.sub (analyticAt_const (v := z))
    have hthis : AnalyticAt ℂ ((fun w : ℂ => w - z) * (fun w : ℂ => a * R (h w))) z := h1.mul h2_an
    rw [hρdef]
    exact hthis
  have hρ_z : ρ z = 0 := by simp [hρdef]
  have hρ_deriv : deriv ρ z = a := by
    have h1 : DifferentiableAt ℂ (fun w : ℂ => w - z) z := by fun_prop
    have h2d : DifferentiableAt ℂ (fun w : ℂ => a * R (h w)) z := h2_an.differentiableAt
    have hstep : deriv ρ z = a * R (h z) := by
      rw [hρdef]
      change deriv ((fun w : ℂ => w - z) * (fun w : ℂ => a * R (h w))) z = a * R (h z)
      simpa using deriv_mul h1 h2d
    rw [hstep, hh_z, hR0, mul_one]
  -- rho^n = G on a neighbourhood of z
  have hρ_pow : ∀ w, ρ w ^ n = (w - z) ^ n * u w := by
    intro w
    simp only [hρdef, hRdef]
    rw [mul_pow, mul_pow, ha_pow, Complex.cpow_nat_inv_pow (1 + h w) hn0]
    simp only [hhdef]
    have h1 : u z * (1 + (u w - u z) / u z) = u w := by
      rw [mul_add, mul_one, mul_div_cancel₀ (u w - u z) hu_ne]
      ring
    rw [h1]
  have hG_eq_ρ : G =ᶠ[𝓝 z] ρ ^ n := by
    filter_upwards [hG_eq] with w hw
    show G w = ρ w ^ n
    rw [hρ_pow w]
    simpa using hw
  have hρ_notconst : ¬ (∀ᶠ w in 𝓝 z, ρ w = ρ z) := by
    intro hc
    have hd : deriv ρ z = 0 := by
      rw [Filter.EventuallyEq.deriv_eq hc]
      exact deriv_const z (ρ z)
    rw [hρ_deriv] at hd
    exact ha_ne hd
  have hopen : 𝓝 (ρ z) ≤ Filter.map ρ (𝓝 z) :=
    (hρ_an.eventually_constant_or_nhds_le_map_nhds).resolve_left hρ_notconst
  rw [hρ_z] at hopen
  -- combine the neighbourhoods
  obtain ⟨δ, hδpos, hδU, hδρ⟩ :
      ∃ δ > 0, ball z δ ⊆ U ∧ ∀ w ∈ ball z δ, G w = ρ w ^ n := by
    have hmem : U ∩ {w | G w = ρ w ^ n} ∈ 𝓝 z :=
      Filter.inter_mem (hU.mem_nhds hz) hG_eq_ρ
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨δ, hδ, fun w hw => (hsub hw).1, fun w hw => (hsub hw).2⟩
  have himg : ρ '' ball z δ ∈ 𝓝 (0 : ℂ) := by
    have hmm : ρ '' ball z δ ∈ Filter.map ρ (𝓝 z) :=
      Filter.image_mem_map (Metric.ball_mem_nhds z hδpos)
    exact hopen hmm
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp himg
  -- a nontrivial n-th root of unity
  obtain ⟨ω, hω_pow, hω_ne⟩ : ∃ ω : ℂ, ω ^ n = 1 ∧ ω ≠ 1 := by
    refine ⟨Complex.exp (2 * Real.pi * Complex.I / n), ?_, ?_⟩
    · exact (Complex.isPrimitiveRoot_exp n hn0).pow_eq_one
    · exact (Complex.isPrimitiveRoot_exp n hn0).ne_one (by omega)
  -- two small values with equal n-th powers
  set t : ℝ := ε / (2 * (1 + ‖ω‖)) with htdef
  have hden : 0 < 2 * (1 + ‖ω‖) := by positivity
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht_eps : t < ε := by
    rw [htdef, div_lt_iff₀ hden]
    nlinarith [norm_nonneg ω, hεpos]
  have hwt_eps : ‖ω‖ * t < ε := by
    rw [htdef]
    have heq : ‖ω‖ * (ε / (2 * (1 + ‖ω‖))) = ε * ‖ω‖ / (2 * (1 + ‖ω‖)) := by ring
    rw [heq, div_lt_iff₀ hden]
    nlinarith [norm_nonneg ω, hεpos]
  have hnorm_t : ‖(t : ℂ)‖ = t := by simp [abs_of_pos htpos]
  have hw1ball : (t : ℂ) ∈ ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right, hnorm_t]
    exact ht_eps
  have hw2ball : (ω * t : ℂ) ∈ ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hnorm_t]
    exact hwt_eps
  obtain ⟨z1, hz1ball, hz1eq⟩ := hεsub hw1ball
  obtain ⟨z2, hz2ball, hz2eq⟩ := hεsub hw2ball
  have hz1U : z1 ∈ U := hδU hz1ball
  have hz2U : z2 ∈ U := hδU hz2ball
  have hpow_eq : ρ z1 ^ n = ρ z2 ^ n := by
    rw [hz1eq, hz2eq, mul_pow, hω_pow, one_mul]
  have hG_eq2 : G z1 = G z2 := by
    rw [hδρ z1 hz1ball, hδρ z2 hz2ball, hpow_eq]
  have hf_eq : f z1 = f z2 := by
    have h1 : f z1 - f z = f z2 - f z := by
      have h := hG_eq2; rw [hGdef] at h; exact h
    have := congrArg (fun x : ℂ => x + f z) h1
    simpa using this
  have hz_ne : z1 ≠ z2 := by
    intro h
    have heq : ρ z1 = ρ z2 := by rw [h]
    rw [hz1eq, hz2eq] at heq
    have htne : (t : ℂ) ≠ 0 := fun hh => (ne_of_gt htpos) (Complex.ofReal_inj.mp hh)
    have h2 : ω * (t : ℂ) = 1 * (t : ℂ) := (heq.symm).trans (one_mul (t : ℂ)).symm
    exact hω_ne (mul_right_cancel₀ htne h2)
  exact hz_ne (hinj hz1U hz2U hf_eq)

end Work.ELRig
