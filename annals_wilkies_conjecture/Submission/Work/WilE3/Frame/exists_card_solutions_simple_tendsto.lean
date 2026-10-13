import Mathlib
import Submission.Work.WilE3.Lib.exists_card_solutions_eq_analyticOrderAt
import Submission.Work.WilE3.Lib.exists_analyticAt_pow_eq
import Submission.Work.WilE3.Lib.card_nthRootsFinset_complex

namespace Work.WilE3.Frame

set_option autoImplicit false
open Classical Topology

/-- **Simplicity of the solutions.**  Suppose `g = φ ^ N` on `ball z₀ r`, `ψ` is a left inverse
of `φ` on that ball (`ψ (φ t) = t`), `φ` is analytic there, and `ψ` is analytic near `0`.
If `z` lies in the ball and satisfies `g z = ε` with `ε ≠ 0` and `‖ε‖ < μ ^ N`, then
`deriv g z ≠ 0`.

Indeed such a `z` satisfies `φ z ^ N = ε`, so `‖φ z‖ = ‖ε‖ ^ (1/N) < μ` lies in the region
where `ψ` is analytic; the identity `ψ ∘ φ = id` near `z` gives, by the chain rule,
`deriv ψ (φ z) * deriv φ z = 1`, hence `deriv φ z ≠ 0`, and finally
`deriv g z = N * (φ z) ^ (N - 1) * deriv φ z ≠ 0`. -/
private theorem deriv_ne_zero_of_simple_solution {φ ψ g : ℂ → ℂ} {z₀ z ε : ℂ} {N : ℕ}
    {r μ : ℝ} (hN0 : N ≠ 0) (hμ : 0 < μ)
    (hpow : ∀ t : ℂ, ‖t - z₀‖ < r → g t = φ t ^ N)
    (hleft : ∀ t : ℂ, ‖t - z₀‖ < r → ψ (φ t) = t)
    (hφan : ∀ t : ℂ, ‖t - z₀‖ < r → AnalyticAt ℂ φ t)
    (hψana : ∀ y : ℂ, ‖y‖ < μ → AnalyticAt ℂ ψ y)
    (hzr : ‖z - z₀‖ < r) (hgz : g z = ε) (hε0 : ε ≠ 0) (hlt : ‖ε‖ < μ ^ N) :
    deriv g z ≠ 0 := by
  have hφzN : φ z ^ N = ε := by rw [← hpow z hzr]; exact hgz
  have hφzne : φ z ≠ 0 := fun h => hε0 (by rw [← hφzN, h, zero_pow hN0])
  have hnorm : ‖φ z‖ ^ N = ‖ε‖ := by rw [← norm_pow, hφzN]
  have hφz_small : ‖φ z‖ < μ :=
    (pow_lt_pow_iff_left₀ (norm_nonneg _) hμ.le hN0).mp (by rw [hnorm]; exact hlt)
  have hball : Metric.ball z₀ r ∈ 𝓝 z :=
    IsOpen.mem_nhds Metric.isOpen_ball (by simpa [Metric.mem_ball, dist_eq_norm] using hzr)
  have heq : (ψ ∘ φ) =ᶠ[𝓝 z] id := by
    filter_upwards [hball] with t ht
    simp only [Function.comp_apply, id]
    exact hleft t (by simpa [Metric.mem_ball, dist_eq_norm] using ht)
  have hcomp1 : deriv (ψ ∘ φ) z = 1 := by rw [heq.deriv_eq, deriv_id]
  have hchain : deriv (ψ ∘ φ) z = deriv ψ (φ z) * deriv φ z :=
    deriv_comp z (hψana (φ z) hφz_small).differentiableAt (hφan z hzr).differentiableAt
  have hderivφ : deriv φ z ≠ 0 := by
    intro h0
    have h10 : (1 : ℂ) = 0 := by rw [← hcomp1, hchain, h0, mul_zero]
    exact one_ne_zero h10
  have hgg : g =ᶠ[𝓝 z] (fun t => φ t ^ N) := by
    filter_upwards [hball] with t ht
    exact hpow t (by simpa [Metric.mem_ball, dist_eq_norm] using ht)
  rw [hgg.deriv_eq, deriv_fun_pow (hφan z hzr).differentiableAt N]
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hN0) (pow_ne_zero _ hφzne)) hderivφ

/-- **One-variable counting with simplicity and convergence.** Strengthens `Work.WilE3.Lib.exists_card_solutions_eq_analyticOrderAt` by recording that the `N` solutions of `g = ε` in the disc are simple (`deriv g z ≠ 0`), which is what makes them nondegenerate zeros of the complexified system, and that they converge to `z₀` as `ε → 0`. -/
theorem exists_card_solutions_simple_tendsto {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀)
    (h0 : g z₀ = 0) (N : ℕ) (hord : analyticOrderAt g z₀ = N) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      (∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ →
        ∃ s : Finset ℂ, s.card = N ∧
          (∀ z ∈ s, g z = ε ∧ ‖z - z₀‖ < r ∧ deriv g z ≠ 0) ∧
          (∀ z : ℂ, g z = ε → ‖z - z₀‖ < r → z ∈ s)) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ∀ z : ℂ, g z = ε → ‖z - z₀‖ < r →
        ‖z - z₀‖ < η) := by
  classical
  -- `N ≠ 0`, since `g z₀ = 0`.
  have hN0 : N ≠ 0 := by
    intro hN
    exact (hg.analyticOrderAt_ne_zero.mpr h0) (by simp [hord, hN])
  -- Factor `g = (· - z₀)^N * u` with `u` analytic and `u z₀ ≠ 0`.
  obtain ⟨u, hu, hu0, hgu⟩ := (hg.analyticOrderAt_eq_natCast (n := N)).mp hord
  -- An `N`-th root `v` of `u`.
  obtain ⟨v, hv, hv0, hvu⟩ := Work.WilE3.Lib.exists_analyticAt_pow_eq (N := N) hu hu0 hN0
  -- The local biholomorphism `φ z = (z - z₀) * v z`, with `φ ^ N = g` near `z₀`.
  set φ : ℂ → ℂ := fun z => (z - z₀) * v z with hφdef
  have hφ0 : φ z₀ = 0 := by rw [hφdef]; simp
  have hφan : AnalyticAt ℂ φ z₀ := by
    rw [hφdef]; exact (analyticAt_id.sub analyticAt_const).mul hv
  have hderiv0 : deriv φ z₀ = v z₀ := by
    rw [hφdef, deriv_fun_mul]
    · simp
    · fun_prop
    · exact hv.differentiableAt
  have hderiv0ne : deriv φ z₀ ≠ 0 := by rw [hderiv0]; exact hv0
  have hpow : ∀ᶠ z in 𝓝 z₀, g z = φ z ^ N := by
    filter_upwards [hgu] with z hz
    rw [hz, hφdef, mul_pow, hvu z, smul_eq_mul]
  obtain ⟨ran, hran, hran_ball⟩ := Metric.mem_nhds_iff.mp hpow
  have hran_ball' : ∀ z : ℂ, ‖z - z₀‖ < ran → g z = φ z ^ N := fun z hz =>
    hran_ball (by rwa [Metric.mem_ball, dist_eq_norm])
  -- The local inverse `ψ` of `φ` at `z₀`, which is analytic, continuous and the two-sided
  -- inverse of `φ` locally.
  set ψ : ℂ → ℂ :=
    HasStrictDerivAt.localInverse φ (deriv φ z₀) z₀ hφan.hasStrictDerivAt hderiv0ne with hψdef
  have hψana0 : AnalyticAt ℂ ψ 0 := by
    have h := hφan.analyticAt_localInverse hderiv0ne
    rwa [hφ0] at h
  have hψleft : ∀ᶠ z in 𝓝 z₀, ψ (φ z) = z := by
    have h := hφan.hasStrictDerivAt.eventually_left_inverse hderiv0ne
    rwa [hψdef]
  have hψright : ∀ᶠ y in 𝓝 (0 : ℂ), φ (ψ y) = y := by
    have h := hφan.hasStrictDerivAt.eventually_right_inverse hderiv0ne
    rwa [hφ0] at h
  have hψ0 : ψ 0 = z₀ := by
    have h : ψ (φ z₀) = z₀ := by
      rw [hψdef]
      exact HasStrictFDerivAt.localInverse_apply_image _
    rwa [hφ0] at h
  have hψcont : ContinuousAt ψ (φ z₀) := by
    have hd := hφan.hasStrictDerivAt.to_localInverse hderiv0ne
    rw [hψdef]
    exact hd.hasDerivAt.continuousAt
  have hψcont0 : ContinuousAt ψ 0 := by rwa [hφ0] at hψcont
  -- Choose the radius `r` so that all three local facts hold on `ball z₀ r`.
  obtain ⟨rl, hrl, hrl_ball⟩ := Metric.mem_nhds_iff.mp hψleft
  have hrl_ball' : ∀ z : ℂ, ‖z - z₀‖ < rl → ψ (φ z) = z := fun z hz =>
    hrl_ball (by rwa [Metric.mem_ball, dist_eq_norm])
  obtain ⟨ra, hra, hra_ball⟩ := Metric.mem_nhds_iff.mp hφan.eventually_analyticAt
  have hra_ball' : ∀ z : ℂ, ‖z - z₀‖ < ra → AnalyticAt ℂ φ z := fun z hz =>
    hra_ball (by rwa [Metric.mem_ball, dist_eq_norm])
  set r : ℝ := min (min ran rl) ra with hrdef
  have hr : 0 < r := lt_min (lt_min hran hrl) hra
  have hle_ran : r ≤ ran := le_trans (min_le_left (min ran rl) ra) (min_le_left ran rl)
  have hle_rl : r ≤ rl := le_trans (min_le_left (min ran rl) ra) (min_le_right ran rl)
  have hle_ra : r ≤ ra := min_le_right (min ran rl) ra
  have hgt : ∀ z : ℂ, ‖z - z₀‖ < r → g z = φ z ^ N := fun z hz =>
    hran_ball' z (lt_of_lt_of_le hz hle_ran)
  have hleftr : ∀ z : ℂ, ‖z - z₀‖ < r → ψ (φ z) = z := fun z hz =>
    hrl_ball' z (lt_of_lt_of_le hz hle_rl)
  have hanr : ∀ z : ℂ, ‖z - z₀‖ < r → AnalyticAt ℂ φ z := fun z hz =>
    hra_ball' z (lt_of_lt_of_le hz hle_ra)
  -- Choose `μ` so that, for `‖y‖ < μ`, the right inverse, the size bound and the analyticity
  -- of `ψ` all hold.
  have hex : ∀ᶠ y in 𝓝 (0 : ℂ),
      φ (ψ y) = y ∧ ‖ψ y - z₀‖ < r ∧ AnalyticAt ℂ ψ y := by
    have h1 : ∀ᶠ y in 𝓝 (0 : ℂ), φ (ψ y) = y := hψright
    have h2 : ∀ᶠ y in 𝓝 (0 : ℂ), ‖ψ y - z₀‖ < r := by
      have ht : Metric.ball z₀ r ∈ 𝓝 (ψ 0) := by
        rw [hψ0]; exact Metric.ball_mem_nhds z₀ hr
      filter_upwards [hψcont0.preimage_mem_nhds ht] with y hy
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    have h3 : ∀ᶠ y in 𝓝 (0 : ℂ), AnalyticAt ℂ ψ y := hψana0.eventually_analyticAt
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    exact ⟨hy1, hy2, hy3⟩
  obtain ⟨μ, hμ, hμ_ball⟩ := Metric.mem_nhds_iff.mp hex
  have hμ_ball' : ∀ y : ℂ, ‖y‖ < μ →
      φ (ψ y) = y ∧ ‖ψ y - z₀‖ < r ∧ AnalyticAt ℂ ψ y := fun y hy =>
    hμ_ball (by rwa [Metric.mem_ball, dist_eq_norm, sub_zero])
  refine ⟨r, μ ^ N, hr, pow_pos hμ N, ?_, ?_⟩
  · -- Counting, by transporting the `N`-th roots of `ε` through `ψ`.
    intro ε hε0 hεδ
    have hεne : ε ≠ 0 := norm_pos_iff.mp hε0
    have hTcard : (Polynomial.nthRootsFinset N ε).card = N :=
      Work.WilE3.Lib.card_nthRootsFinset_complex hN0 ε hεne
    have hmem : ∀ w : ℂ, w ∈ Polynomial.nthRootsFinset N ε ↔ w ^ N = ε := fun w =>
      Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hN0) ε
    have hwsmall : ∀ w ∈ Polynomial.nthRootsFinset N ε, ‖w‖ < μ := by
      intro w hw
      have hwN : w ^ N = ε := (hmem w).mp hw
      have hn : ‖w‖ ^ N = ‖ε‖ := by rw [← norm_pow, hwN]
      exact (pow_lt_pow_iff_left₀ (norm_nonneg w) hμ.le hN0).mp (by rw [hn]; exact hεδ)
    have hinj : Set.InjOn ψ ↑(Polynomial.nthRootsFinset N ε) := by
      intro w hw w' hw' h
      have h1 := (hμ_ball' w (hwsmall w hw)).1
      have h2 := (hμ_ball' w' (hwsmall w' hw')).1
      rw [← h1, h, h2]
    refine ⟨(Polynomial.nthRootsFinset N ε).image ψ, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn hinj, hTcard]
    · intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨hφw, hψwr, _⟩ := hμ_ball' w (hwsmall w hw)
      have hgz : g (ψ w) = ε := by rw [hgt (ψ w) hψwr, hφw, (hmem w).mp hw]
      exact ⟨hgz, hψwr,
        deriv_ne_zero_of_simple_solution hN0 hμ hgt hleftr hanr
          (fun y hy => (hμ_ball' y hy).2.2) hψwr hgz hεne hεδ⟩
    · intro z hgz hzr
      refine Finset.mem_image.mpr ⟨φ z, (hmem (φ z)).mpr ?_, hleftr z hzr⟩
      rw [← hgt z hzr]; exact hgz
  · -- Convergence: for small `ε` every solution in the disc is `ψ` of a small root.
    intro η hη
    have hmemη : {y : ℂ | ‖ψ y - z₀‖ < η} ∈ 𝓝 (0 : ℂ) := by
      have ht : Metric.ball z₀ η ∈ 𝓝 (ψ 0) := by
        rw [hψ0]; exact Metric.ball_mem_nhds z₀ hη
      filter_upwards [hψcont0.preimage_mem_nhds ht] with y hy
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    obtain ⟨μ', hμ', hμ'_ball⟩ := Metric.mem_nhds_iff.mp hmemη
    have hμ'_ball' : ∀ y : ℂ, ‖y‖ < μ' → ‖ψ y - z₀‖ < η := fun y hy =>
      hμ'_ball (by rwa [Metric.mem_ball, dist_eq_norm, sub_zero])
    have hmain : ∀ᶠ ε in 𝓝 (0 : ℂ),
        ∀ z : ℂ, g z = ε → ‖z - z₀‖ < r → ‖z - z₀‖ < η := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (pow_pos hμ' N)] with ε hε
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hε
      intro z hgz hzr
      have hφzN : φ z ^ N = ε := by rw [← hgt z hzr]; exact hgz
      have hn : ‖φ z‖ ^ N = ‖ε‖ := by rw [← norm_pow, hφzN]
      have hsmall : ‖φ z‖ < μ' :=
        (pow_lt_pow_iff_left₀ (norm_nonneg _) hμ'.le hN0).mp (by rw [hn]; exact hε)
      rw [← hleftr z hzr]
      exact hμ'_ball' (φ z) hsmall
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hmain

end Work.WilE3.Frame
