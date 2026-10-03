import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Basic
import Submission.Work.Pert.small_of_nearOn

namespace Work.Pert

open Complex Metric Filter Set

open scoped Topology

/-! ## `u` is close to `(f₀ - id)/z²` once `f` is `C⁰`-close to `f₀`

Let `f₀` be a parabolic germ on `D₀` (`f₀ z = z + z² + O(z³)`) and let `f` be within `δ₀` of
`f₀` in sup norm on a compact `L ⊇ closedBall 0 ρ`, with `f 0 = 0`.  Suppose `f` is written in
the normal form `f z = z + z (z - σ) u z` on `ball 0 ρ`, with `u` holomorphic and
`1/2 ≤ ‖u z‖ ≤ 2`.  Then `u` is uniformly close to the model cofactor
`z ↦ (f₀ z - z)/z²` on `ball 0 ρ∖{0}`, with an error controlled by `δ₀/ρ²`.

The proof is a two-step Schwarz argument.  With `h = f - f₀` one has `h 0 = 0` and
`‖h‖ ≤ δ₀` on the ball, so the Schwarz lemma gives `‖h z‖ ≤ (δ₀/ρ) ‖z‖`; Cauchy's estimate for
`h'(0)` gives `‖σ‖ ‖u 0‖ = ‖h'(0)‖ ≤ δ₀/ρ`, hence `‖σ‖ ≤ 2 δ₀/ρ`.  The key identity is

  `G z := h z + σ z u z = z² (u z - (f₀ z - z)/z²)`,

and `G 0 = G'(0) = 0` (because `f'(0) = 1 - σ u 0`), so the *second* order Schwarz lemma
(`Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO` with `n = 1`) applied to `G` on the
ball of radius `ρ` gives `‖G z‖ ≤ K ‖z‖²/ρ` with `K ≤ 5 δ₀/ρ`.  Dividing by `‖z‖²` yields the
claim.  Note that no compactness of `L` is used: only `closedBall 0 ρ ⊆ L ⊆ D₀`. -/

theorem u_close_of_nearOn {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀)
    {ρ : ℝ} (hρ : 0 < ρ) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df L : Set ℂ) (u : ℂ → ℂ) (σ : ℂ),
        IsCompact L → Metric.closedBall 0 ρ ⊆ L → L ⊆ D₀ →
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 →
        DifferentiableOn ℂ u (Metric.ball 0 ρ) →
        (∀ z ∈ Metric.ball 0 ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 ρ, f z = z + z * (z - σ) * u z) →
        ∀ z ∈ Metric.ball 0 ρ, z ≠ 0 → ‖u z - (f₀ z - z) / z ^ 2‖ < η := by
  refine ⟨η * ρ ^ 2 / 10, by positivity, ?_⟩
  intro f Df L u σ _hLc hblL hLD0 hnear hf0 hudiff hubnd hform
  obtain ⟨hDfopen, hLDf, hfdiff, hclose⟩ := hnear
  obtain ⟨hD0open, h0D0, hf0diff, hf00, hdf0, _hdd2⟩ := hd
  set δ : ℝ := η * ρ ^ 2 / 10 with hδdef
  have hballDf : Metric.ball (0 : ℂ) ρ ⊆ Df :=
    fun z hz => hLDf (hblL (Metric.ball_subset_closedBall hz))
  have hballD0 : Metric.ball (0 : ℂ) ρ ⊆ D₀ :=
    fun z hz => hLD0 (hblL (Metric.ball_subset_closedBall hz))
  have h0ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have h0Df : (0 : ℂ) ∈ Df := hballDf h0ball
  have h0D0 : (0 : ℂ) ∈ D₀ := hballD0 h0ball
  have hu_at0 : DifferentiableAt ℂ u 0 :=
    hudiff.differentiableAt (Metric.isOpen_ball.mem_nhds h0ball)
  -- ## the difference `h = f - f₀`
  set h : ℂ → ℂ := fun z => f z - f₀ z with hhdef
  have hh0 : h 0 = 0 := by simp [hhdef, hf0, hf00]
  have hhdiff : DifferentiableOn ℂ h (Metric.ball (0 : ℂ) ρ) := by
    rw [hhdef]
    exact (hfdiff.mono hballDf).sub (hf0diff.mono hballD0)
  have hhmap : Set.MapsTo h (Metric.ball (0 : ℂ) ρ) (Metric.closedBall (h 0) δ) := by
    intro z hz
    rw [hh0, Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (hclose z (hblL (Metric.ball_subset_closedBall hz)))
  -- ## Schwarz, first order
  have hh_schwarz : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖h z‖ ≤ δ / ρ * ‖z‖ := by
    intro z hz
    have hh := Complex.dist_le_div_mul_dist_of_mapsTo_ball (c := (0 : ℂ)) (R₁ := ρ) (R₂ := δ)
      hhdiff hhmap hz
    rwa [hh0, dist_zero_right, dist_zero_right] at hh
  -- ## the derivatives at `0`
  have hderiv_model : deriv (fun z : ℂ => z + z * (z - σ) * u z) 0 = 1 - σ * u 0 := by
    change deriv ((fun z : ℂ => z) + fun z : ℂ => z * (z - σ) * u z) 0 = 1 - σ * u 0
    have h1 : HasDerivAt (fun z : ℂ => z) (1 : ℂ) 0 := hasDerivAt_id 0
    have h2 : HasDerivAt (fun z : ℂ => z - σ) (1 : ℂ) 0 := h1.sub_const σ
    have h3 : HasDerivAt (fun z : ℂ => z * (z - σ)) ((1 : ℂ) * (0 - σ) + 0 * 1) 0 := h1.mul h2
    have h4 : HasDerivAt (fun z : ℂ => z * (z - σ) * u z)
        (((1 : ℂ) * (0 - σ) + 0 * 1) * u 0 + (0 * (0 - σ)) * deriv u 0) 0 :=
      h3.mul hu_at0.hasDerivAt
    have h5 := h1.add h4
    rw [h5.deriv]
    ring
  have hfeq : f =ᶠ[𝓝 (0 : ℂ)] (fun z : ℂ => z + z * (z - σ) * u z) :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds h0ball) hform
  have hderivf : deriv f 0 = 1 - σ * u 0 := by
    rw [Filter.EventuallyEq.deriv_eq hfeq, hderiv_model]
  have hderivh : deriv h 0 = -σ * u 0 := by
    have hdf_at : DifferentiableAt ℂ f 0 := hfdiff.differentiableAt (hDfopen.mem_nhds h0Df)
    have hdf0_at : DifferentiableAt ℂ f₀ 0 := hf0diff.differentiableAt (hD0open.mem_nhds h0D0)
    rw [hhdef]
    change deriv (f - f₀) 0 = -σ * u 0
    rw [deriv_sub hdf_at hdf0_at, hderivf, hdf0]
    ring
  -- ## the second fixed point `σ` is small
  have hσbd : ‖σ‖ ≤ 2 * (δ / ρ) := by
    have hschw := Complex.norm_deriv_le_div_of_mapsTo_ball (c := (0 : ℂ)) (R₁ := ρ) (R₂ := δ)
      hhdiff hhmap hρ
    have hu0 : (1 : ℝ) / 2 ≤ ‖u 0‖ := (hubnd 0 h0ball).1
    have hprod : (1 / 2 : ℝ) * ‖σ‖ ≤ ‖σ‖ * ‖u 0‖ := by
      have hh := mul_le_mul_of_nonneg_right hu0 (norm_nonneg σ)
      rwa [mul_comm ‖u 0‖ ‖σ‖] at hh
    have hmid : ‖σ‖ * ‖u 0‖ = ‖deriv h 0‖ := by rw [hderivh, norm_mul, norm_neg]
    rw [hmid] at hprod
    linarith
  set K : ℝ := δ / ρ + 2 * ‖σ‖ with hKdef
  have hK : K ≤ 5 * (δ / ρ) := by rw [hKdef]; linarith [hσbd]
  have hKpos : 0 ≤ K := by rw [hKdef]; positivity
  -- ## the second-order function `G z = h z + σ z u z`
  set G : ℂ → ℂ := fun z => h z + σ * z * u z with hGdef
  have hG0 : G 0 = 0 := by simp [hGdef, hh0]
  have hsu_at0 : DifferentiableAt ℂ (fun z : ℂ => σ * z * u z) 0 :=
    ((differentiableAt_const σ).mul differentiableAt_id).mul hu_at0
  have hderivsu : deriv (fun z : ℂ => σ * z * u z) 0 = σ * u 0 := by
    change deriv ((fun z : ℂ => σ * z) * u) 0 = σ * u 0
    have hs : HasDerivAt (fun z : ℂ => σ * z) σ 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul σ
    have hh := hs.mul hu_at0.hasDerivAt
    rw [hh.deriv]
    ring
  have hderivG0 : deriv G 0 = 0 := by
    have hh_at0 : DifferentiableAt ℂ h 0 :=
      hhdiff.differentiableAt (Metric.isOpen_ball.mem_nhds h0ball)
    rw [hGdef]
    change deriv (h + fun z : ℂ => σ * z * u z) 0 = 0
    rw [deriv_add hh_at0 hsu_at0, hderivh, hderivsu]
    ring
  have hGdiff : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) ρ) := by
    rw [hGdef]
    exact hhdiff.add ((differentiableOn_id.const_mul σ).mul hudiff)
  have hGmap : Set.MapsTo G (Metric.ball (0 : ℂ) ρ) (Metric.closedBall (G 0) (K * ρ)) := by
    intro z hz
    rw [hG0, Metric.mem_closedBall, dist_zero_right]
    have hzlt : ‖z‖ < ρ := by rwa [Metric.mem_ball, dist_zero_right] at hz
    have h1 : ‖G z‖ ≤ K * ‖z‖ := by
      rw [hGdef]
      have h2 : ‖h z + σ * z * u z‖ ≤ ‖h z‖ + ‖σ * z * u z‖ := norm_add_le _ _
      have h3 : ‖h z‖ ≤ δ / ρ * ‖z‖ := hh_schwarz z hz
      have h4 : ‖σ * z * u z‖ ≤ 2 * ‖σ‖ * ‖z‖ := by
        rw [norm_mul, norm_mul]
        have h5 : ‖u z‖ ≤ 2 := (hubnd z hz).2
        calc ‖σ‖ * ‖z‖ * ‖u z‖ ≤ ‖σ‖ * ‖z‖ * 2 :=
              mul_le_mul_of_nonneg_left h5 (by positivity)
          _ = 2 * ‖σ‖ * ‖z‖ := by ring
      rw [hKdef]
      linarith
    calc ‖G z‖ ≤ K * ‖z‖ := h1
      _ ≤ K * ρ := mul_le_mul_of_nonneg_left hzlt.le hKpos
  have hG_lit : (fun w : ℂ => G w - G 0) =o[𝓝 (0 : ℂ)] (fun w : ℂ => ‖w - 0‖ ^ 1) := by
    have hH : HasDerivAt G 0 0 := by
      have hh := hGdiff.differentiableAt (Metric.isOpen_ball.mem_nhds h0ball)
      simpa [hderivG0] using hh.hasDerivAt
    have h2 := hasDerivAt_iff_isLittleO_nhds_zero.mp hH
    simp only [smul_zero, sub_zero, zero_add] at h2
    have h3 := h2.norm_right
    simpa using h3
  -- ## Schwarz, second order, applied to `G`
  have hG_bound : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖G z‖ ≤ K * ‖z‖ ^ 2 / ρ := by
    intro z hz
    have hh := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (c := (0 : ℂ)) (R₁ := ρ)
      (R₂ := K * ρ) (n := 1) hGdiff hGmap hG_lit hz
    rw [dist_eq_norm, dist_eq_norm, hG0, sub_zero, sub_zero] at hh
    calc ‖G z‖ ≤ (K * ρ) * (‖z‖ / ρ) ^ 2 := hh
      _ = K * ‖z‖ ^ 2 / ρ := by field_simp
  have hfin : 5 * δ / ρ ^ 2 = η / 2 := by rw [hδdef]; field_simp; ring
  -- ## conclusion
  intro z hz hz0
  have hzsq : (0 : ℝ) < ‖z‖ ^ 2 := by positivity
  have hkey : u z - (f₀ z - z) / z ^ 2 = G z / z ^ 2 := by
    have hGval : G z = f z - f₀ z + σ * z * u z := by simp [hGdef, hhdef]
    rw [hGval, hform z hz]
    field_simp
    ring
  have hlast : ‖G z‖ / ‖z‖ ^ 2 ≤ 5 * δ / ρ ^ 2 := by
    have h1 := hG_bound z hz
    have h2 : ‖G z‖ / ‖z‖ ^ 2 ≤ (K * ‖z‖ ^ 2 / ρ) / ‖z‖ ^ 2 :=
      div_le_div_of_nonneg_right h1 hzsq.le
    have h3 : (K * ‖z‖ ^ 2 / ρ) / ‖z‖ ^ 2 = K / ρ := by field_simp
    rw [h3] at h2
    have h4 : K / ρ ≤ 5 * δ / ρ ^ 2 := by
      have h5 : (5 * (δ / ρ)) / ρ = 5 * δ / ρ ^ 2 := by field_simp
      rw [← h5, div_le_div_iff_of_pos_right hρ]
      exact hK
    linarith
  calc ‖u z - (f₀ z - z) / z ^ 2‖ = ‖G z‖ / ‖z‖ ^ 2 := by rw [hkey, norm_div, norm_pow]
    _ ≤ 5 * δ / ρ ^ 2 := hlast
    _ = η / 2 := hfin
    _ < η := by linarith [hη]

end Work.Pert
