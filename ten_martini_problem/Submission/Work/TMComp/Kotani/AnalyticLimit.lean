import Mathlib

/-!
# A Vitali-type limit theorem for bounded holomorphic functions

If a sequence of holomorphic functions on a ball is uniformly bounded by `1` and converges
pointwise off the real axis, then it converges locally uniformly to a holomorphic limit.

The proof is elementary: the uniform bound gives (by Cauchy's estimate for the derivative) a
uniform Lipschitz bound on every closed sub-ball; Lipschitz plus pointwise convergence on the
dense set `{z | z.im ≠ 0}` gives a uniformly Cauchy sequence there.  No measure theory is used.
-/

open Filter Metric Topology Set
open scoped Topology

noncomputable section

namespace Work.TMComp.Kotani

/-- Any point of the plane is arbitrarily close to a point off the real axis. -/
theorem exists_offAxis_near (z : ℂ) {η : ℝ} (hη : 0 < η) :
    ∃ y : ℂ, y.im ≠ 0 ∧ ‖y - z‖ < η := by
  by_cases h : z.im = 0
  · refine ⟨z + (η / 2 : ℝ) * Complex.I, ?_, ?_⟩
    · simp [Complex.add_im, h, Complex.mul_im, Complex.I_re, Complex.I_im]
      positivity
    · rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
  · exact ⟨z, h, by simpa using hη⟩

/-- A closed ball of radius `s` around `z₀` is contained in the open ball of radius `r` around
`c` as soon as `‖z₀ - c‖ + s < r`. -/
theorem closedBall_subset_ball' {c z₀ : ℂ} {s r : ℝ} (h : ‖z₀ - c‖ + s < r) :
    Metric.closedBall z₀ s ⊆ Metric.ball c r := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm]
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  calc ‖z - c‖ = ‖(z - z₀) + (z₀ - c)‖ := by ring_nf
    _ ≤ ‖z - z₀‖ + ‖z₀ - c‖ := norm_add_le _ _
    _ < r := by linarith

/-- A holomorphic function bounded by `1` on `ball c r` is Lipschitz on every closed ball
`closedBall z₀ s` with `‖z₀ - c‖ + s < r`. -/
theorem lipschitz_of_bounded {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball c r)) (hb : ∀ z ∈ Metric.ball c r, ‖f z‖ ≤ 1)
    {z₀ : ℂ} {s : ℝ} (hzs : ‖z₀ - c‖ + s < r) :
    ∀ z ∈ Metric.closedBall z₀ s, ∀ w ∈ Metric.closedBall z₀ s,
      ‖f z - f w‖ ≤ (2 / (r - ‖z₀ - c‖ - s)) * ‖z - w‖ := by
  set t : ℝ := r - ‖z₀ - c‖ - s with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  intro z hz w hw
  have hsub : Metric.closedBall z₀ s ⊆ Metric.ball c r := closedBall_subset_ball' hzs
  have hder : ∀ u ∈ Metric.closedBall z₀ s, ‖deriv f u‖ ≤ 2 / t := by
    intro u hu
    have htu : 0 < t / 2 := by linarith
    have hsub' : Metric.closedBall u (t / 2) ⊆ Metric.ball c r := by
      apply closedBall_subset_ball'
      have hu' : ‖u - z₀‖ ≤ s := by
        simpa [dist_eq_norm] using hu
      calc ‖u - c‖ + t / 2 ≤ (‖u - z₀‖ + ‖z₀ - c‖) + t / 2 := by
            have := norm_add_le (u - z₀) (z₀ - c)
            rw [sub_add_sub_cancel] at this
            linarith
        _ ≤ s + ‖z₀ - c‖ + t / 2 := by linarith
        _ < r := by rw [ht]; linarith
    have h1 : Complex.cderiv (t / 2) f u = deriv f u :=
      Complex.cderiv_eq_deriv isOpen_ball hf.differentiableOn htu hsub'
    have h2 : ‖Complex.cderiv (t / 2) f u‖ ≤ 1 / (t / 2) :=
      Complex.norm_cderiv_le (M := 1) htu fun x hx =>
        hb x (hsub' (sphere_subset_closedBall hx))
    rw [← h1]
    calc ‖Complex.cderiv (t / 2) f u‖ ≤ 1 / (t / 2) := h2
      _ = 2 / t := by ring
  have hconv : Convex ℝ (Metric.closedBall z₀ s) := convex_closedBall z₀ s
  have hd : ∀ u ∈ Metric.closedBall z₀ s, DifferentiableAt ℂ f u := fun u hu =>
    (hf u (hsub hu)).differentiableAt
  exact hconv.norm_image_sub_le_of_norm_deriv_le hd hder hw hz

end Work.TMComp.Kotani

namespace Work.TMComp.Kotani

open Filter Metric Topology Set
open scoped Topology

/-- **Vitali-type limit theorem.**  A sequence of holomorphic functions on a ball, uniformly
bounded by `1`, which converges pointwise off the real axis, converges locally uniformly on the
ball to a holomorphic limit which agrees with the pointwise limit off the real axis. -/
theorem exists_analyticOnNhd_of_tendsto_offreal (c : ℂ) (r : ℝ) (hr : 0 < r)
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, AnalyticOnNhd ℂ (F n) (Metric.ball c r))
    (hb : ∀ n z, z ∈ Metric.ball c r → ‖F n z‖ ≤ 1)
    (hg : ∀ z ∈ Metric.ball c r, z.im ≠ 0 → Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.ball c r) ∧
      (∀ z ∈ Metric.ball c r, z.im ≠ 0 → G z = g z) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < r → TendstoUniformlyOn F G atTop (Metric.closedBall c ρ)) ∧
      (∀ z ∈ Metric.ball c r, Tendsto (fun n => F n z) atTop (𝓝 (G z))) := by
  classical
  have hclosed : ∀ ρ : ℝ, ρ < r → Metric.closedBall c ρ ⊆ Metric.ball c r := by
    intro ρ hρ z hz
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    linarith
  -- (A) the sequence is uniformly Cauchy on every compact subset of the ball
  have huc : ∀ K : Set ℂ, K ⊆ Metric.ball c r → IsCompact K → ∀ ε > 0,
      ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ z ∈ K, ‖F n z - F m z‖ ≤ ε := by
    intro K hK hKc ε hε
    by_contra hcon
    push_neg at hcon
    choose n hn m hm z hz hbig using hcon
    obtain ⟨z₁, hz₁K, ψ, hψmono, hψtend⟩ := hKc.tendsto_subseq (x := z) (fun j => hz j)
    have hz₁ball : z₁ ∈ Metric.ball c r := hK hz₁K
    have hz₁c : ‖z₁ - c‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz₁ball
    set t : ℝ := (r - ‖z₁ - c‖) / 2 with htdef
    have ht0 : 0 < t := by rw [htdef]; linarith
    have hzt : ‖z₁ - c‖ + t < r := by rw [htdef]; linarith
    have hrt : r - ‖z₁ - c‖ - t = t := by rw [htdef]; ring
    obtain ⟨y, hyim, hyclose⟩ :=
      exists_offAxis_near z₁ (η := min (t / 4) (ε * t / 64)) (by positivity)
    have hyclose2 : ‖y - z₁‖ < ε * t / 64 := lt_of_lt_of_le hyclose (min_le_right _ _)
    have hyclose3 : ‖y - z₁‖ < t / 4 := lt_of_lt_of_le hyclose (min_le_left _ _)
    have hyball : y ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖y - c‖ = ‖(y - z₁) + (z₁ - c)‖ := by ring_nf
        _ ≤ ‖y - z₁‖ + ‖z₁ - c‖ := norm_add_le _ _
        _ < t + ‖z₁ - c‖ := by linarith
        _ < r := by rw [htdef]; linarith
    have hntend : Tendsto (fun j => n (ψ j)) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b, fun j hj =>
        le_trans hj (le_trans (hψmono.id_le j) (hn (ψ j)))⟩
    have hmtend : Tendsto (fun j => m (ψ j)) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b, fun j hj =>
        le_trans hj (le_trans (hψmono.id_le j) (hm (ψ j)))⟩
    have hby : Tendsto (fun j => ‖F (n (ψ j)) y - F (m (ψ j)) y‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j => F (n (ψ j)) y) atTop (𝓝 (g y)) :=
        (hg y hyball hyim).comp hntend
      have h2 : Tendsto (fun j => F (m (ψ j)) y) atTop (𝓝 (g y)) :=
        (hg y hyball hyim).comp hmtend
      simpa using (h1.sub h2).norm
    have hzy : Tendsto (fun j => ‖z (ψ j) - y‖) atTop (𝓝 ‖z₁ - y‖) :=
      (hψtend.sub tendsto_const_nhds).norm
    have hexpr : Tendsto (fun j => 2 * (2 / t) * ‖z (ψ j) - y‖
        + ‖F (n (ψ j)) y - F (m (ψ j)) y‖) atTop (𝓝 (2 * (2 / t) * ‖z₁ - y‖ + 0)) :=
      (tendsto_const_nhds.mul hzy).add hby
    have hev : ∀ᶠ j in atTop, ε ≤ 2 * (2 / t) * ‖z (ψ j) - y‖
        + ‖F (n (ψ j)) y - F (m (ψ j)) y‖ := by
      have h1 : ∀ᶠ j in atTop, z (ψ j) ∈ Metric.ball z₁ t :=
        hψtend.eventually (Metric.ball_mem_nhds z₁ ht0)
      filter_upwards [h1] with j hj
      have hzy_mem : z (ψ j) ∈ Metric.closedBall z₁ t := Metric.ball_subset_closedBall hj
      have hy_mem : y ∈ Metric.closedBall z₁ t := by
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith
      have hl1 := lipschitz_of_bounded (f := F (n (ψ j))) (hF _) (hb _) hzt
        (z (ψ j)) hzy_mem y hy_mem
      have hl2 := lipschitz_of_bounded (f := F (m (ψ j))) (hF _) (hb _) hzt
        y hy_mem (z (ψ j)) hzy_mem
      rw [hrt] at hl1 hl2
      rw [norm_sub_rev y (z (ψ j))] at hl2
      have h3 := hbig (ψ j)
      have hsplit : F (n (ψ j)) (z (ψ j)) - F (m (ψ j)) (z (ψ j))
          = (F (n (ψ j)) (z (ψ j)) - F (n (ψ j)) y)
            + (F (n (ψ j)) y - F (m (ψ j)) y)
            + (F (m (ψ j)) y - F (m (ψ j)) (z (ψ j))) := by ring
      have h4 : ‖F (n (ψ j)) (z (ψ j)) - F (m (ψ j)) (z (ψ j))‖
          ≤ (2 / t) * ‖z (ψ j) - y‖ + ‖F (n (ψ j)) y - F (m (ψ j)) y‖
            + (2 / t) * ‖z (ψ j) - y‖ := by
        rw [hsplit]
        calc ‖(F (n (ψ j)) (z (ψ j)) - F (n (ψ j)) y) + (F (n (ψ j)) y - F (m (ψ j)) y)
              + (F (m (ψ j)) y - F (m (ψ j)) (z (ψ j)))‖
            ≤ ‖(F (n (ψ j)) (z (ψ j)) - F (n (ψ j)) y) + (F (n (ψ j)) y - F (m (ψ j)) y)‖
              + ‖F (m (ψ j)) y - F (m (ψ j)) (z (ψ j))‖ := norm_add_le _ _
          _ ≤ (‖F (n (ψ j)) (z (ψ j)) - F (n (ψ j)) y‖
                + ‖F (n (ψ j)) y - F (m (ψ j)) y‖)
              + ‖F (m (ψ j)) y - F (m (ψ j)) (z (ψ j))‖ := by
              have := norm_add_le (F (n (ψ j)) (z (ψ j)) - F (n (ψ j)) y)
                (F (n (ψ j)) y - F (m (ψ j)) y)
              linarith
          _ ≤ ((2 / t) * ‖z (ψ j) - y‖ + ‖F (n (ψ j)) y - F (m (ψ j)) y‖)
              + (2 / t) * ‖z (ψ j) - y‖ := by linarith [hl1, hl2]
      have h5 : (2 / t) * ‖z (ψ j) - y‖ + ‖F (n (ψ j)) y - F (m (ψ j)) y‖
          + (2 / t) * ‖z (ψ j) - y‖
          = 2 * (2 / t) * ‖z (ψ j) - y‖ + ‖F (n (ψ j)) y - F (m (ψ j)) y‖ := by ring
      rw [h5] at h4
      exact le_of_lt (lt_of_lt_of_le h3 h4)
    have hge : ε ≤ 2 * (2 / t) * ‖z₁ - y‖ + 0 := ge_of_tendsto hexpr hev
    have hsmall : 2 * (2 / t) * ‖z₁ - y‖ + 0 < ε := by
      have hy : ‖z₁ - y‖ < ε * t / 64 := by rwa [norm_sub_rev] at hyclose2
      have h1 : 2 * (2 / t) * ‖z₁ - y‖ + 0 = (4 / t) * ‖z₁ - y‖ := by ring
      rw [h1]
      calc (4 / t) * ‖z₁ - y‖ < (4 / t) * (ε * t / 64) :=
            mul_lt_mul_of_pos_left hy (by positivity)
        _ = ε / 16 := by field_simp; ring
        _ < ε := by linarith
    exact absurd hge (not_le.mpr hsmall)
  -- (B) pointwise convergence in the whole ball, and the limit function
  have hpt : ∀ z ∈ Metric.ball c r, CauchySeq (fun n => F n z) := by
    intro z hz
    have hzc : ‖z - c‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := huc (Metric.closedBall c ((‖z - c‖ + r) / 2)) (by
        intro w hw
        rw [Metric.mem_ball, dist_eq_norm]
        rw [Metric.mem_closedBall, dist_eq_norm] at hw
        linarith)
      (isCompact_closedBall c ((‖z - c‖ + r) / 2)) (ε / 2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmem : z ∈ Metric.closedBall c ((‖z - c‖ + r) / 2) := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    have := hN n hn m hm z hmem
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  have hex : ∀ z ∈ Metric.ball c r, ∃ L : ℂ, Tendsto (fun n => F n z) atTop (𝓝 L) :=
    fun z hz => cauchySeq_tendsto_of_complete (hpt z hz)
  let G : ℂ → ℂ := fun z => if h : z ∈ Metric.ball c r then Classical.choose (hex z h) else 0
  have hGt : ∀ z ∈ Metric.ball c r, Tendsto (fun n => F n z) atTop (𝓝 (G z)) := by
    intro z hz
    have hGz : G z = Classical.choose (hex z hz) := by
      show (if h : z ∈ Metric.ball c r then Classical.choose (hex z h) else 0) = _
      exact dif_pos hz
    rw [hGz]
    exact Classical.choose_spec (hex z hz)
  -- (C) uniform convergence on compact subsets of the ball
  have hunif : ∀ K : Set ℂ, K ⊆ Metric.ball c r → IsCompact K →
      TendstoUniformlyOn F G atTop K := by
    intro K hK hKc
    rw [tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := huc K hK hKc (ε / 2) (by linarith)
    refine eventually_atTop.mpr ⟨N, fun n hn z hz => ?_⟩
    have htend : Tendsto (fun m => F m z) atTop (𝓝 (G z)) := hGt z (hK hz)
    have hlim : Tendsto (fun m => ‖F n z - F m z‖) atTop (𝓝 ‖F n z - G z‖) := by
      simpa using (tendsto_const_nhds.sub htend).norm
    have hbound : ‖F n z - G z‖ ≤ ε / 2 :=
      le_of_tendsto hlim (eventually_atTop.mpr ⟨N, fun m hm => hN n hn m hm z hz⟩)
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  -- (D) analyticity of the limit
  have hloc : TendstoLocallyUniformlyOn F G atTop (Metric.ball c r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mpr hunif
  have hGan : AnalyticOnNhd ℂ G (Metric.ball c r) := by
    have hd : DifferentiableOn ℂ G (Metric.ball c r) :=
      hloc.differentiableOn (Eventually.of_forall fun n => (hF n).differentiableOn) isOpen_ball
    exact (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hd
  have hGval : ∀ z ∈ Metric.ball c r, z.im ≠ 0 → G z = g z := by
    intro z hz hzim
    exact tendsto_nhds_unique (hGt z hz) (hg z hz hzim)
  refine ⟨G, hGan, hGval, ?_, ?_⟩
  · exact fun ρ hρ hρr => hunif (Metric.closedBall c ρ) (hclosed ρ hρr) (isCompact_closedBall c ρ)
  · intro z hz
    obtain ⟨ρ, hzρ, hρr⟩ : ∃ ρ : ℝ, dist z c < ρ ∧ ρ < r := by
      refine ⟨(dist z c + r) / 2, ?_, ?_⟩ <;> nlinarith [Metric.mem_ball.mp hz]
    have h0 : 0 < ρ := by
      have h1 : 0 ≤ dist z c := dist_nonneg
      linarith
    have hu : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Metric.closedBall c ρ, dist (G x) (F n x) < ε :=
      tendstoUniformlyOn_iff.mp (hunif (Metric.closedBall c ρ) (hclosed ρ hρr)
        (isCompact_closedBall c ρ))
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hu ε hε] with n hn
    simpa [dist_comm] using hn z (by rw [Metric.mem_closedBall]; exact le_of_lt hzρ)

end Work.TMComp.Kotani
