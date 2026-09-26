import Mathlib

namespace Work.Smooth.SphereJordan

open Filter Set Metric

/-- **Persistence of zeros.** If `g` is holomorphic on a neighbourhood of the closed ball
`closedBall z₀ ρ`, vanishes at its centre, does not vanish on the sphere `sphere z₀ ρ`, and
`G n → g` uniformly on `closedBall z₀ ρ`, then `G n` has a zero in `ball z₀ ρ` for all large `n`.

This is the `2πi`-free half of Hurwitz's theorem (equivalently of Rouché's theorem): instead of
counting zeros with the argument principle we run the maximum modulus principle on `1 / G n`. -/
theorem exists_zero_of_tendstoUniformlyOn {g : ℂ → ℂ} {G : ℕ → ℂ → ℂ} {z₀ : ℂ} {ρ ρ' : ℝ}
    (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hg : DifferentiableOn ℂ g (ball z₀ ρ'))
    (hG : ∀ n, DifferentiableOn ℂ (G n) (ball z₀ ρ'))
    (hg0 : g z₀ = 0)
    (hgnz : ∀ z, z ∈ sphere z₀ ρ → g z ≠ 0)
    (hconv : TendstoUniformlyOn G g atTop (closedBall z₀ ρ)) :
    ∃ N, ∀ n ≥ N, ∃ z ∈ ball z₀ ρ, G n z = 0 := by
  have hsub : sphere z₀ ρ ⊆ ball z₀ ρ' := by
    intro z hz
    rw [mem_ball, mem_sphere] at *
    rw [hz]; exact hρρ'
  have hcont : ContinuousOn (fun z => ‖g z‖) (sphere z₀ ρ) :=
    Continuous.comp_continuousOn continuous_norm (hg.continuousOn.mono hsub)
  have hne : (sphere z₀ ρ).Nonempty :=
    ⟨z₀ + ρ, by rw [mem_sphere, dist_eq_norm]; simp [abs_of_pos hρ]⟩
  obtain ⟨zmin, hzmin, hmin⟩ := (isCompact_sphere z₀ ρ).exists_isMinOn hne hcont
  have hmpos : 0 < ‖g zmin‖ := norm_pos_iff.mpr (hgnz zmin hzmin)
  have hbound : ∀ z ∈ sphere z₀ ρ, ‖g zmin‖ ≤ ‖g z‖ := fun z hz => hmin hz
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hconv) (‖g zmin‖ / 2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  by_contra hno
  push Not at hno
  have hz0ball : z₀ ∈ ball z₀ ρ := by rw [mem_ball, dist_self]; exact hρ
  have hz0cl : z₀ ∈ closedBall z₀ ρ := mem_closedBall.mpr (by rw [dist_self]; exact hρ.le)
  -- `G n` does not vanish on the closed ball
  have hnonzero : ∀ z ∈ closedBall z₀ ρ, G n z ≠ 0 := by
    intro z hz
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hlt | heq
    · exact hno z (mem_ball.mpr hlt)
    · have hsp : z ∈ sphere z₀ ρ := mem_sphere.mpr heq
      intro hzero
      have hd2 : dist (g z) (G n z) < ‖g zmin‖ / 2 := hN n hn z hz
      have hd2' : dist (g z) 0 < ‖g zmin‖ / 2 := by rwa [hzero] at hd2
      have hgz_lt : ‖g z‖ < ‖g zmin‖ / 2 := by
        rw [dist_eq_norm, sub_zero] at hd2'; exact hd2'
      have hbz : ‖g zmin‖ ≤ ‖g z‖ := hbound z hsp
      linarith
  have hdiff : DifferentiableOn ℂ (fun z => (G n z)⁻¹) (ball z₀ ρ) :=
    ((hG n).mono (ball_subset_ball hρρ'.le)).inv (fun z hz => hno z hz)
  have hcont_closed : ContinuousOn (fun z => (G n z)⁻¹) (closedBall z₀ ρ) :=
    ContinuousOn.inv₀
      (((hG n).mono (fun z hz =>
        mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hρρ'))).continuousOn) hnonzero
  have hdc : DiffContOnCl ℂ (fun z => (G n z)⁻¹) (ball z₀ ρ) :=
    ⟨hdiff, by rw [closure_ball z₀ hρ.ne']; exact hcont_closed⟩
  have hle_sphere : ∀ z ∈ frontier (ball z₀ ρ), ‖(G n z)⁻¹‖ ≤ 2 / ‖g zmin‖ := by
    intro z hz
    rw [frontier_ball z₀ hρ.ne'] at hz
    have hsp : z ∈ sphere z₀ ρ := hz
    have hzcl : z ∈ closedBall z₀ ρ := mem_closedBall.mpr (le_of_eq (mem_sphere.mp hz))
    rw [norm_inv]
    have hd2 : dist (g z) (G n z) < ‖g zmin‖ / 2 := hN n hn z hzcl
    have habs : |‖g z‖ - ‖G n z‖| ≤ dist (g z) (G n z) := by
      rw [dist_eq_norm]; exact abs_norm_sub_norm_le _ _
    have hlt2 : ‖g z‖ - ‖G n z‖ ≤ dist (g z) (G n z) := le_trans (le_abs_self _) habs
    have hbz : ‖g zmin‖ ≤ ‖g z‖ := hbound z hsp
    have hge : ‖g zmin‖ / 2 ≤ ‖G n z‖ := by linarith
    have hpos : 0 < ‖G n z‖ := lt_of_lt_of_le (by positivity) hge
    have hfin : ‖G n z‖⁻¹ ≤ (‖g zmin‖ / 2)⁻¹ :=
      (inv_le_inv₀ hpos (by positivity : (0 : ℝ) < ‖g zmin‖ / 2)).mpr hge
    simpa [inv_div] using hfin
  have hmax : ‖(G n z₀)⁻¹‖ ≤ 2 / ‖g zmin‖ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_ball : Bornology.IsBounded (ball z₀ ρ)) hdc hle_sphere (subset_closure hz0ball)
  rw [norm_inv] at hmax
  have hGz0pos : 0 < ‖G n z₀‖ := norm_pos_iff.mpr (hno z₀ hz0ball)
  have hmax' : ‖G n z₀‖⁻¹ ≤ (‖g zmin‖ / 2)⁻¹ := by rw [inv_div]; exact hmax
  have hge2 : ‖g zmin‖ / 2 ≤ ‖G n z₀‖ :=
    (inv_le_inv₀ hGz0pos (by positivity : (0 : ℝ) < ‖g zmin‖ / 2)).mp hmax'
  have hlt3 : ‖G n z₀‖ < ‖g zmin‖ / 2 := by
    have := hN n hn z₀ hz0cl
    simpa [hg0, dist_eq_norm] using this
  linarith

/-- **Isolated zeros.** Let `g` be analytic on an open preconnected set `U`, with `g a = 0` and `g`
not identically zero on `U`. Then `g` is non-zero on a punctured ball around `a` (and that ball can
be chosen inside `U`). -/
theorem exists_ball_eventually_ne {U : Set ℂ} (hUo : IsOpen U) (hUp : IsPreconnected U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) {a : ℂ} (ha : a ∈ U) (_hga : g a = 0)
    (hne : ∃ z ∈ U, g z ≠ 0) :
    ∃ ρ > 0, ball a ρ ⊆ U ∧ ∀ z, dist z a < ρ → z ≠ a → g z ≠ 0 := by
  rcases (hg a ha).eventually_eq_zero_or_eventually_ne_zero with h0 | hne'
  · exfalso
    obtain ⟨z, hz, hgz⟩ := hne
    exact hgz (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUp ha h0 hz)
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne'
    obtain ⟨ε, hεpos, hε⟩ := hne'
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hUo a ha
    refine ⟨min ε δ / 2, by positivity, ?_, ?_⟩
    · intro z hz
      exact hδsub (ball_subset_ball (by linarith [min_le_right ε δ] : min ε δ / 2 ≤ δ) hz)
    · intro z hz hzne
      exact hε (by linarith [hz, min_le_left ε δ, hεpos] : dist z a < ε) (by simpa using hzne)

/-- **Hurwitz's theorem.** A locally uniform limit of injective holomorphic functions on an open
preconnected subset of `ℂ` is itself injective, unless it is constant. -/
theorem hurwitz {U : Set ℂ} (hUo : IsOpen U) (hUp : IsPreconnected U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hf : DifferentiableOn ℂ f U)
    (hinj : ∀ n, Set.InjOn (F n) U) (hconv : TendstoLocallyUniformlyOn F f Filter.atTop U) :
    Set.InjOn f U ∨ ∃ c : ℂ, ∀ z ∈ U, f z = c := by
  by_cases hconst : ∃ c : ℂ, ∀ z ∈ U, f z = c
  · exact Or.inr hconst
  push Not at hconst
  left
  intro a ha b hb hab
  by_contra habne
  -- Work with `g = f - f a` and `G n = F n - f a`; note `f b = f a`.
  set w : ℂ := f a with hw
  have hwa : f a = w := hw.symm
  have hwb : f b = w := by rw [hw]; exact hab.symm
  set g : ℂ → ℂ := fun z => f z - w with hgdef
  set G : ℕ → ℂ → ℂ := fun n z => F n z - w with hGdef
  have hg_diff : DifferentiableOn ℂ g U := by rw [hgdef]; exact hf.sub_const w
  have hGdiff : ∀ n, DifferentiableOn ℂ (G n) U := by
    intro n; rw [hGdef]; exact (hF n).sub_const w
  have hg_an : AnalyticOnNhd ℂ g U := hg_diff.analyticOnNhd hUo
  have hga : g a = 0 := by rw [hgdef]; simp [hwa]
  have hgb : g b = 0 := by rw [hgdef]; simp [hwb]
  have hg_ne : ∃ z ∈ U, g z ≠ 0 := by
    obtain ⟨z, hz, hz'⟩ := hconst w
    exact ⟨z, hz, by rw [hgdef]; exact sub_ne_zero.mpr hz'⟩
  obtain ⟨ρa, _hρapos, hρasub, hρanz⟩ := exists_ball_eventually_ne hUo hUp hg_an ha hga hg_ne
  obtain ⟨ρb, _hρbpos, hρbsub, hρbnz⟩ := exists_ball_eventually_ne hUo hUp hg_an hb hgb hg_ne
  set d : ℝ := dist a b with hddef
  have hdpos : 0 < d := by rw [hddef]; exact dist_pos.mpr habne
  set ra : ℝ := min (ρa / 2) (d / 4) with radef
  set rb : ℝ := min (ρb / 2) (d / 4) with rbdef
  have hrapos : 0 < ra := by rw [radef]; positivity
  have hrbpos : 0 < rb := by rw [rbdef]; positivity
  have hra_lt_ρa : ra < ρa := by
    have h1 : ra ≤ ρa / 2 := by rw [radef]; exact min_le_left _ _
    linarith
  have hrb_lt_ρb : rb < ρb := by
    have h1 : rb ≤ ρb / 2 := by rw [rbdef]; exact min_le_left _ _
    linarith
  have hra_le : ra ≤ d / 4 := by rw [radef]; exact min_le_right _ _
  have hrb_le : rb ≤ d / 4 := by rw [rbdef]; exact min_le_right _ _
  -- uniform convergence of `G` to `g` on any closed ball contained in `U`
  have hconvG : ∀ (c : ℂ) (r : ℝ), closedBall c r ⊆ U →
      TendstoUniformlyOn G g Filter.atTop (closedBall c r) := by
    intro c r hcU
    have hFconv : TendstoUniformlyOn F f Filter.atTop (closedBall c r) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hUo).mp hconv _ hcU (isCompact_closedBall c r)
    rw [Metric.tendstoUniformlyOn_iff] at hFconv ⊢
    intro ε hε
    filter_upwards [hFconv ε hε] with n hn z hz
    simpa only [hgdef, hGdef, dist_eq_norm, sub_sub_sub_cancel_right] using hn z hz
  have hKsub_a : closedBall a ra ⊆ U := fun z hz =>
    hρasub (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hra_lt_ρa))
  have hKsub_b : closedBall b rb ⊆ U := fun z hz =>
    hρbsub (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hrb_lt_ρb))
  have hgnz_a : ∀ z ∈ sphere a ra, g z ≠ 0 := by
    intro z hz
    rw [mem_sphere] at hz
    exact hρanz z (by rw [hz]; exact hra_lt_ρa)
      (by rintro rfl; rw [dist_self] at hz; linarith)
  have hgnz_b : ∀ z ∈ sphere b rb, g z ≠ 0 := by
    intro z hz
    rw [mem_sphere] at hz
    exact hρbnz z (by rw [hz]; exact hrb_lt_ρb)
      (by rintro rfl; rw [dist_self] at hz; linarith)
  obtain ⟨Na, hNa⟩ := exists_zero_of_tendstoUniformlyOn hrapos hra_lt_ρa
    (hg_diff.mono hρasub) (fun n => (hGdiff n).mono hρasub) hga hgnz_a (hconvG a ra hKsub_a)
  obtain ⟨Nb, hNb⟩ := exists_zero_of_tendstoUniformlyOn hrbpos hrb_lt_ρb
    (hg_diff.mono hρbsub) (fun n => (hGdiff n).mono hρbsub) hgb hgnz_b (hconvG b rb hKsub_b)
  obtain ⟨z, hzball, hzG⟩ := hNa (max Na Nb) (le_max_left _ _)
  obtain ⟨y, hyball, hyG⟩ := hNb (max Na Nb) (le_max_right _ _)
  have hzu : z ∈ U := hρasub (ball_subset_ball hra_lt_ρa.le hzball)
  have hyu : y ∈ U := hρbsub (ball_subset_ball hrb_lt_ρb.le hyball)
  have hFz : F (max Na Nb) z = w := by
    rw [hGdef] at hzG; exact sub_eq_zero.mp hzG
  have hFy : F (max Na Nb) y = w := by
    rw [hGdef] at hyG; exact sub_eq_zero.mp hyG
  -- the two balls are disjoint, so `z ≠ y`, contradicting injectivity of `F (max Na Nb)`
  have hzy : z ≠ y := by
    intro hzyeq
    have h1 : dist z a < ra := mem_ball.mp hzball
    have h2 : dist y b < rb := mem_ball.mp hyball
    have hda : dist a z = dist z a := dist_comm a z
    have hzy0 : dist z y = 0 := by rw [hzyeq, dist_self]
    have hmain : d < ra + rb := by
      rw [hddef]
      calc dist a b ≤ dist a z + dist z b := dist_triangle a z b
        _ ≤ dist a z + (dist z y + dist y b) := by gcongr; exact dist_triangle z y b
        _ = dist z a + dist y b := by rw [hda, hzy0, zero_add]
        _ < ra + rb := add_lt_add h1 h2
    have hfin : ra + rb ≤ d / 2 := by linarith
    linarith [hdpos]
  exact hzy (hinj (max Na Nb) hzu hyu (by rw [hFz, hFy]))

end Work.Smooth.SphereJordan
