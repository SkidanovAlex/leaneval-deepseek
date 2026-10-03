import Mathlib

/-!
# Two points of a large circle whose images are at least as far apart as `g 1` and `g (-1)`

Let `g : ℂ → ℂ` be a `C¹` map which is injective and whose real derivative is injective at
every point (so `g` is a local diffeomorphism and an open map), and let `r ≥ 1`.  Then there
are points `z₁`, `z₂` of the circle of radius `r` such that

`dist (g 1) (g (-1)) ≤ dist (g z₁) (g z₂)`.

The proof only uses that a local diffeomorphism of `ℂ` is an open map.  For a point `p`, the
maximum of `y ↦ dist p y` over the compact set `K = g '' closedBall 0 r` is attained at some
`g b`.  If `‖b‖ < r`, then `g b` is an interior point of `K` (the image of the open disc of
radius `r` is open because `g` is open), so one may move `g b` a little bit away from `p`
while staying in `K`, contradicting maximality.  Hence `b` lies on the sphere of radius `r`.
Applying this first with `p = g 1` and then with `p = g z₁` yields the claim.
-/

namespace Work.Fatou.Analysis

/-- In finite dimension (here `ℂ` over `ℝ`) an injective continuous linear map `ℂ →L[ℝ] ℂ` is
a continuous linear equivalence. -/
lemma exists_clm_equiv_of_injective (f : ℂ →L[ℝ] ℂ) (hf : Function.Injective f) :
    ∃ e : ℂ ≃L[ℝ] ℂ, (e : ℂ →L[ℝ] ℂ) = f := by
  refine ⟨ContinuousLinearEquiv.ofBijective f ?_ ?_, ?_⟩
  · exact LinearMap.ker_eq_bot.mpr hf
  · exact LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hf)
  · exact ContinuousLinearEquiv.coe_ofBijective f _ _

/-- A `C¹` map `ℂ → ℂ` whose real derivative is injective at every point is an open map. -/
lemma isOpenMap_of_contDiff_one_fderiv_injective (g : ℂ → ℂ) (hC1 : ContDiff ℝ 1 g)
    (hderiv : ∀ z, Function.Injective (fderiv ℝ g z)) : IsOpenMap g := by
  classical
  refine isOpenMap_of_hasStrictFDerivAt_equiv
    (f' := fun z => (exists_clm_equiv_of_injective (fderiv ℝ g z) (hderiv z)).choose) fun z => ?_
  rw [(exists_clm_equiv_of_injective (fderiv ℝ g z) (hderiv z)).choose_spec]
  exact hC1.hasStrictFDerivAt (x := z) (by norm_num)

/-- For `g` as above and any point `p`, the maximum of `dist p (g ·)` over the closed disc of
radius `r ≥ 1` is attained at a point of the *sphere* of radius `r`. -/
lemma exists_sphere_max_dist (g : ℂ → ℂ) (r : ℝ) (hr : 1 ≤ r)
    (hC1 : ContDiff ℝ 1 g) (hinj : Function.Injective g)
    (hderiv : ∀ z, Function.Injective (fderiv ℝ g z)) (p : ℂ) :
    ∃ b ∈ Metric.sphere (0 : ℂ) r,
      ∀ a ∈ Metric.closedBall (0 : ℂ) r, dist p (g a) ≤ dist p (g b) := by
  have hcont : Continuous g := hC1.continuous
  have hgopen : IsOpenMap g := isOpenMap_of_contDiff_one_fderiv_injective g hC1 hderiv
  -- the maximum of `dist p (g ·)` over the closed disc is attained
  obtain ⟨y₀, hy₀K, hy₀max⟩ :=
    IsCompact.exists_isMaxOn ((isCompact_closedBall (0 : ℂ) r).image hcont)
      ⟨g 0, 0, by simp only [Metric.mem_closedBall, dist_self]; linarith, rfl⟩
      (continuous_const.dist continuous_id).continuousOn
  obtain ⟨b₀, hb₀, hgb⟩ := hy₀K
  have hmem : ∀ a ∈ Metric.closedBall (0 : ℂ) r, dist p (g a) ≤ dist p (g b₀) := by
    intro a ha
    have h : dist p (g a) ≤ dist p y₀ := hy₀max ⟨a, ha, rfl⟩
    rwa [← hgb] at h
  have hb₀le : ‖b₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hb₀
  refine ⟨b₀, ?_, hmem⟩
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  by_contra hne'
  have hlt : ‖b₀‖ < r := lt_of_le_of_ne hb₀le hne'
  have hb₁ : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_one]; exact hr
  have hbm₁ : (-1 : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_neg, norm_one]; exact hr
  have hDpos : 0 < dist (g 1) (g (-1)) := by
    rw [dist_pos]
    intro h
    exact (by norm_num : (1 : ℂ) ≠ -1) (hinj h)
  -- the maximum is positive, hence the maximizing point differs from `p`
  have hmaxpos : 0 < dist p (g b₀) := by
    have h1 := hmem 1 hb₁
    have h2 := hmem (-1) hbm₁
    have htri : dist (g 1) (g (-1)) ≤ dist p (g 1) + dist p (g (-1)) := by
      calc dist (g 1) (g (-1)) ≤ dist (g 1) p + dist (g (-1)) p := dist_triangle_right _ _ _
        _ = dist p (g 1) + dist p (g (-1)) := by rw [dist_comm (g 1) p, dist_comm (g (-1)) p]
    linarith
  have hne_p : g b₀ ≠ p := by
    intro h; rw [h, dist_self] at hmaxpos; exact lt_irrefl 0 hmaxpos
  -- `g b₀` is an interior point of the image of the closed disc
  have hgb0ball : g b₀ ∈ g '' Metric.ball (0 : ℂ) r :=
    ⟨b₀, by simpa [Metric.mem_ball, dist_eq_norm] using hlt, rfl⟩
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (Metric.isOpen_iff.mp (hgopen _ Metric.isOpen_ball)) (g b₀) hgb0ball
  -- move `g b₀` a little bit in the direction away from `p`
  set c : ℂ := g b₀ - p with hc
  have hcne : c ≠ 0 := by rw [hc, sub_ne_zero]; exact hne_p
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hcne
  set t : ℝ := δ / (2 * ‖c‖) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htn : t * ‖c‖ = δ / 2 := by
    rw [ht]
    field_simp
  set y : ℂ := g b₀ + t • c with hy
  have hyc : y - p = (1 + t) • c := by
    have h1 : y - p = c + t • c := by rw [hy, hc]; abel
    have h2 : (1 + t) • c = c + t • c := by rw [add_smul, one_smul]
    rw [h1, ← h2]
  -- `y` still belongs to the image of the closed disc
  have hyfin : dist p y ≤ dist p (g b₀) := by
    obtain ⟨a, ha, hay⟩ := hδsub (show y ∈ Metric.ball (g b₀) δ from by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : y - g b₀ = t • c := by rw [hy]; abel
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, htn]
      linarith)
    have h := hmem a (Metric.ball_subset_closedBall ha)
    rwa [hay] at h
  have hylarge : dist p (g b₀) < dist p y := by
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have hyval : ‖y - p‖ = (1 + t) * ‖c‖ := by
      rw [hyc, norm_smul, Real.norm_eq_abs, abs_of_pos h1t]
    have hbval : ‖g b₀ - p‖ = ‖c‖ := by rw [hc]
    rw [dist_comm p (g b₀), dist_comm p y, dist_eq_norm, dist_eq_norm, hyval, hbval]
    nlinarith [hcn, htn, hδpos]
  linarith

theorem exists_sphere_points_far (g : ℂ → ℂ) (r : ℝ) (hr : 1 ≤ r)
    (hC1 : ContDiff ℝ 1 g) (hinj : Function.Injective g)
    (hderiv : ∀ z, Function.Injective (fderiv ℝ g z)) :
    ∃ z₁ ∈ Metric.sphere (0:ℂ) r, ∃ z₂ ∈ Metric.sphere (0:ℂ) r,
      dist (g 1) (g (-1)) ≤ dist (g z₁) (g z₂) := by
  have h1 : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_one]; exact hr
  have hm1 : (-1 : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_neg, norm_one]; exact hr
  obtain ⟨z₁, hz₁, hmax₁⟩ := exists_sphere_max_dist g r hr hC1 hinj hderiv (g 1)
  obtain ⟨z₂, hz₂, hmax₂⟩ := exists_sphere_max_dist g r hr hC1 hinj hderiv (g z₁)
  refine ⟨z₁, hz₁, z₂, hz₂, ?_⟩
  have hA : dist (g 1) (g (-1)) ≤ dist (g 1) (g z₁) := hmax₁ (-1) hm1
  have hB : dist (g z₁) (g 1) ≤ dist (g z₁) (g z₂) := hmax₂ 1 h1
  linarith [dist_comm (g 1) (g z₁)]

end Work.Fatou.Analysis
