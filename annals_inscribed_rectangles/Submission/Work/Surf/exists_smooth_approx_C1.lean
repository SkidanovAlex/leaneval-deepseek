import Mathlib

/-!
# Smooth (C^∞) approximation of a `C^1` map, together with its derivative

For a `C^1` map `F : E → E'` between a finite dimensional real normed space `E` and a complete
real normed space `E'`, a compact set `K ⊆ E` and `ε > 0`, there is a `C^∞` map `G : E → E'`
which is `ε`-close to `F` and whose derivative is `ε`-close to the derivative of `F` on `K`.

The construction is the classical one: multiply `F` by a smooth compactly supported cutoff `χ`
which is `1` on a ball containing `K`, then convolve with a smooth bump function with support on a
small ball.  The derivative of a convolution is the convolution of the derivative, and both
convolutions are normalized averages of the corresponding values, hence close to the value at the
point under consideration.
-/

open MeasureTheory Metric Set Filter Function
open scoped Convolution ContDiff Topology

namespace Work.Surf

theorem exists_smooth_approx_C1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    (F : E → E') (hF : ContDiff ℝ 1 F) {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : E → E', ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧
      ∀ x ∈ K, ‖G x - F x‖ ≤ ε ∧ ‖fderiv ℝ G x - fderiv ℝ F x‖ ≤ ε := by
  borelize E
  let μ : Measure E := Measure.addHaar
  -- A ball containing `K`.
  obtain ⟨R₀, hR₀⟩ : ∃ R : ℝ, K ⊆ closedBall (0 : E) R :=
    (isBounded_iff_subset_closedBall (0 : E)).1 hK.isBounded
  let R : ℝ := max R₀ 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hRK : K ⊆ closedBall (0 : E) R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  -- A smooth cutoff which is `1` on `closedBall 0 (R + 1)`.
  let χ : ContDiffBump (0 : E) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let χf : E → ℝ := χ
  have hχ_one : ∀ x ∈ closedBall (0 : E) (R + 1), χf x = 1 := fun x hx => χ.one_of_mem_closedBall hx
  have hχ_supp : HasCompactSupport χf := χ.hasCompactSupport
  have hχ_cd : ContDiff ℝ ∞ χf := χ.contDiff
  -- `F` truncated by the cutoff.
  let Fc : E → E' := fun x => χf x • F x
  have hFc_eq : ∀ x ∈ closedBall (0 : E) (R + 1), Fc x = F x := by
    intro x hx
    have h1 : χf x = 1 := hχ_one x hx
    simp only [Fc, h1, one_smul]
  have hFc_supp : HasCompactSupport Fc := by
    have h : HasCompactSupport (χf • F) := hχ_supp.smul_right (f' := F)
    exact h
  have hFc_cd1 : ContDiff ℝ 1 Fc := by
    have hχ1 : ContDiff ℝ 1 χf := hχ_cd.of_le (by simp)
    exact hχ1.smul hF
  have hFc_cont : Continuous Fc := hFc_cd1.continuous
  have hFc_locInt : LocallyIntegrable Fc μ := hFc_cont.locallyIntegrable
  have hFc_fderiv_supp : HasCompactSupport (fderiv ℝ Fc) := hFc_supp.fderiv ℝ
  have hFc_fderiv_cont : Continuous (fderiv ℝ Fc) := hFc_cd1.continuous_fderiv (by norm_num)
  -- Uniform continuity of `F` and of `fderiv F` on a compact neighbourhood of `K`.
  have hK1c : IsCompact (cthickening (1 : ℝ) K) := hK.cthickening
  have hF_uc : UniformContinuousOn F (cthickening (1 : ℝ) K) :=
    hK1c.uniformContinuousOn_of_continuous hF.continuous.continuousOn
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.uniformContinuousOn_iff.mp hF_uc ε hε
  have hdf_cont : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hdf_uc : UniformContinuousOn (fderiv ℝ F) (cthickening (1 : ℝ) K) :=
    hK1c.uniformContinuousOn_of_continuous hdf_cont.continuousOn
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.uniformContinuousOn_iff.mp hdf_uc ε hε
  let δ : ℝ := min 1 (min δ₁ δ₂)
  have hδpos : 0 < δ := lt_min one_pos (lt_min hδ₁ hδ₂)
  have hδle1 : δ ≤ 1 := min_le_left _ _
  have hδle₁ : δ ≤ δ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδle₂ : δ ≤ δ₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  -- The mollifier and the smoothed function.
  let φ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδpos, half_lt_self hδpos⟩
  let G : E → E' := φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] Fc
  have hφ_locInt : LocallyIntegrable (φ.normed μ) μ :=
    (ContDiffBump.contDiff_normed (f := φ) (μ := μ) (n := ⊤)).continuous.locallyIntegrable
  -- Points of `ball x δ` with `x ∈ K` lie in the ball where the cutoff is `1`.
  have hmem : ∀ x ∈ K, ∀ y ∈ ball x δ, y ∈ ball (0 : E) (R + 1) := by
    intro x hx y hy
    have hxR : ‖x‖ ≤ R := by
      have h := mem_closedBall.mp (hRK hx); rwa [dist_zero_right] at h
    have hyx : dist y x < δ := mem_ball.mp hy
    rw [mem_ball, dist_zero_right]
    calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ < δ + R := by rw [dist_eq_norm] at hyx; linarith
      _ ≤ 1 + R := by linarith
      _ = R + 1 := by ring
  -- There, the derivative of the truncated map is the derivative of `F`.
  have hfderivFc : ∀ z ∈ ball (0 : E) (R + 1), fderiv ℝ Fc z = fderiv ℝ F z := by
    intro z hz
    have heq : Fc =ᶠ[𝓝 z] F := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      exact hFc_eq y (ball_subset_closedBall hy)
    exact heq.fderiv_eq
  -- And they lie in the compact neighbourhood of `K` used for uniform continuity.
  have hK1mem : ∀ x ∈ K, ∀ y ∈ ball x δ, y ∈ cthickening (1 : ℝ) K := by
    intro x hx y hy
    rw [cthickening_eq_biUnion_closedBall K (by norm_num : (0 : ℝ) ≤ 1)]
    exact mem_iUnion₂.2 ⟨x, subset_closure hx, by
      rw [mem_closedBall]; exact (mem_ball.mp hy).le.trans hδle1⟩
  refine ⟨G, ?_, ?_⟩
  · -- Smoothness of the convolution.
    have h := (ContDiffBump.hasCompactSupport_normed (f := φ) (μ := μ)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (ContDiffBump.contDiff_normed (f := φ) (μ := μ) (n := ⊤)) hFc_locInt
    exact h
  · intro x hx
    have hxball : x ∈ ball (0 : E) (R + 1) := by
      have hxR : ‖x‖ ≤ R := by
        have h := mem_closedBall.mp (hRK hx); rwa [dist_zero_right] at h
      rw [mem_ball, dist_zero_right]; linarith
    have hFcx : Fc x = F x := hFc_eq x (ball_subset_closedBall hxball)
    have hdfcx : fderiv ℝ Fc x = fderiv ℝ F x := hfderivFc x hxball
    have hxK1 : x ∈ cthickening (1 : ℝ) K := closure_subset_cthickening 1 K (subset_closure hx)
    constructor
    · -- Proximity of the values.
      have hbound : ∀ y ∈ ball x φ.rOut, dist (Fc y) (Fc x) ≤ ε := by
        intro y hy
        have hyb : y ∈ closedBall (0 : E) (R + 1) := ball_subset_closedBall (hmem x hx y hy)
        have hyK1 : y ∈ cthickening (1 : ℝ) K := hK1mem x hx y hy
        rw [hFc_eq y hyb, hFcx]
        exact (hδ₁' y hyK1 x hxK1 (by
          exact lt_of_lt_of_le (mem_ball.mp hy) hδle₁)).le
      have h := ContDiffBump.dist_normed_convolution_le (φ := φ) (μ := μ) (g := Fc)
        (x₀ := x) (ε := ε) hFc_cont.aestronglyMeasurable hbound
      rw [hFcx] at h
      rwa [dist_eq_norm] at h
    · -- Proximity of the derivatives.
      have hGderiv : HasFDerivAt G ((φ.normed μ ⋆[ContinuousLinearMap.precompR E
            (ContinuousLinearMap.lsmul ℝ ℝ), μ] fderiv ℝ Fc) x) x :=
        hFc_supp.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hφ_locInt hFc_cd1 x
      rw [hGderiv.fderiv]
      refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun y => ?_
      have hAx : ((φ.normed μ ⋆[ContinuousLinearMap.precompR E
            (ContinuousLinearMap.lsmul ℝ ℝ), μ] fderiv ℝ Fc) x) y
          = (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
              (fun a => fderiv ℝ Fc a y)) x :=
        convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hφ_locInt hFc_fderiv_supp
          hFc_fderiv_cont x y
      have hsub : (((φ.normed μ ⋆[ContinuousLinearMap.precompR E
            (ContinuousLinearMap.lsmul ℝ ℝ), μ] fderiv ℝ Fc) x) - fderiv ℝ F x) y
          = (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
              (fun a => fderiv ℝ Fc a y)) x - (fun a => fderiv ℝ Fc a y) x := by
        rw [sub_apply, hAx, ← hdfcx]
      rw [hsub, ← dist_eq_norm]
      refine ContDiffBump.dist_normed_convolution_le (φ := φ) (μ := μ)
        (g := fun a => fderiv ℝ Fc a y) (x₀ := x) (ε := ε * ‖y‖) ?_ ?_
      · exact (hFc_fderiv_cont.clm_apply continuous_const).aestronglyMeasurable
      · intro y' hy'
        have hy'b : y' ∈ ball (0 : E) (R + 1) := hmem x hx y' hy'
        have hy'K1 : y' ∈ cthickening (1 : ℝ) K := hK1mem x hx y' hy'
        have hd : dist (fderiv ℝ F y') (fderiv ℝ F x) ≤ ε :=
          (hδ₂' y' hy'K1 x hxK1 (by
            exact lt_of_lt_of_le (mem_ball.mp hy') hδle₂)).le
        have hd' : ‖fderiv ℝ F y' - fderiv ℝ F x‖ ≤ ε := by
          rwa [dist_eq_norm] at hd
        rw [hfderivFc y' hy'b, hdfcx]
        calc dist ((fderiv ℝ F y') y) ((fderiv ℝ F x) y)
            = ‖((fderiv ℝ F y' - fderiv ℝ F x) y)‖ := by
              rw [dist_eq_norm, sub_apply]
          _ ≤ ‖fderiv ℝ F y' - fderiv ℝ F x‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ε * ‖y‖ := mul_le_mul_of_nonneg_right hd' (norm_nonneg y)

end Work.Surf
