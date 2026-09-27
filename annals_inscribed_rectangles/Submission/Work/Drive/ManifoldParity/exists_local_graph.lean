import Submission.Work.Drive.ManifoldParity.exists_chartDiff_extension

/-!
# The local graph structure of the intersection set

`Work.Drive.exists_local_graph`: near a point `x` of the chart region at which the two chains meet
and at which the charted difference map is transverse to the coordinate hyperplane `{v | v i = 0}`,
the intersection set `{y | D (sqPart y) = N (cbPart y)}` is the graph of a smooth map `η` over the
`i`-th coordinate:

`y = (y i) • eᵢ + η (y i)`.

This is the local structure of the intersection 1-manifold (in the form in which the vector-space
chapter uses it: `Work.Drive.ChartData`), obtained from `Work.Drive.exists_local_normalForm` applied
to the globalization of the charted difference map
(`Work.Drive.exists_chartDiff_extension`).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

theorem exists_local_graph (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N) (heq : D (sqPart x) = N (cbPart x)) (i : Fin 5)
    (hface_i : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (chartDiff p D N) x v.1)) :
    ∃ (δ ρ : ℝ) (η : ℝ → Amb 4), 0 < δ ∧ 0 < ρ ∧ ContDiff ℝ Ctop η ∧
      (∀ u, η u i = 0) ∧ η (x i) = x - (x i) • EuclideanSpace.single i 1 ∧
      (∀ y, |y i - x i| < δ →
        ‖y - (y i) • EuclideanSpace.single i 1 - η (y i)‖ < ρ →
        y ∈ chartRegion p D N ∧
        (D (sqPart y) = N (cbPart y) ↔
          y = (y i) • EuclideanSpace.single i 1 + η (y i))) := by
  obtain ⟨F, U, hUopen, hxU, hUsub, hFsmooth, hFeq⟩ :=
    exists_chartDiff_extension p D N hD hN hx
  have hFx : F x = 0 := by
    rw [hFeq hxU]
    exact (chartDiff_eq_zero_iff hx).mpr heq
  have hderiv : fderiv ℝ F x = fderiv ℝ (chartDiff p D N) x := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact hFeq hy
  have hface' : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ F x v.1) := by
    rw [hderiv]
    exact hface_i
  obtain ⟨δ₀, ρ₀, η, hδ₀, hρ₀, hηsmooth, hηi, hηx, -, hchar⟩ :=
    exists_local_normalForm hFsmooth hFx i hface'
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  have hε3 : (0:ℝ) < ε / 3 := by linarith
  have hηcont : ContinuousAt η (x i) := hηsmooth.continuous.continuousAt
  obtain ⟨δ₁, hδ₁, hηnear⟩ : ∃ δ₁ > 0, ∀ u, |u - x i| < δ₁ → ‖η u - η (x i)‖ < ε / 3 := by
    have hball : Metric.ball (η (x i)) (ε / 3) ∈ 𝓝 (η (x i)) :=
      Metric.ball_mem_nhds _ hε3
    obtain ⟨δ₁, hδ₁, hsub⟩ := Metric.mem_nhds_iff.mp (hηcont.eventually hball)
    exact ⟨δ₁, hδ₁, fun u hu => hsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hu)⟩
  refine ⟨min (min δ₀ δ₁) (ε / 3), min ρ₀ (ε / 3), η,
    lt_min (lt_min hδ₀ hδ₁) hε3, lt_min hρ₀ hε3, hηsmooth, hηi, hηx, ?_⟩
  intro y h1 h2
  have h1₀ : |y i - x i| < δ₀ :=
    lt_of_lt_of_le h1 (le_trans (min_le_left _ _) (min_le_left _ _))
  have h1₁ : |y i - x i| < δ₁ :=
    lt_of_lt_of_le h1 (le_trans (min_le_left _ _) (min_le_right _ _))
  have h1ε : |y i - x i| < ε / 3 := lt_of_lt_of_le h1 (min_le_right _ _)
  have h2₀ : ‖y - (y i) • EuclideanSpace.single i 1 - η (y i)‖ < ρ₀ :=
    lt_of_lt_of_le h2 (min_le_left _ _)
  have h2ε : ‖y - (y i) • EuclideanSpace.single i 1 - η (y i)‖ < ε / 3 :=
    lt_of_lt_of_le h2 (min_le_right _ _)
  have hynorm : ‖y - x‖ < ε := by
    have hsplit : y - x = (y - (y i) • EuclideanSpace.single i 1 - η (y i))
        + (η (y i) - η (x i)) + ((y i - x i) • EuclideanSpace.single i 1) := by
      rw [hηx]
      module
    rw [hsplit]
    have hnorm : ‖(y - (y i) • EuclideanSpace.single i 1 - η (y i))
        + (η (y i) - η (x i)) + ((y i - x i) • EuclideanSpace.single i 1)‖
        ≤ ‖y - (y i) • EuclideanSpace.single i 1 - η (y i)‖
          + ‖η (y i) - η (x i)‖ + |y i - x i| := by
      have hsingle : ‖(y i - x i) • EuclideanSpace.single (i : Fin 5) (1 : ℝ)‖ = |y i - x i| := by
        rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single]
        simp
      have h1 := norm_add_le ((y - (y i) • EuclideanSpace.single i 1 - η (y i))
        + (η (y i) - η (x i))) ((y i - x i) • EuclideanSpace.single (i : Fin 5) (1 : ℝ))
      have h2 := norm_add_le (y - (y i) • EuclideanSpace.single i 1 - η (y i))
        (η (y i) - η (x i))
      rw [hsingle] at h1
      linarith
    have hη' := hηnear (y i) h1₁
    linarith
  have hyU : y ∈ U := hεsub hynorm
  have hyreg : y ∈ chartRegion p D N := hUsub hyU
  exact ⟨hyreg, by rw [← chartDiff_eq_zero_iff hyreg, ← hFeq hyU, hchar y h1₀ h2₀]⟩

end

end Work.Drive
