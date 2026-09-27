import Mathlib
import Submission.Work.Drive.TParity.ChartDeriv
import Submission.Work.Drive.exists_local_normalForm

/-!
# The local graph structure of the triple intersection set

At a point `x` of the chart region at which the three chains meet and at which the charted
difference map is transverse to the coordinate hyperplane `{v | v i = 0}`, the triple intersection
set is the graph of a smooth `η` over the `i`-th coordinate: `y = (y i) • eᵢ + η (y i)`.

This is the nine-box analogue of `Work.Drive.exists_local_graph`.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## Smoothness of the chart composition -/

theorem contMDiffOn_chart_comp8 (f : Amb 8 → M) (hf : ContMDiff (𝓡 9) (𝓡 4) Ctop f) (p : M) :
    ContMDiffOn (𝓡 9) (𝓡 4) Ctop (fun x => (Work.Drive.chr p) (f x))
      (f ⁻¹' (Work.Drive.chr p).source) := by
  have hchart : ContMDiffOn (𝓡 4) (𝓡 4) Ctop (Work.Drive.chr p) (Work.Drive.chr p).source := by
    have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
    simpa [Work.Drive.chr] using h
  have hcomp := hchart.comp (hf.contMDiffOn (s := f ⁻¹' (Work.Drive.chr p).source))
    (fun x hx => hx)
  simpa [Function.comp_def] using hcomp

theorem contMDiffOn_to_contDiffOn8 (F : EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 4))
    (s : Set (EuclideanSpace ℝ (Fin 9)))
    (h : ContMDiffOn (𝓡 9) (𝓡 4) (n := Ctop) F s) : ContDiffOn ℝ Ctop F s :=
  h.contDiffOn

/-- **The charted difference map of the three chains is smooth on the chart region.** -/
theorem contDiffOn_chartDiff3 (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k)) :
    ContDiffOn ℝ Ctop (chartDiff3 p D) (region3 p D) := by
  have hchain : ∀ k : Fin 3, ContDiffOn ℝ Ctop
      (fun x : Amb 8 => (Work.Drive.chr p) (D k (bPartC k x))) (region3 p D) := by
    intro k
    have hk : ContMDiff (𝓡 9) (𝓡 4) Ctop (fun x : Amb 8 => D k (bPartC k x)) :=
      (hD k).comp (bPartC k).contMDiff
    have := contMDiffOn_chart_comp8 (fun x : Amb 8 => D k (bPartC k x)) hk p
    show ContDiffOn ℝ Ctop (fun x : Amb 8 => (Work.Drive.chr p) (D k (bPartC k x))) (region3 p D)
    exact contMDiffOn_to_contDiffOn8 _ _ (this.mono (fun x hx => hx k))
  have hA := (hchain 0).sub (hchain 1)
  have hB := (hchain 0).sub (hchain 2)
  have hpair : ContDiffOn ℝ Ctop (fun x : Amb 8 => ((fun x : Amb 8 => (Work.Drive.chr p) (D 0 (bPartC 0 x)) -
      (Work.Drive.chr p) (D 1 (bPartC 1 x))) x, (fun x : Amb 8 => (Work.Drive.chr p) (D 0 (bPartC 0 x)) -
      (Work.Drive.chr p) (D 2 (bPartC 2 x))) x)) (region3 p D) := hA.prodMk hB
  have hmain := pUpCLM.contDiff.comp_contDiffOn hpair
  have hfun : (⇑pUpCLM ∘ (fun x : Amb 8 => ((fun x : Amb 8 => (Work.Drive.chr p) (D 0 (bPartC 0 x)) -
        (Work.Drive.chr p) (D 1 (bPartC 1 x))) x,
      (fun x : Amb 8 => (Work.Drive.chr p) (D 0 (bPartC 0 x)) -
        (Work.Drive.chr p) (D 2 (bPartC 2 x))) x))) = chartDiff3 p D := by
    funext x
    simp [chartDiff3, pUpCLM_apply, pUp, Function.comp_def]
  rwa [hfun] at hmain

/-! ## Globalization of the charted difference map -/

theorem exists_chartDiff3_extension (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    {x : Amb 8} (hx : x ∈ region3 p D) :
    ∃ (F : Amb 8 → Tgt 8) (U : Set (Amb 8)), IsOpen U ∧ x ∈ U ∧ U ⊆ region3 p D ∧
      ContDiff ℝ Ctop F ∧ Set.EqOn F (chartDiff3 p D) U := by
  have hregion : IsOpen (region3 p D) := isOpen_region3 p D (fun k => (hD k).continuous)
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hregion x hx
  set χ : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩ with hχ
  have hχ1 : ∀ y ∈ Metric.ball x (r / 4), χ y = 1 := fun y hy =>
    χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hχ0 : ∀ y, r / 2 ≤ dist y x → χ y = 0 := by
    intro y hy
    refine χ.zero_of_le_dist ?_
    rw [hχ]
    show r / 2 ≤ dist y x
    exact hy
  have hsupp : ∀ y, ¬ (dist y x ≤ r / 2) → ∀ᶠ z in 𝓝 y, χ z = 0 := by
    intro y hy
    have hy' : r / 2 < dist y x := not_le.mp hy
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds y (sub_pos.mpr hy')) ?_
    intro z hz
    refine hχ0 z (le_of_lt ?_)
    have hz' : dist z y < dist y x - r / 2 := Metric.mem_ball.mp hz
    have h1 : dist y x ≤ dist z y + dist z x := by
      simpa [dist_comm] using dist_triangle y z x
    linarith
  refine ⟨fun y => χ y • chartDiff3 p D y, Metric.ball x (r / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by linarith), ?_, ?_, ?_⟩
  · intro y hy
    exact hsub (Metric.ball_subset_ball (by linarith) hy)
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ region3 p D
    · have h1 : ContDiffAt ℝ Ctop (fun y : Amb 8 => χ y) y := χ.contDiff.contDiffAt
      have h2 : ContDiffAt ℝ Ctop (chartDiff3 p D) y :=
        (contDiffOn_chartDiff3 p D hD).contDiffAt (hregion.mem_nhds hy)
      exact h1.smul h2
    · have hdist : ¬ (dist y x ≤ r / 2) := by
        intro hcon
        refine hy (hsub (Metric.mem_ball.mpr ?_))
        linarith
      refine (contDiffAt_const (c := (0 : Tgt 8))).congr_of_eventuallyEq ?_
      filter_upwards [hsupp y hdist] with z hz
      simp [hz]
  · intro y hy
    change χ y • chartDiff3 p D y = chartDiff3 p D y
    rw [hχ1 y hy, one_smul]

/-! ## The local graph structure -/

theorem exists_local_graph3 (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    {x : Amb 8} (hx : x ∈ region3 p D) (hm : meet3 D x) (i : Fin 9)
    (hsurj_i : Function.Surjective (fun v : {v : Amb 8 // v i = 0} =>
      fderiv ℝ (chartDiff3 p D) x v.1)) :
    ∃ (δ ρ : ℝ) (η : ℝ → Amb 8), 0 < δ ∧ 0 < ρ ∧ ContDiff ℝ Ctop η ∧
      (∀ u, η u i = 0) ∧ η (x i) = x - (x i) • EuclideanSpace.single i 1 ∧
      (∀ y, |y i - x i| < δ →
        ‖y - (y i) • EuclideanSpace.single i 1 - η (y i)‖ < ρ →
        y ∈ region3 p D ∧
        (meet3 D y ↔ y = (y i) • EuclideanSpace.single i 1 + η (y i))) := by
  obtain ⟨F, U, hUopen, hxU, hUsub, hFsmooth, hFeq⟩ :=
    exists_chartDiff3_extension p D hD hx
  have hFx : F x = 0 := by
    rw [hFeq hxU]
    exact (chartDiff3_eq_zero_iff hx).mpr hm
  have hderiv : fderiv ℝ F x = fderiv ℝ (chartDiff3 p D) x := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact hFeq hy
  have hface' : Function.Surjective (fun v : {v : Amb 8 // v i = 0} =>
      fderiv ℝ F x v.1) := by
    rw [hderiv]
    exact hsurj_i
  obtain ⟨δ₀, ρ₀, η, hδ₀, hρ₀, hηsmooth, hηi, hηx, -, hchar⟩ :=
    Work.Drive.exists_local_normalForm hFsmooth hFx i hface'
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  have hηcont : ContinuousAt η (x i) := hηsmooth.continuous.continuousAt
  obtain ⟨δ₁, hδ₁, hηnear⟩ : ∃ δ₁ > 0, ∀ u, |u - x i| < δ₁ → ‖η u - η (x i)‖ < ε / 3 := by
    have hball : Metric.ball (η (x i)) (ε / 3) ∈ 𝓝 (η (x i)) := Metric.ball_mem_nhds _ hε3
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
    have hsplit : y - x = (y - (y i) • EuclideanSpace.single i 1 - η (y i)) +
        (η (y i) - η (x i)) + ((y i - x i) • EuclideanSpace.single i 1) := by
      rw [hηx]
      module
    rw [hsplit]
    have hnorm : ‖(y - (y i) • EuclideanSpace.single i 1 - η (y i)) +
        (η (y i) - η (x i)) + ((y i - x i) • EuclideanSpace.single i 1)‖
        ≤ ‖y - (y i) • EuclideanSpace.single i 1 - η (y i)‖
          + ‖η (y i) - η (x i)‖ + |y i - x i| := by
      have hsingle : ‖(y i - x i) • EuclideanSpace.single (i : Fin 9) (1 : ℝ)‖ = |y i - x i| := by
        rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single]
        simp
      have h1 := norm_add_le ((y - (y i) • EuclideanSpace.single i 1 - η (y i))
        + (η (y i) - η (x i))) ((y i - x i) • EuclideanSpace.single (i : Fin 9) (1 : ℝ))
      have h2 := norm_add_le (y - (y i) • EuclideanSpace.single i 1 - η (y i))
        (η (y i) - η (x i))
      rw [hsingle] at h1
      linarith
    have hη' := hηnear (y i) h1₁
    linarith
  have hyU : y ∈ U := hεsub hynorm
  have hyreg : y ∈ region3 p D := hUsub hyU
  exact ⟨hyreg, by rw [← chartDiff3_eq_zero_iff hyreg, ← hFeq hyU, hchar y h1₀ h2₀]⟩

end

end Work.Drive.TParity
