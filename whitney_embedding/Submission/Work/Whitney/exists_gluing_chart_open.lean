import Mathlib
import Submission.Work.Whitney.exists_chart_globally_smooth_symm
import Submission.Work.Whitney.InsertedDoublePoint

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

theorem exists_gluing_chart_open {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target)
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hcinv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u)
    (W : Set M) (hWopen : IsOpen W) (hzW : c.symm 0 ∈ W) (hWsub : W ⊆ c.source)
    (ψ : EuclideanSpace ℝ (Fin n)) :
    ∃ (ĉ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (r : ℝ),
      0 < r ∧ Metric.ball 0 r ⊆ c.target ∧
      ĉ.target = Metric.ball 0 (r / 2) ∧
      ĉ.source = c.symm '' Metric.ball 0 (r / 2) ∧
      ĉ.source ⊆ W ∧
      c.symm 0 ∈ ĉ.source ∧ ĉ (c.symm 0) = 0 ∧
      (∀ y : M, y ∈ W → ĉ y = c y) ∧
      (∀ y : M, y ∉ W → ĉ y = ψ) ∧
      (∀ y : M, y ∈ ĉ.source →
        ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) ĉ y) ∧
      (∀ u : EuclideanSpace ℝ (Fin n),
        ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) ĉ.symm u) := by
  classical
  -- a radius `r0 > 0` with `ball 0 r0 ⊆ c.target`
  obtain ⟨r0, hr0, hball0⟩ := (Metric.isOpen_iff.mp c.open_target) 0 h0
  -- `c.symm` is continuous at `0`, so a small ball around `0` is mapped into `W`
  have hcontAt : ContinuousAt (⇑c.symm) (0 : EuclideanSpace ℝ (Fin n)) :=
    c.continuousOn_symm.continuousAt (c.open_target.mem_nhds h0)
  have hpre : (⇑c.symm) ⁻¹' W ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) :=
    hcontAt.preimage_mem_nhds (hWopen.mem_nhds hzW)
  obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp hpre
  -- choose the radius `r = min r0 (2δ)`
  set r : ℝ := min r0 (2 * δ) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact lt_min hr0 (by linarith)
  have hr_le_r0 : r ≤ r0 := by rw [hrdef]; exact min_le_left _ _
  have hr_le_2δ : r ≤ 2 * δ := by rw [hrdef]; exact min_le_right _ _
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ c.target :=
    (Metric.ball_subset_ball hr_le_r0).trans hball0
  have hball2 : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2) ⊆ c.target :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  have hr2pos : (0 : ℝ) < r / 2 := by linarith
  have h0ball2 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 (r / 2) := by
    rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact hr2pos
  have hball2δ : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2) ⊆ (⇑c.symm) ⁻¹' W :=
    (Metric.ball_subset_ball (by linarith : r / 2 ≤ δ)).trans hδball
  -- a bump function which is `1` on `ball 0 (r/2)` and supported in `ball 0 r`
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨r / 2, r, by linarith, by linarith⟩
  have hbrIn : b.rIn = r / 2 := rfl
  have hbrOut : b.rOut = r := rfl
  -- the retraction `φ u = b u • u`, globally smooth, with image in `ball 0 r`
  let φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun u => b u • u
  have hφcont : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) φ :=
    (b.contDiff (n := ⊤)).smul contDiff_id
  have hφmem : ∀ u : EuclideanSpace ℝ (Fin n), φ u ∈ c.target := by
    intro u
    by_cases h : ‖u‖ < r
    · apply hball
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖φ u‖ = ‖b u • u‖ := rfl
        _ = ‖b u‖ * ‖u‖ := norm_smul _ _
        _ = |b u| * ‖u‖ := by rw [Real.norm_eq_abs]
        _ = b u * ‖u‖ := by rw [abs_of_nonneg b.nonneg]
        _ ≤ 1 * ‖u‖ := by gcongr; exact b.le_one
        _ = ‖u‖ := by rw [one_mul]
        _ < r := h
    · have hbu : b u = 0 := by
        rw [← Function.notMem_support]
        rw [b.support_eq, hbrOut]
        simp only [Metric.mem_ball, not_lt, dist_zero_right]
        exact not_lt.mp h
      have hz : φ u = 0 := by simp [φ, hbu]
      rw [hz]
      apply hball
      rw [Metric.mem_ball, dist_zero_right, norm_zero]
      exact hrpos
  have hφid : ∀ u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2), φ u = u := by
    intro u hu
    have h1 : b u = 1 := by
      apply b.one_of_mem_closedBall
      rw [hbrIn]
      exact Metric.ball_subset_closedBall hu
    simp [φ, h1]
  -- the globally smooth extension of `c.symm` off its target
  let g : EuclideanSpace ℝ (Fin n) → M := fun u => c.symm (φ u)
  have hg : ∀ u : EuclideanSpace ℝ (Fin n),
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) g u := by
    intro u
    have h1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (((⊤ : ℕ∞) : WithTop ℕ∞)) φ u := (hφcont.contMDiff).contMDiffAt
    have h2 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (((⊤ : ℕ∞) : WithTop ℕ∞)) c.symm (φ u) := hcinv (φ u) (hφmem u)
    have h3 := ContMDiffAt.comp u h2 h1
    simpa [g, Function.comp_def] using h3
  -- the new source
  let C : Set M := c.symm '' Metric.ball 0 (r / 2)
  have hC_sub : C ⊆ c.source := by
    rintro y ⟨u, hu, rfl⟩
    exact c.map_target (hball2 hu)
  have hCopen : IsOpen C := c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball2
  have hCsubW : C ⊆ W := by
    rintro y ⟨u, hu, rfl⟩
    exact hball2δ hu
  have hp_mem : c.symm 0 ∈ C := ⟨0, h0ball2, rfl⟩
  have hgu : ∀ u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2), g u = c.symm u :=
    fun u hu => by simp [g, hφid u hu]
  -- the new chart
  let ĉ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    { toPartialHomeomorph :=
        { toPartialEquiv :=
            { toFun := fun y => if y ∈ W then c y else ψ
              invFun := g
              source := C
              target := Metric.ball 0 (r / 2)
              map_source' := by
                rintro y ⟨u, hu, rfl⟩
                rw [if_pos (hCsubW ⟨u, hu, rfl⟩)]
                rw [c.right_inv (hball2 hu)]
                exact hu
              map_target' := by
                intro u hu
                rw [hgu u hu]
                exact ⟨u, hu, rfl⟩
              left_inv' := by
                rintro y ⟨u, hu, rfl⟩
                rw [if_pos (hCsubW ⟨u, hu, rfl⟩)]
                rw [c.right_inv (hball2 hu)]
                exact hgu u hu
              right_inv' := by
                intro u hu
                have hmemW : g u ∈ W := hCsubW (by rw [hgu u hu]; exact ⟨u, hu, rfl⟩)
                rw [if_pos hmemW, hgu u hu, c.right_inv (hball2 hu)] }
          continuousOn_toFun := by
            have hEq : Set.EqOn (fun y => if y ∈ W then c y else ψ) (⇑c) C :=
              fun y hy => by simp only [if_pos (hCsubW hy)]
            exact (c.continuousOn.mono hC_sub).congr hEq
          continuousOn_invFun := by
            have hgc : Continuous g := by
              rw [continuous_iff_continuousAt]
              intro u
              exact (hg u).continuousAt
            exact hgc.continuousOn }
      open_source := hCopen
      open_target := Metric.isOpen_ball }
  have hĉ_coe : ∀ y : M, ĉ y = (if y ∈ W then c y else ψ) := fun y => rfl
  have hĉ_symm : (ĉ.symm : EuclideanSpace ℝ (Fin n) → M) = g := rfl
  refine ⟨ĉ, r, hrpos, hball, rfl, rfl, hCsubW, hp_mem, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hĉ_coe, if_pos hzW, c.right_inv h0]
  · intro y hy; rw [hĉ_coe, if_pos hy]
  · intro y hy; rw [hĉ_coe, if_neg hy]
  · intro y hy
    have hc := hcsm y (hC_sub hy)
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [hWopen.mem_nhds (hCsubW hy)] with z hz
    rw [hĉ_coe, if_pos hz]
  · intro u
    rw [hĉ_symm]
    exact hg u

end Work.Whitney
