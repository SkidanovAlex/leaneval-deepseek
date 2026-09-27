import Mathlib

namespace Work.Whitney

/-- Auxiliary version, for a manifold modelled on an arbitrary real normed space `E` admitting bump
functions.  Given a chart `c` (an open partial homeomorphism) which is smooth on its source and
whose inverse is smooth on its target, one can shrink it to a chart `c'` around the point
`c.symm 0`, with `c' (c.symm 0) = 0`, agreeing with `c` on its source, smooth on its source, and
whose inverse is smooth *everywhere* on `E` (the inverse is extended off the target by a bump
function argument, making it globally smooth). -/
theorem exists_chart_globally_smooth_symm_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (c : OpenPartialHomeomorph M E)
    (h0 : (0 : E) ∈ c.target)
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
        ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hcinv : ∀ u : E, u ∈ c.target →
      ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
        ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u) :
    ∃ c' : OpenPartialHomeomorph M E,
      c'.source ⊆ c.source ∧
      (c.symm 0) ∈ c'.source ∧ c' (c.symm 0) = 0 ∧
      (∀ y : M, y ∈ c'.source → c' y = c y) ∧
      (∀ y : M, y ∈ c'.source →
        ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
          ((⊤ : ℕ∞) : WithTop ℕ∞) c' y) ∧
      (∀ u : E,
        ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
          ((⊤ : ℕ∞) : WithTop ℕ∞) c'.symm u) := by
  classical
  -- a radius `r > 0` with `ball 0 r ⊆ c.target`
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp c.open_target) 0 h0
  have hball2 : Metric.ball 0 (r / 2) ⊆ c.target :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  have hr2pos : 0 < r / 2 := by linarith
  have h0ball2 : (0 : E) ∈ Metric.ball 0 (r / 2) := by
    rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact hr2pos
  -- a bump function which is `1` on `ball 0 (r/2)` and supported in `ball 0 r`
  let b : ContDiffBump (0 : E) := ⟨r / 2, r, by linarith, by linarith⟩
  have hbrIn : b.rIn = r / 2 := rfl
  have hbrOut : b.rOut = r := rfl
  -- the "retraction" `φ u = b u • u`, a globally smooth map `E → E` with image in `ball 0 r`
  let φ : E → E := fun u => b u • u
  have hφcont : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) φ :=
    (b.contDiff (n := ⊤)).smul contDiff_id
  have hφmem : ∀ u : E, φ u ∈ c.target := by
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
      exact hr
  have hφid : ∀ u ∈ Metric.ball 0 (r / 2), φ u = u := by
    intro u hu
    have h1 : b u = 1 := by
      apply b.one_of_mem_closedBall
      rw [hbrIn]
      exact Metric.ball_subset_closedBall hu
    simp [φ, h1]
  -- the globally smooth extension of `c.symm` off its target
  let g : E → M := fun u => c.symm (φ u)
  have hg : ∀ u : E, ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
      (((⊤ : ℕ∞) : WithTop ℕ∞)) g u := by
    intro u
    have h1 : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
        (((⊤ : ℕ∞) : WithTop ℕ∞)) φ u := (hφcont.contMDiff).contMDiffAt
    have h2 : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
        (((⊤ : ℕ∞) : WithTop ℕ∞)) c.symm (φ u) := hcinv (φ u) (hφmem u)
    have h3 := ContMDiffAt.comp u h2 h1
    simpa [g, Function.comp_def] using h3
  -- the new source
  let C : Set M := c.symm '' Metric.ball 0 (r / 2)
  have hC_sub : C ⊆ c.source := by
    rintro y ⟨u, hu, rfl⟩
    exact c.map_target (hball2 hu)
  have hCopen : IsOpen C := c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball2
  have hp_mem : c.symm 0 ∈ C := ⟨0, h0ball2, rfl⟩
  -- the new chart
  let c' : OpenPartialHomeomorph M E :=
    { toPartialHomeomorph :=
        { toPartialEquiv :=
            { toFun := fun y => c y
              invFun := g
              source := C
              target := Metric.ball 0 (r / 2)
              map_source' := by
                rintro y ⟨u, hu, rfl⟩
                rw [c.right_inv (hball2 hu)]
                exact hu
              map_target' := by
                intro u hu
                have hgu : g u = c.symm u := by simp [g, hφid u hu]
                rw [hgu]
                exact ⟨u, hu, rfl⟩
              left_inv' := by
                rintro y ⟨u, hu, rfl⟩
                rw [c.right_inv (hball2 hu)]
                simp [g, hφid u hu]
              right_inv' := by
                intro u hu
                have hgu : g u = c.symm u := by simp [g, hφid u hu]
                rw [hgu, c.right_inv (hball2 hu)] }
          continuousOn_toFun := c.continuousOn.mono hC_sub
          continuousOn_invFun := by
            have hEq : Set.EqOn g (⇑c.symm) (Metric.ball 0 (r / 2)) :=
              fun u hu => by simp [g, hφid u hu]
            exact (c.continuousOn_symm.mono hball2).congr hEq }
      open_source := hCopen
      open_target := Metric.isOpen_ball }
  refine ⟨c', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hC_sub
  · exact hp_mem
  · exact c.right_inv h0
  · intro y hy; rfl
  · intro y hy; exact hcsm y (hC_sub hy)
  · intro u; exact hg u

theorem exists_chart_globally_smooth_symm {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target)
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hcinv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u) :
    ∃ c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      c'.source ⊆ c.source ∧
      (c.symm 0) ∈ c'.source ∧ c' (c.symm 0) = 0 ∧
      (∀ y : M, y ∈ c'.source → c' y = c y) ∧
      (∀ y : M, y ∈ c'.source →
        ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c' y) ∧
      (∀ u : EuclideanSpace ℝ (Fin n),
        ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c'.symm u) :=
  exists_chart_globally_smooth_symm_aux c h0 hcsm hcinv

end Work.Whitney
