import Mathlib
import Submission.Work.ManifoldParity.Defs
import Submission.Work.ManifoldParity.GraphManifold
import Submission.Work.ManifoldParity.OpensInclusion
import Submission.Work.OneDim.classify_connected_one_manifold
import Submission.Work.Drive.curve_deriv_ne_zero
import Submission.Work.Drive.essential_loop

/-!
# Periodic parametrisations of the components

Every connected component of `↥K` is a compact connected smooth `1`-manifold, hence diffeomorphic
to the circle; composing with `Circle.exp` gives a periodic parametrisation of the component by
`ℝ` (period `2π`) whose derivative never vanishes.
-/

open scoped Manifold Topology

namespace Work.ManifoldParity

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set

variable {n : ℕ}

theorem isOpen_connectedComponent_graph (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) :
    letI := graphChartedSpace K hgra
    ∀ x : ↥K, IsOpen (connectedComponent x) := by
  letI := graphChartedSpace K hgra
  haveI hgr := hasGroupoid_graph K hgra
  haveI hism : IsManifold (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) ↥K :=
    IsManifold.mk' _ _ _
  have hkey : ∀ x : ↥K, connectedComponent x ∈ 𝓝 x := by
    intro x
    set c := chartAt ME1 x with hc
    have htarget : c.target ∈ 𝓝 (c x) :=
      c.open_target.mem_nhds (c.map_source (mem_chart_source _ _))
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp htarget
    have hBnhds : Metric.ball (c x) r ∈ 𝓝 (c x) := Metric.ball_mem_nhds _ hr
    have hBsymm : Metric.ball (c x) r ⊆ c.symm.source := by
      rw [OpenPartialHomeomorph.symm_source]
      exact hrsub
    have himg : c.symm '' Metric.ball (c x) r ∈ 𝓝 (c.symm (c x)) :=
      c.symm.image_mem_nhds (c.map_source (mem_chart_source _ _)) hBnhds
    have hxmem : c.symm (c x) = x := c.left_inv (mem_chart_source _ _)
    rw [hxmem] at himg
    have hpreconn : IsPreconnected (c.symm '' Metric.ball (c x) r) :=
      (convex_ball (c x) r).isPreconnected.image _ (c.continuousOn_invFun.mono hBsymm)
    have hxmem' : x ∈ c.symm '' Metric.ball (c x) r :=
      ⟨c x, Metric.mem_ball_self hr, hxmem⟩
    exact Filter.mem_of_superset himg (hpreconn.subset_connectedComponent hxmem')
  intro x
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have h1 : connectedComponent y ∈ 𝓝 y := hkey y
  rw [connectedComponent_eq hy]
  exact h1

/-- Every point of `↥K` lies on a periodic parametrised closed curve. -/
theorem exists_periodic_param_component (K : Set (EuclideanSpace ℝ (Fin n)))
    (hgra : HasLocalGraphCharts K) (hK : IsCompact K) :
    letI := graphChartedSpace K hgra
    ∀ x : ↥K, ∃ (γ : ℝ → ↥K) (T : ℝ), 0 < T ∧
      ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
        ((⊤ : ℕ∞) : WithTop ℕ∞) γ ∧ Function.Periodic γ T ∧
      (∀ t : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1) γ t 1 ≠ 0) ∧
      (∀ a b : ℝ, γ a = γ b → ∃ k : ℤ, a = b + k * T) ∧
      Set.range γ = connectedComponent x := by
  letI := graphChartedSpace K hgra
  haveI hgr := hasGroupoid_graph K hgra
  haveI hism : IsManifold (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) ↥K :=
    IsManifold.mk' _ _ _
  haveI hcpt : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  intro x
  set Cx : TopologicalSpace.Opens ↥K :=
    ⟨connectedComponent x, isOpen_connectedComponent_graph K hgra x⟩ with hCx
  haveI : CompactSpace ↥Cx := by
    have h1 : IsCompact (connectedComponent x : Set ↥K) := isClosed_connectedComponent.isCompact
    exact isCompact_iff_compactSpace.mp h1
  haveI : IsManifold (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) ↥Cx :=
    IsManifold.mk' (modelWithCornersSelf ℝ ME1) ((⊤ : ℕ∞) : WithTop ℕ∞) ↥Cx
  haveI : ConnectedSpace ↥Cx := by
    have h := isConnected_iff_connectedSpace.mp
      (isConnected_connectedComponent (x := x))
    exact h
  rcases Work.OneDim.classify_connected_one_manifold (C := ↥Cx) with ⟨⟨G⟩⟩ | ⟨⟨G⟩⟩
  · -- the `ℝ` case is impossible: `ℝ` would be compact
    exfalso
    have hc : CompactSpace ℝ := G.toHomeomorph.symm.compactSpace
    have hb : Bornology.IsBounded (Set.univ : Set ℝ) :=
      ((isCompact_univ_iff (X := ℝ)).mpr hc).isBounded
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hb
    have h2 := hr (Set.mem_univ (|r| + 1))
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ |r| + 1)] at h2
    have := abs_nonneg r
    linarith [le_abs_self r]
  · refine ⟨fun t : ℝ => ((G (Circle.exp t) : ↥Cx) : ↥K), 2 * Real.pi, Real.two_pi_pos,
      ?_, ?_, ?_, ?_, ?_⟩
    · -- smoothness
      exact (contMDiff_subtype_val (U := Cx) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp
        (G.contMDiff.comp (contMDiff_circleExp (m := ((⊤ : ℕ∞) : WithTop ℕ∞))))
    · -- periodicity
      intro t
      show ((G (Circle.exp (t + 2 * Real.pi)) : ↥Cx) : ↥K) = ((G (Circle.exp t) : ↥Cx) : ↥K)
      rw [Circle.exp_eq_exp.mpr ⟨1, by ring⟩]
    · -- nonvanishing derivative
      intro t hv
      have hchain : mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
          (fun s : ℝ => G (Circle.exp s)) t
          = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
              (G : Circle → ↥Cx) (Circle.exp t)) ∘SL
            (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
              (Circle.exp : ℝ → Circle) t) :=
        mfderiv_comp t (G.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          ((contMDiff_circleExp (m := ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffAt.mdifferentiableAt (by simp))
      have h1 : (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
          (fun s : ℝ => G (Circle.exp s)) t) 1 ≠ 0 := by
        rw [hchain]
        simp only [ContinuousLinearMap.comp_apply]
        intro h0
        have hinj : Function.Injective (mfderiv (modelWithCornersSelf ℝ ME1)
            (modelWithCornersSelf ℝ ME1) (G : Circle → ↥Cx) (Circle.exp t)) :=
          ((G.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) (Circle.exp t)).toLinearEquiv).injective
        exact Work.Drive.circleExp_mfderiv_apply_one_ne_zero t
          (hinj (by rw [h0, map_zero]))
      have hchain2 : mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
          (fun t : ℝ => ((G (Circle.exp t) : ↥Cx) : ↥K)) t
          = (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
              (Subtype.val : ↥Cx → ↥K) (G (Circle.exp t))) ∘SL
            (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
              (fun s : ℝ => G (Circle.exp s)) t) :=
        mfderiv_comp t
          ((Manifold.IsSmoothEmbedding.of_opens (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) Cx).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          ((G.contMDiff.comp (contMDiff_circleExp (m := ((⊤ : ℕ∞) : WithTop ℕ∞)))).contMDiffAt.mdifferentiableAt (by simp))
      have h2 : (mfderiv (modelWithCornersSelf ℝ ME1) (modelWithCornersSelf ℝ ME1)
          (Subtype.val : ↥Cx → ↥K) (G (Circle.exp t)))
          ((mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ME1)
            (fun s : ℝ => G (Circle.exp s)) t) 1) = 0 := by
        have h := hv
        rw [hchain2] at h
        simpa only [ContinuousLinearMap.comp_apply] using h
      exact h1 (mfderiv_subtypeVal_opens_injective Cx (G (Circle.exp t))
        (by rw [h2, map_zero]))
    · -- injectivity modulo the period
      intro a b hab
      have h1 : G (Circle.exp a) = G (Circle.exp b) := Subtype.ext hab
      have h2 : Circle.exp a = Circle.exp b := G.injective h1
      exact Circle.exp_eq_exp.mp h2
    · -- the range is the whole component
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact (G (Circle.exp t) : ↥Cx).2
      · intro hz
        obtain ⟨w, hw⟩ := G.surjective ⟨z, hz⟩
        obtain ⟨θ, hθ⟩ := Work.Drive.corePt_surjective w
        refine ⟨Real.pi * θ, ?_⟩
        show ((G (Circle.exp (Real.pi * θ)) : ↥Cx) : ↥K) = z
        rw [show Circle.exp (Real.pi * θ) = w from hθ]
        exact congrArg (fun y : ↥Cx => (y : ↥K)) hw

end

end Work.ManifoldParity
