import Mathlib

open Set

namespace Work.SimplyConnected.ABS

/-- Transport of ball geometry across a chart: if the closed `c`-ball of radius `ρ` lies in the
target of an open partial homeomorphism `e : X → ℂ`, then the `e.symm`-image of the ball is open,
its closure is the image of the closed ball, its frontier is the image of the sphere, the image of
the closed ball is compact, that frontier is connected, and the image of the ball is (as a subtype)
homeomorphic to — hence simply connected like — the unit disc. -/
theorem chartBall_transport {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall c ρ ⊆ e.target) :
    IsOpen (e.symm '' Metric.ball c ρ) ∧
      closure (e.symm '' Metric.ball c ρ) = e.symm '' Metric.closedBall c ρ ∧
      frontier (e.symm '' Metric.closedBall c ρ) = e.symm '' Metric.sphere c ρ ∧
      IsCompact (e.symm '' Metric.closedBall c ρ) ∧
      IsConnected (frontier (e.symm '' Metric.closedBall c ρ)) ∧
      Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥(e.symm '' Metric.ball c ρ)) ∧
      SimplyConnectedSpace ↥(e.symm '' Metric.ball c ρ) := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hballT : Metric.ball c ρ ⊆ e.target := Metric.ball_subset_closedBall.trans hsub
  have hsphereT : Metric.sphere c ρ ⊆ e.target := Metric.sphere_subset_closedBall.trans hsub
  -- `e.symm` maps subsets of the target into the source
  have imgSub : ∀ t : Set ℂ, t ⊆ e.target → e.symm '' t ⊆ e.source := by
    intro t ht y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact e.map_target (ht hz)
  -- `e.symm '' t` is the "image" of `t` under the partial homeomorphism `e`
  have key : ∀ t : Set ℂ, t ⊆ e.target → e.IsImage (e.symm '' t) t := by
    intro t ht x hx
    constructor
    · intro hxt
      exact ⟨e x, hxt, e.left_inv hx⟩
    · rintro ⟨y, hyt, hyx⟩
      rw [← hyx, e.right_inv (ht hyt)]
      exact hyt
  -- reconstructing a set from its `IsImage` relation with a set inside the target
  have key_eq : ∀ (s : Set X) (t : Set ℂ), e.IsImage s t → s ⊆ e.source → t ⊆ e.target →
      e.symm '' t = s := by
    intro s t h hs ht
    have h1 : e.symm '' (e.target ∩ t) = e.source ∩ s := h.symm_image_eq
    rw [Set.inter_eq_right.mpr ht, Set.inter_eq_right.mpr hs] at h1
    exact h1
  have h1 : IsOpen (e.symm '' Metric.ball c ρ) :=
    e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballT
  have hc : IsCompact (e.symm '' Metric.closedBall c ρ) :=
    (isCompact_closedBall c ρ).image_of_continuousOn (e.continuousOn_symm.mono hsub)
  have h2 : closure (e.symm '' Metric.ball c ρ) = e.symm '' Metric.closedBall c ρ := by
    refine Set.Subset.antisymm ?_ ?_
    · exact (hc.isClosed.closure_subset_iff).mpr (Set.image_mono Metric.ball_subset_closedBall)
    · have hcl : e.IsImage (closure (e.symm '' Metric.ball c ρ)) (Metric.closedBall c ρ) := by
        have := (key (Metric.ball c ρ) hballT).closure
        rwa [closure_ball c hρne] at this
      have h1' : e.symm '' (e.target ∩ Metric.closedBall c ρ) =
          e.source ∩ closure (e.symm '' Metric.ball c ρ) := hcl.symm_image_eq
      rw [Set.inter_eq_right.mpr hsub] at h1'
      exact h1' ▸ Set.inter_subset_right
  have h3 : frontier (e.symm '' Metric.closedBall c ρ) = e.symm '' Metric.sphere c ρ := by
    have hf : e.IsImage (frontier (e.symm '' Metric.closedBall c ρ)) (Metric.sphere c ρ) := by
      have := (key (Metric.closedBall c ρ) hsub).frontier
      rwa [frontier_closedBall c hρne] at this
    have hs : frontier (e.symm '' Metric.closedBall c ρ) ⊆ e.source :=
      frontier_subset_closure.trans (by rw [hc.isClosed.closure_eq]; exact imgSub _ hsub)
    exact (key_eq _ _ hf hs hsphereT).symm
  have h4 : IsCompact (e.symm '' Metric.closedBall c ρ) := hc
  have h5 : IsConnected (frontier (e.symm '' Metric.closedBall c ρ)) := by
    rw [h3]
    exact IsConnected.image
      (isConnected_sphere (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) c
        (le_of_lt hρ))
      _ (e.continuousOn_symm.mono hsphereT)
  have h6 : Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥(e.symm '' Metric.ball c ρ)) := by
    refine ⟨(OpenPartialHomeomorph.unitBallBall c ρ hρ).toHomeomorphSourceTarget.trans ?_⟩
    have hballImage : e.IsImage (e.symm '' Metric.ball c ρ) (Metric.ball c ρ) := key _ hballT
    have hs : IsOpen (e.source ∩ (e.symm '' Metric.ball c ρ)) := by
      rw [Set.inter_eq_right.mpr (imgSub _ hballT)]; exact h1
    refine ((Homeomorph.setCongr (Set.inter_eq_right.mpr hballT)).symm).trans ?_
    refine ((hballImage.restr hs).toHomeomorphSourceTarget.symm).trans ?_
    exact Homeomorph.setCongr (Set.inter_eq_right.mpr (imgSub _ hballT))
  have h7 : SimplyConnectedSpace ↥(e.symm '' Metric.ball c ρ) := by
    obtain ⟨Φ⟩ := h6
    have hC1 : ContractibleSpace ↥(Metric.ball (0 : ℂ) 1) :=
      Metric.contractibleSpace_ball one_pos
    have hC2 : ContractibleSpace ↥(e.symm '' Metric.ball c ρ) := Φ.symm.contractibleSpace
    exact inferInstance
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end Work.SimplyConnected.ABS
