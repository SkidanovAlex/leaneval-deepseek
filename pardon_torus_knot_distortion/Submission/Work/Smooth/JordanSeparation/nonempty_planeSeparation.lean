import Mathlib
import Submission.Work.Smooth.Jordan.All

namespace Work.Smooth.JordanSeparation

open Set Metric

/-- For `0 ≤ R`, the exterior `{z : ℂ | R < ‖z‖}` of the closed ball of radius `R` is
preconnected.  It is the image of the preconnected set `{z | z ≠ 0}` (the complement of a point, in
the plane, whose real dimension is `2`) under the radial map `z ↦ (‖z‖ + R)/‖z‖ • z`, which adds `R`
to the norm of `z` and preserves its direction. -/
theorem isPreconnected_norm_gt {R : ℝ} (hR : 0 ≤ R) : IsPreconnected {z : ℂ | R < ‖z‖} := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hS : IsPreconnected ({z : ℂ | z ≠ 0}) := by
    have h := (Set.Countable.isConnected_compl_of_one_lt_rank hrank
      (Set.countable_singleton (0 : ℂ))).isPreconnected
    simpa only [compl_singleton_eq] using h
  have hcont : ContinuousOn (fun z : ℂ => ((‖z‖ + R)/‖z‖) • z) {z : ℂ | z ≠ 0} := by
    apply ContinuousOn.smul (f := fun z : ℂ => (‖z‖ + R)/‖z‖) (g := fun z : ℂ => z)
    · apply ContinuousOn.div
      · exact continuous_norm.continuousOn.add continuousOn_const
      · exact continuous_norm.continuousOn
      · intro z hz; exact norm_ne_zero_iff.mpr hz
    · exact continuousOn_id
  have himg : (fun z : ℂ => ((‖z‖ + R)/‖z‖) • z) '' {z : ℂ | z ≠ 0} = {z : ℂ | R < ‖z‖} := by
    apply Subset.antisymm
    · rintro w ⟨z, hz, rfl⟩
      change R < ‖((‖z‖ + R)/‖z‖) • z‖
      have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
      have hval : ‖((‖z‖ + R)/‖z‖) • z‖ = ‖z‖ + R := by
        rw [norm_smul,
          Real.norm_of_nonneg (div_nonneg (add_nonneg (norm_nonneg z) hR) (le_of_lt hzn))]
        exact div_mul_cancel₀ _ (ne_of_gt hzn)
      rw [hval]; linarith
    · intro w hw
      have hw' : R < ‖w‖ := hw
      have hwn : (0:ℝ) < ‖w‖ := lt_of_le_of_lt hR hw'
      have hfac : 0 ≤ (‖w‖ - R)/‖w‖ := div_nonneg (by linarith) (le_of_lt hwn)
      have hnorm : ‖((‖w‖ - R)/‖w‖) • w‖ = ‖w‖ - R := by
        rw [norm_smul, Real.norm_of_nonneg hfac]
        exact div_mul_cancel₀ _ (ne_of_gt hwn)
      refine ⟨((‖w‖ - R)/‖w‖) • w, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq]
        intro hz0
        rw [hz0, norm_zero] at hnorm
        linarith
      · change ((‖((‖w‖ - R)/‖w‖) • w‖ + R)/‖((‖w‖ - R)/‖w‖) • w‖) •
            (((‖w‖ - R)/‖w‖) • w) = w
        rw [hnorm, smul_smul]
        simp only [sub_add_cancel]
        have hcoef : (‖w‖ / (‖w‖ - R)) * ((‖w‖ - R)/‖w‖) = 1 := by
          rw [div_mul_div_comm, mul_comm (‖w‖) (‖w‖ - R)]
          exact div_self (mul_ne_zero (by linarith) (ne_of_gt hwn))
        rw [hcoef, one_smul]
  rw [← himg]
  exact hS.image _ hcont

theorem nonempty_planeSeparation (c : Work.Smooth.Jordan.PlaneCurve)
    (hsimple : Work.Smooth.Jordan.PlaneCurve.IsSimple c)
    (hatMost : ∀ x y z : ℂ, x ∉ c.trace → y ∉ c.trace → z ∉ c.trace →
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ y ∨
        connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ z ∨
        connectedComponentIn c.traceᶜ y = connectedComponentIn c.traceᶜ z)
    (hatLeast : ∃ x y : ℂ, x ∉ c.trace ∧ y ∉ c.trace ∧
      connectedComponentIn c.traceᶜ x ≠ connectedComponentIn c.traceᶜ y) :
    Nonempty (Work.Smooth.Jordan.PlaneSeparation c) := by
  obtain ⟨x0, y0, hx0, hy0, hne_xy⟩ := hatLeast
  have hFopen : IsOpen c.traceᶜ := c.isOpen_compl_trace
  have hx0F : x0 ∈ c.traceᶜ := hx0
  have hy0F : y0 ∈ c.traceᶜ := hy0
  -- The two connected components of the complement picked out by `hatLeast`.
  have hAne : (connectedComponentIn c.traceᶜ x0).Nonempty := ⟨x0, mem_connectedComponentIn hx0F⟩
  have hBne : (connectedComponentIn c.traceᶜ y0).Nonempty := ⟨y0, mem_connectedComponentIn hy0F⟩
  have hApre : IsPreconnected (connectedComponentIn c.traceᶜ x0) :=
    isPreconnected_connectedComponentIn
  have hBpre : IsPreconnected (connectedComponentIn c.traceᶜ y0) :=
    isPreconnected_connectedComponentIn
  have hAopen : IsOpen (connectedComponentIn c.traceᶜ x0) := hFopen.connectedComponentIn
  have hBopen : IsOpen (connectedComponentIn c.traceᶜ y0) := hFopen.connectedComponentIn
  -- Distinct components are disjoint.
  have hdisj : Disjoint (connectedComponentIn c.traceᶜ x0) (connectedComponentIn c.traceᶜ y0) :=
    Set.disjoint_left.mpr fun _ hzA hzB =>
      hne_xy ((connectedComponentIn_eq hzA).trans (connectedComponentIn_eq hzB).symm)
  -- `hatMost` says that the complement has no third component.
  have hUnion : connectedComponentIn c.traceᶜ x0 ∪ connectedComponentIn c.traceᶜ y0 = c.traceᶜ := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)
    · intro z hz
      rcases hatMost x0 y0 z hx0 hy0 hz with h | h | h
      · exact absurd h hne_xy
      · exact Or.inl (h ▸ mem_connectedComponentIn hz)
      · exact Or.inr (h ▸ mem_connectedComponentIn hz)
  -- The trace is compact, hence lies in a closed ball; the exterior of that ball is preconnected
  -- and contained in the complement.
  obtain ⟨R₀, hR₀⟩ := c.isCompact_trace.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : (0 : ℝ) ≤ R := le_max_right _ _
  have hR₀R : R₀ ≤ R := le_max_left _ _
  have htrace_sub : c.trace ⊆ Metric.closedBall (0 : ℂ) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall hR₀R)
  have hEpre : IsPreconnected {z : ℂ | R < ‖z‖} := isPreconnected_norm_gt hR0
  have hEsub : {z : ℂ | R < ‖z‖} ⊆ c.traceᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzt
    have h1 : ‖z‖ ≤ R := by
      have h2 := htrace_sub hzt
      rwa [Metric.mem_closedBall, dist_zero_right] at h2
    exact absurd hz (not_lt.mpr h1)
  -- A preconnected subset of the complement lies entirely in one of the two components.
  rcases hEpre.subset_or_subset hAopen hBopen hdisj (hEsub.trans (le_of_eq hUnion.symm)) with
    hEA | hEB
  · -- The exterior lies in the component of `x0`, so the other component is bounded.
    have hBball : connectedComponentIn c.traceᶜ y0 ⊆ Metric.closedBall (0 : ℂ) R := by
      intro z hzB
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hcon
      have hzE : z ∈ {z : ℂ | R < ‖z‖} := not_le.mp hcon
      exact (Set.disjoint_left.mp hdisj) (hEA hzE) hzB
    have hBbd : Bornology.IsBounded (connectedComponentIn c.traceᶜ y0) :=
      Metric.isBounded_closedBall.subset hBball
    exact ⟨{ simple := hsimple
             U := connectedComponentIn c.traceᶜ x0
             V := connectedComponentIn c.traceᶜ y0
             isOpen_U := hAopen
             isOpen_V := hBopen
             preconn_U := hApre
             preconn_V := hBpre
             nonempty_U := hAne
             nonempty_V := hBne
             disjoint_UV := hdisj
             union_eq := hUnion
             bounded_V := hBbd }⟩
  · -- The exterior lies in the component of `y0`, so the component of `x0` is bounded.
    have hAball : connectedComponentIn c.traceᶜ x0 ⊆ Metric.closedBall (0 : ℂ) R := by
      intro z hzA
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hcon
      have hzE : z ∈ {z : ℂ | R < ‖z‖} := not_le.mp hcon
      exact (Set.disjoint_left.mp hdisj) hzA (hEB hzE)
    have hAbd : Bornology.IsBounded (connectedComponentIn c.traceᶜ x0) :=
      Metric.isBounded_closedBall.subset hAball
    exact ⟨{ simple := hsimple
             U := connectedComponentIn c.traceᶜ y0
             V := connectedComponentIn c.traceᶜ x0
             isOpen_U := hBopen
             isOpen_V := hAopen
             preconn_U := hBpre
             preconn_V := hApre
             nonempty_U := hBne
             nonempty_V := hAne
             disjoint_UV := hdisj.symm
             union_eq := by rw [Set.union_comm]; exact hUnion
             bounded_V := hAbd }⟩

end Work.Smooth.JordanSeparation
