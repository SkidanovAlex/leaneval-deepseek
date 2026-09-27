import Mathlib
import Submission.Work.Whitney.SmoothArc.Bump

/-!
# Moving the endpoint of a chart ball, on a manifold

The manifold form of the bump translation: there is a universal constant `ε > 0` such that for
every chart `c` of a smooth manifold, base point `y ∈ c.source` and radius `R > 0` with
`closedBall (c y) R ⊆ c.target`, and every `z ∈ c.source` with `‖c z - c y‖ < ε * R`, there is a
smooth injective self-map `ψ` of the manifold with `ψ y = z`, `ψ = id` outside the chart ball of
radius `R` around `y`, and `ψ` mapping that ball into itself.
-/

namespace Work.Whitney

open Set Metric Function
open scoped Manifold ContDiff

/-- **The bump translation on a manifold.** -/
theorem exists_contMDiff_injective_bump {n : ℕ} :
    ∃ ε > 0, ∀ {M : Type*} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M] [T2Space M]
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ c c.source →
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ c.symm c.target →
      ∀ (y : M), y ∈ c.source → ∀ (R : ℝ), 0 < R →
      Metric.closedBall (c y) R ⊆ c.target →
      ∀ z : M, z ∈ c.source → ‖c z - c y‖ < ε * R →
      ∃ ψ : M → M,
        ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ ψ ∧
        Function.Injective ψ ∧
        (∀ w : M, w ∉ c.symm '' Metric.ball (c y) R → ψ w = w) ∧
        ψ y = z ∧
        ψ '' (c.symm '' Metric.ball (c y) R) ⊆ c.symm '' Metric.ball (c y) R := by
  classical
  obtain ⟨κ, hκpos, hκ⟩ := exists_bumpTranslation (n := n)
  refine ⟨κ, hκpos, ?_⟩
  intro M _ _ _ _ c hc hcs y hy R hR hclosed z hz hzd
  obtain ⟨Ψ, hΨc, hΨinj, hΨu, hΨid, hΨball⟩ := hκ (c y) R hR (c z - c y) hzd
  have hΨmd : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Ψ :=
    contMDiff_iff_contDiff.mpr hΨc
  have hΨcy : Ψ (c y) = c z := by rw [hΨu]; abel
  have hmemT : ∀ u ∈ Metric.ball (c y) R, u ∈ c.target :=
    fun u hu => hclosed (Metric.ball_subset_closedBall hu)
  set A : Set M := c.symm '' Metric.ball (c y) R with hA
  let ψ : M → M := fun w => if h : w ∈ c.source then c.symm (Ψ (c w)) else w
  have hψeq : ∀ w, w ∈ c.source → ψ w = c.symm (Ψ (c w)) := by
    intro w hw; simp only [ψ, dif_pos hw]
  have injOn_symm : InjOn c.symm c.target := by
    have h := c.symm.injOn
    rwa [OpenPartialHomeomorph.symm_source] at h
  have hΨmem : ∀ w ∈ c.source, Ψ (c w) ∈ c.target := by
    intro w hw
    by_cases hd : dist (c w) (c y) < R
    · exact hclosed (Metric.ball_subset_closedBall (Metric.mem_ball.mpr (hΨball (c w) hd)))
    · have h0 : Ψ (c w) = c w := hΨid (c w) (by push Not at hd; linarith)
      rw [h0]; exact c.map_source hw
  have hψA : ψ '' A ⊆ A := by
    rintro _ ⟨w, ⟨u, hu, hwu⟩, rfl⟩
    have hws : w ∈ c.source := hwu ▸ c.map_target (hmemT u hu)
    have hcw : c w = u := by rw [← hwu, c.right_inv (hmemT u hu)]
    refine ⟨Ψ (c w), Metric.mem_ball.mpr (hΨball (c w) (by rw [hcw]; exact Metric.mem_ball.mp hu)), ?_⟩
    rw [hψeq w hws]
  have hinjA : InjOn ψ A := by
    rintro w ⟨u, hu, hwu⟩ w' ⟨u', hu', hwu'⟩ heq
    have hws : w ∈ c.source := hwu ▸ c.map_target (hmemT u hu)
    have hw's : w' ∈ c.source := hwu' ▸ c.map_target (hmemT u' hu')
    rw [hψeq w hws, hψeq w' hw's] at heq
    exact c.injOn hws hw's (hΨinj (injOn_symm (hΨmem w hws) (hΨmem w' hw's) heq))
  have hψidA : ∀ w : M, w ∉ A → ψ w = w := by
    intro w hwA
    by_cases hws : w ∈ c.source
    · have hcw : c w ∉ Metric.ball (c y) R := fun hmem => hwA ⟨c w, hmem, c.left_inv hws⟩
      have : Ψ (c w) = c w := hΨid (c w) (by
        have := not_lt.mp (fun h => hcw (Metric.mem_ball.mpr h)); linarith)
      rw [hψeq w hws, this, c.left_inv hws]
    · simp only [ψ, dif_neg hws]
  have hinjψ : Function.Injective ψ := by
    intro w w' h
    by_cases hw : w ∈ A
    · by_cases hw' : w' ∈ A
      · exact hinjA hw hw' h
      · have hmem : ψ w' ∈ A := h ▸ hψA ⟨w, hw, rfl⟩
        rw [hψidA w' hw'] at hmem
        exact absurd hmem hw'
    · by_cases hw' : w' ∈ A
      · have hmem : ψ w ∈ A := h ▸ hψA ⟨w', hw', rfl⟩
        rw [hψidA w hw] at hmem
        exact absurd hmem hw
      · rw [hψidA w hw, hψidA w' hw'] at h; exact h
  refine ⟨ψ, ?_, hinjψ, hψidA, ?_, hψA⟩
  · have h1 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ (fun w : M => Ψ (c w)) c.source :=
      hΨmd.contMDiffOn (s := univ) |>.comp hc (fun _ _ => Set.mem_univ _)
    have h2 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
        (fun w : M => c.symm (Ψ (c w))) c.source :=
      hcs.comp h1 (fun w hw => hΨmem w hw)
    have h3 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ ψ c.source :=
      h2.congr (fun w hw => hψeq w hw)
    have hclosedA : IsClosed (c.symm '' Metric.closedBall (c y) R) :=
      ((isCompact_closedBall (c y) R).image_of_continuousOn (c.continuousOn_symm.mono hclosed)).isClosed
    have h4 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ ψ
        (c.symm '' Metric.closedBall (c y) R)ᶜ :=
      contMDiff_id.contMDiffOn.congr (fun w hw => by
        refine hψidA w (fun hmem => hw ?_)
        rcases hmem with ⟨u, hu, hwu⟩
        exact ⟨u, Metric.ball_subset_closedBall hu, hwu⟩)
    have hcover : c.source ∪ (c.symm '' Metric.closedBall (c y) R)ᶜ = univ := by
      ext w
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
      by_cases hw : w ∈ c.symm '' Metric.closedBall (c y) R
      · left; rcases hw with ⟨u, hu, hwu⟩; rw [← hwu]; exact c.map_target (hclosed hu)
      · exact Or.inr hw
    rw [← contMDiffOn_univ, ← hcover]
    exact h3.union_of_isOpen h4 c.open_source hclosedA.isOpen_compl
  · have : ψ y = c.symm (Ψ (c y)) := hψeq y hy
    rw [this, hΨcy]; exact c.left_inv hz

end Work.Whitney
