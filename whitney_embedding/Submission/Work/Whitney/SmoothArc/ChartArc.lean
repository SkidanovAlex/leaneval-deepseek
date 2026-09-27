import Mathlib
import Submission.Work.Whitney.SmoothArc.Bump

/-!
# A smooth arc inside a chart ball

Given a chart `c` and two points `a`, `b` whose images lie in a small ball inside `c.target`, there
is a smooth arc from `a` to `b` whose whole image lies in a larger chart ball.  The construction
uses a smooth retraction of the model space onto the ball, so that the obvious linear segment
between `c a` and `c b` is well defined and smooth on all of `ℝ`.
-/

namespace Work.Whitney

open Set Metric Function
open scoped Manifold ContDiff

/-- **A smooth arc between two points of a chart ball.** -/
theorem exists_contMDiff_chartArc {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hcs : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ c.symm c.target)
    {y : M} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₁₂ : R₁ < R₂)
    (hclosed : Metric.closedBall (c y) R₂ ⊆ c.target)
    {a b : M} (ha : a ∈ c.source) (hb : b ∈ c.source) (hab : a ≠ b)
    (hca : c a ∈ Metric.closedBall (c y) R₁) (hcb : c b ∈ Metric.closedBall (c y) R₁) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ,ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ γ ∧
      γ 0 = a ∧ γ 1 = b ∧ Set.InjOn γ (Set.Icc (0:ℝ) 1) ∧
      (∀ t : ℝ, γ t ∈ c.symm '' Metric.closedBall (c y) R₂) := by
  classical
  have hR21 : 0 < R₂^2 - R₁^2 := by nlinarith
  let σ : EuclideanSpace ℝ (Fin n) → ℝ := fun v =>
    Real.smoothTransition ((R₂^2 - ‖v - c y‖^2)/(R₂^2 - R₁^2))
  let r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun v => c y + σ v • (v - c y)
  have hσsmooth : ContDiff ℝ ∞ σ := by
    have hg : ContDiff ℝ ∞
        (fun v : EuclideanSpace ℝ (Fin n) => (R₂^2 - ‖v - c y‖^2)/(R₂^2 - R₁^2)) := by
      apply ContDiff.div_const
      exact contDiff_const.sub (ContDiff.norm_sq ℝ (contDiff_id.sub contDiff_const))
    exact (Real.smoothTransition.contDiff (n := ⊤)).comp hg
  have hσ1 : ∀ v ∈ Metric.closedBall (c y) R₁, σ v = 1 := by
    intro v hv
    have h1 : ‖v - c y‖^2 ≤ R₁^2 := by
      have h2 := Metric.mem_closedBall.mp hv
      rw [dist_eq_norm] at h2
      nlinarith [norm_nonneg (v - c y)]
    have h2 : 1 ≤ (R₂^2 - ‖v - c y‖^2)/(R₂^2 - R₁^2) := by
      rw [le_div_iff₀ hR21]; linarith
    exact Real.smoothTransition.one_of_one_le h2
  have hσ0 : ∀ v, R₂^2 ≤ ‖v - c y‖^2 → σ v = 0 := by
    intro v hv
    have h2 : (R₂^2 - ‖v - c y‖^2)/(R₂^2 - R₁^2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hR21.le
    exact Real.smoothTransition.zero_of_nonpos h2
  have hσle : ∀ v, ‖σ v‖ ≤ 1 := by
    intro v
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hr_mem : ∀ v, r v ∈ Metric.closedBall (c y) R₂ := by
    intro v
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h2 : r v - c y = σ v • (v - c y) := by simp only [r]; abel
    rw [h2, norm_smul]
    by_cases h3 : (R₂^2 : ℝ) ≤ ‖v - c y‖^2
    · rw [hσ0 v h3]; simp; linarith
    · push Not at h3
      have hr1 : ‖v - c y‖ < R₂ := by nlinarith [norm_nonneg (v - c y)]
      calc ‖σ v‖ * ‖v - c y‖ ≤ 1 * ‖v - c y‖ :=
            mul_le_mul_of_nonneg_right (hσle v) (norm_nonneg _)
        _ ≤ R₂ := by linarith
  have hr_smooth : ContDiff ℝ ∞ r := by
    have h1 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => σ v • (v - c y)) :=
      hσsmooth.smul (contDiff_id.sub contDiff_const)
    exact contDiff_const.add h1
  have hseg : ∀ s ∈ Set.Icc (0:ℝ) 1, c a + s • (c b - c a) ∈ Metric.closedBall (c y) R₁ :=
    fun s hs => (convex_closedBall (c y) R₁).add_smul_mem hca (by simpa using hcb) hs
  have hrseg : ∀ s ∈ Set.Icc (0:ℝ) 1, r (c a + s • (c b - c a)) = c a + s • (c b - c a) := by
    intro s hs
    simp only [r, hσ1 _ (hseg s hs), one_smul]
    abel
  have hseg0 : r (c a) = c a := by
    have h := hrseg 0 (by norm_num); simpa using h
  have hseg1 : r (c b) = c b := by
    have h := hrseg 1 (by norm_num)
    rw [one_smul] at h
    rw [show c a + (c b - c a) = c b from by abel] at h
    exact h
  refine ⟨fun t => c.symm (r (c a + t • (c b - c a))), ?_, ?_, ?_, ?_, ?_⟩
  · have hinner : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun t : ℝ => r (c a + t • (c b - c a))) := by
      rw [contMDiff_iff_contDiff]
      exact hr_smooth.comp (by fun_prop)
    exact hcs.comp_contMDiff hinner (fun t => hclosed (hr_mem _))
  · show c.symm (r (c a + (0:ℝ) • (c b - c a))) = a
    rw [zero_smul, add_zero, hseg0]
    exact c.left_inv ha
  · show c.symm (r (c a + (1:ℝ) • (c b - c a))) = b
    rw [one_smul, show c a + (c b - c a) = c b from by abel, hseg1]
    exact c.left_inv hb
  · intro s hs t ht hst
    beta_reduce at hst
    rw [hrseg s hs, hrseg t ht] at hst
    have hinj : InjOn c.symm c.target := by
      have h := c.symm.injOn
      rwa [OpenPartialHomeomorph.symm_source] at h
    have h1 : c a + s • (c b - c a) = c a + t • (c b - c a) :=
      hinj (hclosed (Metric.closedBall_subset_closedBall hR₁₂.le (hseg s hs)))
        (hclosed (Metric.closedBall_subset_closedBall hR₁₂.le (hseg t ht))) hst
    have h2 : (s - t) • (c b - c a) = 0 := by
      rw [sub_smul]; exact sub_eq_zero.mpr (add_left_cancel h1)
    have h3 : c b - c a ≠ 0 := by
      intro h
      exact hab (c.injOn ha hb (sub_eq_zero.mp h).symm)
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h h3
  · intro t
    exact ⟨r (c a + t • (c b - c a)), hr_mem _, rfl⟩

end Work.Whitney
