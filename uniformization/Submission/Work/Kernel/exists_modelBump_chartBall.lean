import Mathlib

open scoped Manifold ContDiff Topology

open Set Metric Function

namespace Work.Kernel

/-- Existence of a smooth bump function on a Riemann surface which is `1` on the closed ball of
radius `r₁` in the chart at `y` and whose (closed) support is contained in the ball of radius `r₂`
in that chart (and hence in the source of the chart). -/
theorem exists_modelBump_chartBall {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ⊤ X]
    {y : X} {p : ℂ} {r₁ r₂ : ℝ} (h12 : r₁ < r₂) (hr₂ : 0 < r₂)
    (htgt : Metric.ball p r₂ ⊆ (chartAt ℂ y).target) :
    ∃ χ : X → ℝ, ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
        (((⊤ : ℕ∞) : WithTop ℕ∞)) χ ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ x, x ∈ (chartAt ℂ y).source → (chartAt ℂ y) x ∈ Metric.closedBall p r₁ → χ x = 1) ∧
      tsupport χ ⊆ (chartAt ℂ y).source ∩ (chartAt ℂ y) ⁻¹' Metric.ball p r₂ := by
  let c := chartAt ℂ y
  have hR : max r₁ 0 < r₂ := max_lt h12 hr₂
  let rIn : ℝ := (max r₁ 0 + r₂) / 2
  let rOut : ℝ := (rIn + r₂) / 2
  have hrIn_pos : 0 < rIn := by
    show (0 : ℝ) < (max r₁ 0 + r₂) / 2
    linarith [le_max_right r₁ 0]
  have hrIn_lt_rOut : rIn < rOut := by
    show (max r₁ 0 + r₂) / 2 < ((max r₁ 0 + r₂) / 2 + r₂) / 2
    linarith [hR]
  have hrOut_lt : rOut < r₂ := by
    show ((max r₁ 0 + r₂) / 2 + r₂) / 2 < r₂
    linarith [hR]
  have hr₁_le : r₁ ≤ rIn := by
    show r₁ ≤ (max r₁ 0 + r₂) / 2
    linarith [le_max_left r₁ 0, h12]
  let f : ContDiffBump p := ⟨rIn, rOut, hrIn_pos, hrIn_lt_rOut⟩
  have hball_sub : closedBall p rOut ⊆ c.target :=
    fun z hz => htgt (closedBall_subset_ball hrOut_lt hz)
  let χ : X → ℝ := c.source.indicator (fun z => f (c z))
  -- the support of `χ` is the preimage of the open `rOut`-ball, intersected with the chart source
  have hsupp : Function.support χ = c.source ∩ c ⁻¹' ball p rOut := by
    rw [support_indicator]
    rw [show Function.support (fun z => f (c z)) = c ⁻¹' Function.support f from ?_]
    · rw [f.support_eq]
    · rw [show (fun z => f (c z)) = (↑f ∘ (↑c : X → ℂ)) from rfl]
      rw [support_comp_eq_preimage]
  -- the closure of the chart ball is contained in the chart source, since it is a compact subset of
  -- the chart target
  have hT_closed : IsClosed (c.symm '' closedBall p rOut) :=
    ((isCompact_closedBall p rOut).image_of_continuousOn
      (c.continuousOn_symm.mono hball_sub)).isClosed
  have hsupp_sub : Function.support χ ⊆ c.symm '' closedBall p rOut := by
    rw [hsupp]
    rintro x ⟨hx, hxd⟩
    exact ⟨c x, ball_subset_closedBall hxd, c.left_inv hx⟩
  have htsupp_sub : tsupport χ ⊆ c.symm '' closedBall p rOut :=
    closure_minimal hsupp_sub hT_closed
  have hT_sub : c.symm '' closedBall p rOut ⊆ c.source ∩ c ⁻¹' ball p r₂ := by
    rintro z ⟨q, hq, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← PartialHomeomorph.symm_image_target_eq_source]
      exact ⟨q, hball_sub hq, rfl⟩
    · show c (c.symm q) ∈ ball p r₂
      rw [c.right_inv (hball_sub hq)]
      exact closedBall_subset_ball hrOut_lt hq
  have htsupp : tsupport χ ⊆ c.source ∩ c ⁻¹' ball p r₂ := htsupp_sub.trans hT_sub
  have hsrc : tsupport χ ⊆ c.source := fun x hx => (hT_sub (htsupp_sub hx)).1
  refine ⟨χ, ?_, ?_, ?_, ?_, htsupp⟩
  · -- smoothness: use `contMDiff_of_tsupport`; on the chart source, `χ = f ∘ c` and both are smooth
    refine contMDiff_of_tsupport fun x hx => ?_
    have hxsrc : x ∈ c.source := hsrc hx
    have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) c x :=
      ((contMDiffOn_chart (I := modelWithCornersSelf ℝ ℂ) (x := y)).of_le le_top).contMDiffAt
        (c.open_source.mem_nhds hxsrc)
    have hfb : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => f z) (c x) :=
      ((f.contDiff (n := ⊤)).contDiffAt).contMDiffAt
    have hcomp : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => f (c z)) x :=
      hfb.comp x hchart
    have hEqOn : Set.EqOn χ (fun z => f (c z)) c.source := fun z hz => indicator_of_mem hz _
    exact hcomp.congr_of_eventuallyEq (hEqOn.eventuallyEq_of_mem (c.open_source.mem_nhds hxsrc))
  · intro x
    by_cases hx : x ∈ c.source
    · rw [show χ x = f (c x) from indicator_of_mem hx _]; exact f.nonneg
    · rw [show χ x = 0 from indicator_of_notMem hx _]
  · intro x
    by_cases hx : x ∈ c.source
    · rw [show χ x = f (c x) from indicator_of_mem hx _]; exact f.le_one
    · rw [show χ x = 0 from indicator_of_notMem hx _]; exact zero_le_one
  · intro x hxsrc hxball
    rw [show χ x = f (c x) from indicator_of_mem hxsrc _]
    exact f.one_of_mem_closedBall (closedBall_subset_closedBall hr₁_le hxball)

end Work.Kernel
