import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Jeps_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

/-! ## The shift is jointly continuous on `K × (ball)` -/

/-- The three-variable map `(z, θ, q) ↦ sPhi z θ q` is continuous on `K × closedBall 0 1`
whenever `K ⊆ Quad` (the only obstruction to the *global* continuity of `sPhi` is the possible
vanishing of `cos θ`, which cannot happen on the quadrant). -/
private theorem continuousOn_sPhi_prod {K : Set (ℝ × ℝ)} (hKQ : K ⊆ Work.FTS.StrongEps.Quad) :
    ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Work.FTS.StrongEps.sPhi x.1.1 x.1.2 x.2)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) := by
  have hproj : ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1.2)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) :=
    (continuous_snd.comp continuous_fst).continuousOn
  have htan : ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Real.tan x.1.2)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) := by
    refine Real.continuousOn_tan_Ioo.comp hproj ?_
    intro x hx
    simp only [Set.mem_prod] at hx
    simp only [Set.mem_Ioo]
    have h2 : x.1.2 ∈ Set.Ioo 0 (Real.pi / 2) :=
      (Work.FTS.StrongEps.mem_Quad.mp (hKQ hx.1)).2
    exact ⟨by linarith [h2.1, Real.pi_pos], by linarith [h2.2]⟩
  have h1 : ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Work.FTS.StrongEps.zShift x.1.1 x.2.1)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) := by
    simp only [Work.FTS.StrongEps.zShift]
    fun_prop
  have h2 : ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Work.FTS.StrongEps.thShift x.1.2 x.2.2)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) := by
    simp only [Work.FTS.StrongEps.thShift]
    exact Real.continuous_arctan.comp_continuousOn
      (htan.mul (by fun_prop : ContinuousOn
        (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Real.exp (-x.2.2))
          (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1)))
  have h := h1.prodMk h2
  refine h.congr ?_
  intro x _
  simp only [Work.FTS.StrongEps.sPhi, Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift]

/-- **The shift of the mollifier is uniformly close to the identity on a compact set.**  For every
compact `K` inside the open quadrant and every `η > 0` there is `δ > 0` such that for every
`p ∈ K` and every `q` with `‖q‖ ≤ δ`, the shifted point `sPhi p.1 p.2 q` is within `η` of `p`.

This is the Heine–Cantor statement for the joint continuity of `(p, q) ↦ sPhi p.1 p.2 q` on the
compact set `K × closedBall 0 1`, together with `sPhi p.1 p.2 0 = p`. -/
theorem exists_dist_sPhi_le {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.StrongEps.Quad) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ p ∈ K, ∀ q : ℝ × ℝ, ‖q‖ ≤ δ → dist (Work.FTS.StrongEps.sPhi p.1 p.2 q) p ≤ η := by
  have hsc : IsCompact (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) :=
    hK.prod (isCompact_closedBall 0 1)
  have huc : UniformContinuousOn
      (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Work.FTS.StrongEps.sPhi x.1.1 x.1.2 x.2)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) :=
    hsc.uniformContinuousOn_of_continuous (continuousOn_sPhi_prod hKQ)
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ, hδprop⟩ := huc η hη
  refine ⟨min δ 1, lt_min hδ one_pos, fun p hp q hq => ?_⟩
  have hqB : q ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans hq (min_le_right _ _)
  have h0B : (0 : ℝ × ℝ) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  have hdist : dist (p, q) (p, 0) ≤ δ := by
    rw [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg q)]
    exact le_trans hq (min_le_left _ _)
  have hres := hδprop (p, q) ⟨hp, hqB⟩ (p, 0) ⟨hp, h0B⟩ hdist
  have hp2 : p.2 ∈ Set.Ioo 0 (Real.pi / 2) := (Work.FTS.StrongEps.mem_Quad.mp (hKQ hp)).2
  have hz : Work.FTS.StrongEps.sPhi p.1 p.2 0 = p := by
    rw [Work.FTS.StrongEps.sPhi_zero hp2]
  rwa [hz] at hres

end Work.FTS.StrongEps.E5Aux
