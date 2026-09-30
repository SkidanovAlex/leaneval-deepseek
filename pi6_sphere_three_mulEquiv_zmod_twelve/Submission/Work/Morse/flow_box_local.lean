import Submission.Work.Morse.flow_basic

set_option synthInstance.maxHeartbeats 400000

/-!
# Local flow boxes on a smooth manifold

For a smooth vector field `v` on a manifold `M` (charted over `ℝⁿ`, without boundary), every point
lies in a *flow box*: an open neighbourhood `U` and a time `ε > 0` together with a map `Ψ` that is
jointly continuous on `Ioo (-ε) ε × U` and whose curves `t ↦ Ψ t x` are integral curves of `v`
starting at `x`.

The proof works in the chart at the base point `x₀`: the chart expression `chartVF v x₀` of the
vector field is `C¹` there, so `exists_flow_model` provides a jointly continuous flow of the
coordinate ODE; transporting it back through `(extChartAt _ x₀).symm` gives the flow box, using
`isMIntegralCurveOn_chartVF` to recognise the transported curve as an integral curve of `v`.
-/

open scoped Manifold ContDiff Topology
open Set Function Metric

namespace Work.Morse

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Local flow boxes, with the two chart ingredients (`chartVF` is `C¹` at the base point, and
solutions of the chart equation are integral curves) taken as hypotheses. -/
theorem flow_box_local_aux
    (v : (x : M) → TangentSpace (𝓡 n) x)
    (hCD : ∀ x₀ : M, ContDiffAt ℝ 1 (chartVF v x₀) (extChartAt (𝓡 n) x₀ x₀))
    (hODE : ∀ (x₀ : M) (γ : ℝ → M) (f : ℝ → EuclideanSpace ℝ (Fin n)) (s : Set ℝ),
      (∀ t ∈ s, γ t = (extChartAt (𝓡 n) x₀).symm (f t)) →
      (∀ t ∈ s, f t ∈ (extChartAt (𝓡 n) x₀).target) →
      (∀ t ∈ s, HasDerivAt f (chartVF v x₀ (f t)) t) →
      IsMIntegralCurveOn γ v s) :
    ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > 0, ∃ Ψ : ℝ → M → M, IsFlowBox v ε U Ψ := by
  classical
  intro x₀
  set e : PartialEquiv M (EuclideanSpace ℝ (Fin n)) := extChartAt (𝓡 n) x₀ with he
  have hT : IsOpen e.target := isOpen_extChartAt_target x₀
  have hcT : e x₀ ∈ e.target := mem_extChartAt_target x₀
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hcT)
  set ρ : ℝ := δ / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρT : Metric.closedBall (e x₀) ρ ⊆ e.target := by
    refine subset_trans (Metric.closedBall_subset_ball ?_) hδT
    rw [hρdef]; linarith
  obtain ⟨a, r, ε, α, ha0, haρ, hr0, hrρ, hε0, hερ, hcont, hprop⟩ :=
    exists_flow_model (hCD x₀) hρ0
  have haT : Metric.closedBall (e x₀) a ⊆ e.target :=
    subset_trans (Metric.closedBall_subset_closedBall haρ) hρT
  -- the flow box of the chart flow, transported to `M`
  set U : Set M := interior (e.source ∩ e ⁻¹' Metric.ball (e x₀) r) with hU
  have hUopen : IsOpen U := isOpen_interior
  have hx₀U : x₀ ∈ U := by
    rw [hU, mem_interior_iff_mem_nhds]
    exact Filter.inter_mem (extChartAt_source_mem_nhds x₀)
      ((continuousAt_extChartAt x₀).preimage_mem_nhds (Metric.ball_mem_nhds _ hr0))
  have hUsub : U ⊆ e.source := fun x hx ↦ (interior_subset hx).1
  have hUmem : ∀ x ∈ U, e x ∈ Metric.ball (e x₀) r := fun x hx ↦ (interior_subset hx).2
  let Ψ : ℝ → M → M := fun t x ↦ if hx : x ∈ U then e.symm (α (e x, t)) else x
  refine ⟨U, hUopen, hx₀U, ε, hε0, Ψ, ?_, ?_⟩
  · -- joint continuity on the strip
    have hsymm : ContinuousOn (fun y : EuclideanSpace ℝ (Fin n) ↦ e.symm y) e.target :=
      fun y hy ↦ (continuousAt_extChartAt_symm'' hy).continuousWithinAt
    have hcomp : ContinuousOn (fun p : ℝ × M ↦ e.symm (α (e p.2, p.1)))
        (Ioo (-ε) ε ×ˢ U) := by
      refine hsymm.comp ?_ ?_
      · refine hcont.comp ?_ ?_
        · exact (((continuousOn_extChartAt x₀).mono hUsub).comp continuousOn_snd
            (fun p hp ↦ hp.2)).prodMk continuousOn_fst
        · intro p hp
          exact ⟨Metric.ball_subset_closedBall (hUmem p.2 hp.2),
            Ioo_subset_Icc_self hp.1⟩
      · intro p hp
        exact haT (hprop (e p.2) (Metric.ball_subset_closedBall (hUmem p.2 hp.2)) |>.2.2 p.1
          (Ioo_subset_Icc_self hp.1))
    refine hcomp.congr fun p hp ↦ ?_
    show (if hx : p.2 ∈ U then e.symm (α (e p.2, p.1)) else p.2) = e.symm (α (e p.2, p.1))
    rw [dif_pos hp.2]
  · -- the curves are integral curves
    intro x hx
    have hxsrc : x ∈ e.source := hUsub hx
    have hex : e x ∈ Metric.closedBall (e x₀) r :=
      Metric.ball_subset_closedBall (hUmem x hx)
    have hpx := hprop (e x) hex
    constructor
    · show (if hx : x ∈ U then e.symm (α (e x, 0)) else x) = x
      rw [dif_pos hx, hpx.1]
      exact PartialEquiv.left_inv e hxsrc
    · have hmem : ∀ t ∈ Ioo (-ε) ε, α (e x, t) ∈ e.target := fun t ht ↦
        haT (hpx.2.2 t (Ioo_subset_Icc_self ht))
      have hder : ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt (fun t ↦ α (e x, t)) (chartVF v x₀ (α (e x, t))) t := fun t ht ↦
        (hpx.2.1 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      exact hODE x₀ (fun t ↦ Ψ t x) (fun t ↦ α (e x, t)) (Ioo (-ε) ε)
        (fun t _ ↦ by
          show (if hx : x ∈ U then e.symm (α (e x, t)) else x) = e.symm (α (e x, t))
          rw [dif_pos hx]) hmem hder

end Work.Morse
