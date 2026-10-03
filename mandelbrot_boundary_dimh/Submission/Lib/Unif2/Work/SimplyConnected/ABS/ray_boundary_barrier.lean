import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.barrier_of_sector
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.plane_ray_barrier

/-!
# The ray (slit) condition at a frontier point, and its barrier

`Work.SimplyConnected.ABS.HasSectorBoundary` records the *sector* (cone of positive angle) condition
of potential theory at a frontier point `p` of a region `U`, and
`Work.SimplyConnected.ABS.barrier_of_sector` turns it into a barrier in the sense required by
`Work.SimplyConnected.ABS.exists_isGreenOn_of_barriers`.

This module supplies the **degenerate** companion, needed at a frontier point where the local
complement of `U` is a *ray* (the cusp case of two tangent boundary circles):

`HasRayBoundary U p` says that, in some chart `c` around `p`, `U` avoids the ray through `p` in a
direction `d ≠ 0`, i.e. `c x - c p ≠ t • d` for `t ≥ 0`, `x ∈ U`.  `barrier_of_ray` turns it into a
barrier, using the plane ray barrier `Work.SimplyConnected.ABS.plane_ray_barrier`, by exactly the
argument of `barrier_of_sector`.

With this, *every* frontier point of a finite union of chart balls carries a barrier: see the header
of `plane_ray_barrier` for the local analysis (the sector case or the ray case, no general position
needed).
-/

namespace Work.SimplyConnected.ABS

open Set Filter
open scoped Topology Manifold ContDiff

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The ray (slit) condition at a frontier point `p` of `U`.**

There is a chart `c` (a member of the atlas), a neighbourhood `V` of `p` and a direction `d ≠ 0` such
that `U` avoids, near `p`, the ray through `p` in the direction `d`:

`∀ x ∈ U ∩ V, ∀ t ≥ 0, c x - c p ≠ t • d`.

This is the local model of the complement of a finite union of chart balls at a *tangency* point of
two of its boundary spheres (the two tangent half-balls have opposite outward normals, so the local
complement contains the common tangent-normal ray). -/
def HasRayBoundary (U : Set X) (p : X) : Prop :=
  ∃ (c : OpenPartialHomeomorph X ℂ) (V : Set X) (d : ℂ),
    c ∈ atlas ℂ X ∧ IsOpen V ∧ p ∈ V ∧ V ⊆ c.source ∧ p ∈ c.source ∧ d ≠ 0 ∧
      ∀ x ∈ U ∩ V, ∀ t : ℝ, 0 ≤ t → c x - c p ≠ t • d

/-- **The ray condition yields a barrier.**  If `U` is open, `p ∉ U` and `U` satisfies the ray
condition at `p`, then there are `u` and a neighbourhood `V` of `p` with `u` superharmonic on
`U ∩ V`, positive on `U ∩ V`, continuous on `V` and `u p = 0`. -/
theorem barrier_of_ray {U : Set X} {p : X} (hUo : IsOpen U) (hpU : p ∉ U)
    (h : HasRayBoundary U p) :
    ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (U ∩ V) ∧ (∀ x ∈ U ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0 := by
  obtain ⟨c, V, d, hcatlas, hVo, hpV, hVc, hpsrc, hd, hray⟩ := h
  obtain ⟨φ, hφcont, hφ0, hφpos, hφharm⟩ := plane_ray_barrier d hd
  have hcV : ContinuousOn (fun y : X => c y - c p) V :=
    (c.continuousOn.mono hVc).sub continuousOn_const
  have hcu : ContinuousOn (fun y : X => φ (c y - c p)) V := hφcont.comp_continuousOn hcV
  refine ⟨fun y : X => φ (c y - c p), V, hVo, hpV, ⟨?_, ?_⟩, ?_, hcu, ?_⟩
  · exact hcu.mono Set.inter_subset_right
  · -- superharmonicity at every point of `U ∩ V`
    intro x hx
    have hxsrc : x ∈ c.source := hVc hx.2
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp
      (InnerProductSpace.isOpen_setOfPred_harmonicAt φ) _ (hφharm _ (hray x hx))
    have hchart : Submission.SuperharmonicAtChart (fun y : X => φ (c y - c p)) c x :=
      superharmonicAtChart_comp_sub (a := c p) hxsrc hδ hδsub
    exact Submission.SuperharmonicAtChart.transport hxsrc (mem_chart_source ℂ x)
      (Submission.analyticAt_transition_of_mem_atlas hcatlas (chart_mem_atlas ℂ x))
      (Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ x) hcatlas)
      hchart
  · intro x hx
    exact hφpos _ (hray x hx)
  · simp [hφ0]

end

end Work.SimplyConnected.ABS
