import Submission.Work.PlaneSlice.Transversality
import Submission.Work.Smooth.SphereJordan.jsepExists
import Submission.Work.Smooth.SphereJordan.Caratheodory.TopologyAux
import Submission.Work.Smooth.Schoenflies.PlaneJordanDataRel
import Submission.Work.Smooth.Schoenflies.ConvexRel

/-!
# Elementary plane Jordan topology used by the plane slicing

This file collects the few facts about the two sides of a simple closed plane curve which the
construction of the plane slicing of a convex planar region needs, in the vocabulary of
`Work.Smooth.Jordan.PlaneSeparation` / `Work.Smooth.Jordan.PlaneSchoenflies` (curves of class
`C⁰`, which is what the level-set classification of the workspace produces).

## Main results

* `Work.PlaneSlice.preconnected_subset_of_boundedSide` — a preconnected set avoiding the trace and
  meeting the bounded side lies in it;
* `Work.PlaneSlice.nested_boundedSide` — the bounded side of a curve lying in the bounded side of
  another is contained in it (the nesting of the inside regions of disjoint Jordan curves);
* `Work.PlaneSlice.boundedSide_subset_of_convex` — the bounded side of a Jordan curve lies in every
  convex set containing the curve (the convexity form of planar Jordan–Schoenflies, in the
  `PlaneSeparation` vocabulary);
* `Work.PlaneSlice.closure_boundedSide_eq` — the closure of the bounded side is the side together
  with the curve.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PlaneSlice

noncomputable section

/-- **A preconnected set avoiding the trace of a Jordan curve and meeting its bounded side lies in
it.** -/
theorem preconnected_subset_of_boundedSide {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) {K : Set ℂ} (hK : IsPreconnected K)
    (hdisj : Disjoint K c.trace) (hmeet : (K ∩ S.V).Nonempty) : K ⊆ S.V := by
  have hsub : K ⊆ c.traceᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    exact fun hxt => Set.disjoint_left.mp hdisj hx hxt
  rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S hK hsub with h | h
  · obtain ⟨y, hyK, hyV⟩ := hmeet
    exact absurd (h hyK) (Set.disjoint_left.mp S.disjoint_UV · hyV)
  · exact h

/-- **The bounded side of a curve contained in the bounded side of another is contained in it.**

If the trace of `c₂` lies in the bounded side `S₁.V` of the separation `S₁` of `c₁`, then the whole
bounded side `S₂.V` of `c₂` lies in `S₁.V`: two disjoint Jordan curves in the plane are nested or
disjoint, and here they are nested. -/
theorem nested_boundedSide {c₁ c₂ : Work.Smooth.Jordan.PlaneCurve}
    (S₁ : Work.Smooth.Jordan.PlaneSeparation c₁) (S₂ : Work.Smooth.Jordan.PlaneSeparation c₂)
    (hsub : c₂.trace ⊆ S₁.V) : S₂.V ⊆ S₁.V := by
  obtain ⟨J₁⟩ := Work.Smooth.SphereJordan.exists_jsep c₁ S₁.simple
  obtain ⟨J₂⟩ := Work.Smooth.SphereJordan.exists_jsep c₂ S₂.simple
  have hP₁ : S₁.V = J₁.V := by
    rcases Work.Smooth.Jordan.plane_separation_eq S₁ (J₁.toPlaneSeparation S₁.simple) with
      ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exfalso
      -- `S₁.V` is bounded while `J₁.U` is not
      obtain ⟨r, hr⟩ := S₁.bounded_V.subset_closedBall (0 : ℂ)
      obtain ⟨x, hxU, hxr⟩ :=
        Work.Smooth.Jordan.plane_separation_unbounded (J₁.toPlaneSeparation S₁.simple) (r + 1)
      have hxV : x ∈ S₁.V := by rw [h]; exact hxU
      have h1 : ‖x‖ ≤ r := by
        have := hr hxV
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      have h2 : r + 1 ≤ ‖x‖ := hxr
      linarith
  have hP₂ : S₂.V = J₂.V := by
    rcases Work.Smooth.Jordan.plane_separation_eq S₂ (J₂.toPlaneSeparation S₂.simple) with
      ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exfalso
      obtain ⟨r, hr⟩ := S₂.bounded_V.subset_closedBall (0 : ℂ)
      obtain ⟨x, hxU, hxr⟩ :=
        Work.Smooth.Jordan.plane_separation_unbounded (J₂.toPlaneSeparation S₂.simple) (r + 1)
      have hxV : x ∈ S₂.V := by rw [h]; exact hxU
      have h1 : ‖x‖ ≤ r := by
        have := hr hxV
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      have h2 : r + 1 ≤ ‖x‖ := hxr
      linarith
  rw [hP₂, hP₁]
  refine Work.Smooth.SphereJordan.Caratheodory.JSep.V_subset_of_disjoint_trace J₁ J₂ ?_
  rw [Set.disjoint_left]
  intro z hz hzU
  have hzV : z ∈ J₁.V := by rw [← hP₁]; exact hsub hz
  exact Set.disjoint_left.mp J₁.disjoint_UV hzU hzV

/-- **The bounded side of a Jordan curve lies in every convex set containing the curve.**

This is the convexity form of the planar Jordan curve theorem in the `PlaneSeparation` vocabulary:
a point of the bounded side lying outside a convex set `D` containing the curve would be contracted
away from the curve by the straight-line homotopy inside `D`, contradicting the Jordan curve
theorem (`Work.Smooth.Schoenflies.not_nullHomotopicRel_of_mem_V`). -/
theorem boundedSide_subset_of_convex {c : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSchoenflies c) {D : Set ℂ} (hD : Convex ℝ D)
    (hsub : c.trace ⊆ D) : h.V ⊆ D := by
  intro x hxV
  by_contra hxD
  exact Work.Smooth.Schoenflies.not_nullHomotopicRel_of_mem_V h hxV
    (Work.Smooth.Schoenflies.nullHomotopicRel_of_convex hD hxD c.cont c.periodic
      (fun t => hsub (Set.mem_range_self t)))

/-- **The closure of the bounded side of a Schoenflies curve is the side together with the
curve.** -/
theorem closure_boundedSide_eq {c : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSchoenflies c) : closure h.V = h.V ∪ c.trace := by
  have hsphere : h.e '' {z : Work.InnermostDisk.Disc | ‖(z : ℂ)‖ = 1} = c.trace := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨θ, rfl⟩ := Work.Smooth.Plane.exists_circlePoint_eq_of_norm_eq_one hz
      exact ⟨θ, (h.boundary θ).symm⟩
    · rintro _ ⟨θ, rfl⟩
      refine ⟨Work.CoreTopology.circlePoint θ, ?_, h.boundary θ⟩
      show ‖((Work.CoreTopology.circlePoint θ : Work.InnermostDisk.Disc) : ℂ)‖ = 1
      rw [Work.CoreTopology.circlePoint_coe]
      exact Complex.norm_exp_ofReal_mul_I θ
  have hunion : h.e '' (Set.univ : Set Work.InnermostDisk.Disc) =
      h.e '' {z : Work.InnermostDisk.Disc | ‖(z : ℂ)‖ < 1} ∪
        h.e '' {z : Work.InnermostDisk.Disc | ‖(z : ℂ)‖ = 1} := by
    rw [← Set.image_union]
    congr 1
    ext z
    constructor
    · intro _
      rcases lt_or_eq_of_le (by simpa using Metric.mem_closedBall.mp z.2 : ‖(z : ℂ)‖ ≤ 1) with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq
    · intro _; exact Set.mem_univ z
  calc closure h.V = Set.range h.e := h.range_e.symm
    _ = h.e '' (Set.univ : Set Work.InnermostDisk.Disc) := Set.image_univ.symm
    _ = h.e '' {z : Work.InnermostDisk.Disc | ‖(z : ℂ)‖ < 1} ∪
          h.e '' {z : Work.InnermostDisk.Disc | ‖(z : ℂ)‖ = 1} := hunion
    _ = h.V ∪ c.trace := by
        rw [Work.Smooth.Jordan.plane_schoenflies_openDisc_eq h, hsphere]

/-- **The bounded side of a Schoenflies curve is the image of the open disc under the spanning
embedding.** -/
theorem image_openDisc_eq_boundedSide {c : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSchoenflies c) :
    h.e '' {z : Work.InnermostDisk.Disc | ‖(z : ℂ)‖ < 1} = h.V :=
  Work.Smooth.Jordan.plane_schoenflies_openDisc_eq h

end

end Work.PlaneSlice
