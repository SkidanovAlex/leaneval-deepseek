import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.injOn_circlePoint
import Submission.Work.Smooth.SphereJordan.annulusSchoenflies_of_plain
import Submission.Work.Smooth.SphereJordan.disc_image_open_of_injective

/-!
# The boundary curve of an injective disc map, and its boundary arcs

This small module fixes the vocabulary shared by the "theta graph" lemmas of the planar annulus
theorem:

* `discCurve F` — the plane curve `θ ↦ F (e^{iθ})` traced by the boundary circle of a continuous
  injection `F : 𝔻 → ℂ`;
* `discArc F x y` — the arc `t ↦ F (e^{i (x + t (y - x))})` of that curve between the boundary
  parameters `x` and `y`.

Everything here is elementary; the mathematical content (that the image of `F` is the closure of
the bounded side of `discCurve F`) is in the companion module `discCurveSpans`.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **The plane curve traced by the boundary circle of a continuous disc map.** -/
def discCurve (F : C(Work.Smooth.SphereJordan.Disc, ℂ)) : Work.Smooth.Jordan.PlaneCurve where
  γ := fun θ => F (Work.Smooth.Jordan.circlePoint θ)
  cont := F.continuous.comp Work.Smooth.SphereJordan.continuous_circlePoint
  periodic := by
    intro θ
    exact congrArg F (Work.Smooth.SphereJordan.circlePoint_add_two_pi θ)

@[simp] theorem discCurve_apply (F : C(Work.Smooth.SphereJordan.Disc, ℂ)) (θ : ℝ) :
    (discCurve F).γ θ = F (Work.Smooth.Jordan.circlePoint θ) := rfl

/-- The boundary curve of an injective disc map is simple. -/
theorem discCurve_isSimple {F : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hF : Function.Injective F) : (discCurve F).IsSimple :=
  fun _a ha _b hb hab => Work.Smooth.SphereJordan.injOn_circlePoint ha hb (hF hab)

/-- **The boundary arc** of the disc `range F` between the boundary parameters `x` and `y`. -/
def discArc (F : C(Work.Smooth.SphereJordan.Disc, ℂ)) (x y : ℝ) :
    C(Set.Icc (0 : ℝ) 1, ℂ) :=
  ⟨fun t => F (Work.Smooth.Jordan.circlePoint (x + (t : ℝ) * (y - x))),
    F.continuous.comp (Work.Smooth.SphereJordan.continuous_circlePoint.comp
      (continuous_const.add (continuous_subtype_val.mul continuous_const)))⟩

@[simp] theorem discArc_apply (F : C(Work.Smooth.SphereJordan.Disc, ℂ)) (x y : ℝ)
    (t : Set.Icc (0 : ℝ) 1) :
    discArc F x y t = F (Work.Smooth.Jordan.circlePoint (x + (t : ℝ) * (y - x))) := rfl

theorem discArc_zero (F : C(Work.Smooth.SphereJordan.Disc, ℂ)) (x y : ℝ) :
    discArc F x y ⟨0, by norm_num⟩ = F (Work.Smooth.Jordan.circlePoint x) := by
  simp [discArc]

theorem discArc_one (F : C(Work.Smooth.SphereJordan.Disc, ℂ)) (x y : ℝ) :
    discArc F x y ⟨1, by norm_num⟩ = F (Work.Smooth.Jordan.circlePoint y) := by
  simp [discArc]

theorem discArc_trace_subset (F : C(Work.Smooth.SphereJordan.Disc, ℂ)) (x y : ℝ) :
    Set.range (discArc F x y) ⊆ (discCurve F).trace := by
  rintro _ ⟨t, rfl⟩
  exact ⟨x + (t : ℝ) * (y - x), rfl⟩

/-! ## Boundary points of the image of a disc map -/

/-- The norm of a point of the model disc is at most one. -/
theorem discCurve_norm_coe_le_one (z : Work.Smooth.SphereJordan.Disc) : ‖(z : ℂ)‖ ≤ 1 := by
  have h := z.2
  rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h

/-- **The frontier of the image of an injective disc map is traced by its boundary curve.** -/
theorem discCurve_frontier_subset_trace {F : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hF : Function.Injective F) :
    frontier (Set.range (fun z : Work.Smooth.SphereJordan.Disc => (F z : ℂ))) ⊆
      (discCurve F).trace := by
  intro x hx
  have hclosed : IsClosed (Set.range (fun z : Work.Smooth.SphereJordan.Disc => (F z : ℂ))) :=
    (isCompact_range F.continuous).isClosed
  have hxcl : x ∈ Set.range (fun z : Work.Smooth.SphereJordan.Disc => (F z : ℂ)) := by
    rw [← hclosed.closure_eq]
    exact hx.1
  obtain ⟨z, rfl⟩ := hxcl
  have hz : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 := by
    by_contra hne
    have hlt : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 :=
      lt_of_le_of_ne (discCurve_norm_coe_le_one z) hne
    have hmem : F z ∈ openImage F := ⟨z, hlt, rfl⟩
    have hopen : IsOpen (openImage F) := openImage_isOpen_of_injective F hF
    have hsub : openImage F ⊆
        interior (Set.range (fun z : Work.Smooth.SphereJordan.Disc => (F z : ℂ))) :=
      interior_maximal (by rintro y ⟨z, -, rfl⟩; exact ⟨z, rfl⟩) hopen
    exact hx.2 (hsub hmem)
  obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
  exact ⟨θ, by rw [discCurve_apply, hθ]⟩

end

end Work.Smooth.SphereJordan
