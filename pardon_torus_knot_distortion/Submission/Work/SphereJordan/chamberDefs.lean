import Mathlib
import Submission.Work.Smooth.Jordan.Separation

namespace Work.SphereJordan

open Set

noncomputable section

/-- The component of `a` in the part of the trace inside the ball `ball p ε`. -/
def traceComponent (γ : Work.Smooth.Jordan.PlaneCurve) (p : ℂ) (ε : ℝ) (a : ℂ) : Set ℂ :=
  connectedComponentIn (γ.trace ∩ Metric.ball p ε) a

/-- The ball with all trace-components other than that of `a` deleted. -/
def sideChamber (γ : Work.Smooth.Jordan.PlaneCurve) (p : ℂ) (ε : ℝ) (a : ℂ) : Set ℂ :=
  Metric.ball p ε \ ((γ.trace ∩ Metric.ball p ε) \ traceComponent γ p ε a)

theorem traceComponent_subset (γ : Work.Smooth.Jordan.PlaneCurve) (p : ℂ) (ε : ℝ) (a : ℂ) :
    traceComponent γ p ε a ⊆ γ.trace ∩ Metric.ball p ε :=
  connectedComponentIn_subset _ _

theorem traceComponent_subset_trace (γ : Work.Smooth.Jordan.PlaneCurve) (p : ℂ) (ε : ℝ) (a : ℂ) :
    traceComponent γ p ε a ⊆ γ.trace :=
  fun x hx => (traceComponent_subset γ p ε a hx).1

theorem traceComponent_subset_ball (γ : Work.Smooth.Jordan.PlaneCurve) (p : ℂ) (ε : ℝ) (a : ℂ) :
    traceComponent γ p ε a ⊆ Metric.ball p ε :=
  fun x hx => (traceComponent_subset γ p ε a hx).2

theorem mem_traceComponent {γ : Work.Smooth.Jordan.PlaneCurve} {p : ℂ} {ε : ℝ} {a : ℂ}
    (ha : a ∈ γ.trace ∩ Metric.ball p ε) : a ∈ traceComponent γ p ε a :=
  mem_connectedComponentIn ha

theorem sideChamber_subset_ball (γ : Work.Smooth.Jordan.PlaneCurve) (p : ℂ) (ε : ℝ) (a : ℂ) :
    sideChamber γ p ε a ⊆ Metric.ball p ε :=
  Set.diff_subset

theorem sideChamber_eq (γ : Work.Smooth.Jordan.PlaneCurve) (p : ℂ) (ε : ℝ) (a : ℂ) :
    sideChamber γ p ε a = (Metric.ball p ε \ γ.trace) ∪ traceComponent γ p ε a := by
  rw [sideChamber]
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨hxB, hx⟩ := hx
    by_cases hxt : x ∈ γ.trace
    · right
      by_contra hxC
      exact hx (by refine ⟨⟨hxt, hxB⟩, hxC⟩ :
        x ∈ (γ.trace ∩ Metric.ball p ε) \ traceComponent γ p ε a)
    · left
      exact ⟨hxB, hxt⟩
  · rintro x (⟨hxB, hxt⟩ | hxC)
    · exact ⟨hxB, fun h => hxt (Set.mem_of_mem_inter_left h.1)⟩
    · exact ⟨(traceComponent_subset_ball γ p ε a) hxC, fun h => h.2 hxC⟩

end

end Work.SphereJordan
