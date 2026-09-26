import Mathlib
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range
import Submission.Work.Smooth.SphereJordan.interior_range_empty_of_injOn_Icc
import Submission.Work.BoxShrink.Bubble.Plane.interior_iUnion_fin_eq_empty

/-!
# A point of the trace of a Jordan curve lies in the closure of every complementary component

`Work.Smooth.SphereJordan.memClosureConnectedComponentIn`: for a continuous `2π`-periodic curve
`γ : ℝ → ℂ` injective on one period, any point `p` of the trace and any point `w` off the trace
satisfy `p ∈ closure (connectedComponentIn (Set.range γ)ᶜ w)`.

This is Maehara's Lemma 2.  Two cases:

* if `(Set.range γ)ᶜ` is preconnected then it is the single component of `w`, and the claim reduces
  to `p ∈ closure ((Set.range γ)ᶜ)`, i.e. to `interior (Set.range γ) = ∅` (proved here from
  `interior_range_empty_of_injOn_Icc` by covering the period by two intervals of length `< 2π`);
* otherwise `frontier (connectedComponentIn (Set.range γ)ᶜ w) = Set.range γ` (Maehara's Lemma 1,
  `Work.Topology.PlaneCurve.frontier_component_eq_range`), and `frontier ⊆ closure`.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- The trace of a continuous `2π`-periodic curve which is injective on one period has empty
interior.  (The period `[0, 2π]` is split into the two closed intervals `[0, 2π - 1]` and
`[1, 2π]`, on each of which `γ` is injective, hence whose image has empty interior; the trace is
the union of the two closed images.) -/
theorem trace_interior_eq_empty_of_periodic {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) :
    interior (Set.range γ) = ∅ := by
  have h1le : (1 : ℝ) ≤ 2 * Real.pi - 1 := by nlinarith [Real.pi_gt_three]
  have hI : Set.Icc (0 : ℝ) (2 * Real.pi) =
      Set.Icc 0 (2 * Real.pi - 1) ∪ Set.Icc 1 (2 * Real.pi) := by
    ext t
    simp only [Set.mem_Icc, Set.mem_union]
    constructor
    · rintro ⟨ht0, ht1⟩
      by_cases h : t ≤ 2 * Real.pi - 1
      · exact Or.inl ⟨ht0, h⟩
      · exact Or.inr ⟨by linarith [not_le.mp h, h1le], ht1⟩
    · rintro (⟨ht0, ht1⟩ | ⟨ht0, ht1⟩)
      · exact ⟨ht0, by linarith⟩
      · exact ⟨by linarith, ht1⟩
  have hrange : Set.range γ =
      γ '' Set.Icc (0 : ℝ) (2 * Real.pi - 1) ∪ γ '' Set.Icc (1 : ℝ) (2 * Real.pi) := by
    rw [Work.Topology.PlaneCurve.range_eq_image_Icc hper, hI, Set.image_union]
  have hinjA : Set.InjOn γ (Set.Icc (0 : ℝ) (2 * Real.pi - 1)) :=
    Work.Topology.PlaneCurve.injOn_Icc_of_injOn_Ico hper hinj (by linarith)
  have hinjB : Set.InjOn γ (Set.Icc (1 : ℝ) (2 * Real.pi)) :=
    Work.Topology.PlaneCurve.injOn_Icc_of_injOn_Ico hper hinj (by linarith)
  have hintA : interior (γ '' Set.Icc (0 : ℝ) (2 * Real.pi - 1)) = ∅ :=
    interior_range_empty_of_injOn_Icc (by nlinarith [Real.pi_gt_three]) hcont hinjA
  have hintB : interior (γ '' Set.Icc (1 : ℝ) (2 * Real.pi)) = ∅ :=
    interior_range_empty_of_injOn_Icc (by nlinarith [Real.pi_gt_three]) hcont hinjB
  have hclB : IsClosed (γ '' Set.Icc (1 : ℝ) (2 * Real.pi)) :=
    (isCompact_Icc.image hcont).isClosed
  rw [hrange]
  exact Work.BoxShrink.Bubble.Plane.interior_union_eq_empty_of_isClosed_right hclB hintA hintB

/-- **Maehara's Lemma 2.**  Every point of the trace of a continuous `2π`-periodic curve injective
on one period lies in the closure of the connected component of the complement containing any
point off the trace. -/
theorem memClosureConnectedComponentIn {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {w p : ℂ} (hw : w ∉ Set.range γ) (hp : p ∈ Set.range γ) :
    p ∈ closure (connectedComponentIn (Set.range γ)ᶜ w) := by
  by_cases hdis : IsPreconnected (Set.range γ)ᶜ
  · -- the complement is a single component
    have hcompl : connectedComponentIn (Set.range γ)ᶜ w = (Set.range γ)ᶜ :=
      hdis.connectedComponentIn hw
    have hne : interior (Set.range γ) = ∅ := trace_interior_eq_empty_of_periodic hcont hper hinj
    rw [hcompl, closure_compl, hne]
    simp
  · -- the frontier of the component is the whole curve
    have hfr := Work.Topology.PlaneCurve.frontier_component_eq_range hcont hper hinj hdis w hw
    have hp' : p ∈ frontier (connectedComponentIn (Set.range γ)ᶜ w) := by
      rw [hfr]; exact hp
    exact frontier_subset_closure hp'

end

end Work.Smooth.SphereJordan
