import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.localInvKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

theorem lidInvWhere_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : E → E) (S : Set E) (hS : IsOpen S) (hinj : Set.InjOn θ S)
    (hdata : ∀ z ∈ S, ∃ g : E → E, ContDiffAt ℝ (⊤ : ℕ∞) g (θ z) ∧ ContinuousAt g (θ z) ∧
      (∀ᶠ x in nhds z, g (θ x) = x) ∧ (∀ᶠ y in nhds (θ z), θ (g y) = y)) :
    ∀ y ∈ θ '' S, ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep8.lidInvWhere θ S) y := by
  rintro y ⟨z, hzS, rfl⟩
  obtain ⟨g, hgsm, hgct, hgl, hgr⟩ := hdata z hzS
  -- the left-inverse identity holds at the point itself, since `nhds z` is a neighbourhood filter
  have hgy : g (θ z) = z := hgl.self_of_nhds
  -- hence `g` maps a neighbourhood of `θ z` into the open set `S`
  have hB : ∀ᶠ y' in nhds (θ z), g y' ∈ S := by
    have : S ∈ nhds (g (θ z)) := by rw [hgy]; exact hS.mem_nhds hzS
    exact hgct.preimage_mem_nhds this
  -- on that neighbourhood the canonical inverse coincides with the smooth local inverse `g`
  refine hgsm.congr_of_eventuallyEq ?_
  filter_upwards [hB, hgr] with y' hy'S hy'θ
  exact lidInvWhere_eq_of hinj hy'S hy'θ ⟨g y', hy'S, hy'θ⟩

end Work.Diff.STE.B3.SymCalcStep8
