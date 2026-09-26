import Mathlib
import Submission.Work.Smooth.JordanSeparation.Main

/-!
# The two sides are the index level sets

The sibling chapter `Submission/Work/Smooth/Jordan` derives from the *classical* input
`PlaneJordanSchoenflies` that the two components of the complement of a simple closed curve are the
level sets `{ind = 0}` and `{ind ≠ 0}` of the index, and that `|ind| ≤ 1` off the curve.  Those
derivations only use the value of the index on the two sides, which is proved in this chapter for
`C¹` immersed simple closed curves; this file records them here, unconditionally.

* `mem_U_iff_ind_eq_zero`, `mem_V_iff_ind_ne_zero` — the sides are the index level sets;
* `ind_eq_zero_or_abs_eq_one` — the index takes only the values `0`, `1`, `-1` off the trace;
* `ind_abs_le_one` — `|ind| ≤ 1` off the trace.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **A point off the trace lies on the unbounded side iff the index vanishes there.** -/
theorem mem_U_iff_ind_eq_zero (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {S : PlaneSeparation c.toPlaneCurve} {x : ℂ}
    (hx : x ∉ c.trace) : x ∈ S.U ↔ ind c x = 0 := by
  constructor
  · intro h
    exact ind_eq_zero_of_mem_U c himm hs h
  · intro h
    by_contra hU
    have hmem : x ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hx
    have hV : x ∈ S.V := hmem.elim (fun h' => absurd h' hU) id
    have := ind_abs_eq_one_of_mem_V c himm hs hV
    rw [h] at this
    norm_num at this

/-- **A point off the trace lies on the bounded side iff the index does not vanish there.** -/
theorem mem_V_iff_ind_ne_zero (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {S : PlaneSeparation c.toPlaneCurve} {x : ℂ}
    (hx : x ∉ c.trace) : x ∈ S.V ↔ ind c x ≠ 0 := by
  constructor
  · intro h h0
    have := ind_abs_eq_one_of_mem_V c himm hs h
    rw [h0] at this
    norm_num at this
  · intro h
    by_contra hV
    have hmem : x ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hx
    have hU : x ∈ S.U := hmem.elim id (fun h' => absurd h' hV)
    exact h (ind_eq_zero_of_mem_U c himm hs hU)

/-- **The index takes only the values `0`, `1`, `-1` off the trace.** -/
theorem ind_eq_zero_or_abs_eq_one (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {S : PlaneSeparation c.toPlaneCurve} {x : ℂ}
    (hx : x ∉ c.trace) : ind c x = 0 ∨ ind c x = 1 ∨ ind c x = -1 := by
  rcases (S.union_eq ▸ hx : x ∈ S.U ∪ S.V) with h | h
  · exact Or.inl (ind_eq_zero_of_mem_U c himm hs h)
  · have := ind_abs_eq_one_of_mem_V c himm hs h
    rcases abs_cases (ind c x) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inr (Or.inl (by rw [h1] at this; exact this))
    · exact Or.inr (Or.inr (by rw [h1] at this; linarith))

/-- **`|ind| ≤ 1` off the trace** (the sibling chapter's `ind_abs_le_one`, now unconditional). -/
theorem ind_abs_le_one (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {S : PlaneSeparation c.toPlaneCurve} {x : ℂ}
    (hx : x ∉ c.trace) : |ind c x| ≤ 1 := by
  rcases (S.union_eq ▸ hx : x ∈ S.U ∪ S.V) with h | h
  · rw [ind_eq_zero_of_mem_U c himm hs h]; norm_num
  · rw [ind_abs_eq_one_of_mem_V c himm hs h]

/-- **Any two Jordan separations of the same curve have the same sides up to swapping.**  Hence
the index clauses `ind_eq_zero_of_mem_U` / `ind_abs_eq_one_of_mem_V` (and the corollaries below)
hold for *every* `PlaneSeparation` of `c`, not merely for the one produced by `jordanSeparation`;
this makes the values of the index on the sides canonical. -/
theorem eq_U_or_eq_V {c : PlaneCurve} {S T : PlaneSeparation c} :
    S.U = T.U ∨ S.U = T.V := by
  have hsub : ∀ W : Set ℂ, W ⊆ c.traceᶜ → IsPreconnected W → W ⊆ T.U ∨ W ⊆ T.V :=
    fun W hW hpre => IsPreconnected.subset_or_subset T.isOpen_U T.isOpen_V T.disjoint_UV
      (fun z hz => by rw [T.union_eq]; exact hW hz) hpre
  have hSUc : S.U ⊆ c.traceᶜ := by rw [← S.union_eq]; exact subset_union_left
  have hTUc : T.U ⊆ c.traceᶜ := by rw [← T.union_eq]; exact subset_union_left
  have hTVc : T.V ⊆ c.traceᶜ := by rw [← T.union_eq]; exact subset_union_right
  rcases hsub S.U hSUc S.preconn_U with h | h
  · left
    refine subset_antisymm h ?_
    rcases (IsPreconnected.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV
        (fun z hz => by rw [S.union_eq]; exact hTUc hz) T.preconn_U) with h' | h'
    · exact h'
    · exfalso
      exact S.nonempty_U.ne_empty (eq_empty_of_subset_empty fun z hz =>
        Set.disjoint_left.mp S.disjoint_UV hz (h' (h hz)))
  · right
    refine subset_antisymm h ?_
    rcases (IsPreconnected.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV
        (fun z hz => by rw [S.union_eq]; exact hTVc hz) T.preconn_V) with h' | h'
    · exact h'
    · exfalso
      exact S.nonempty_U.ne_empty (eq_empty_of_subset_empty fun z hz =>
        Set.disjoint_left.mp S.disjoint_UV hz (h' (h hz)))

end

end Work.Smooth.JordanSeparation
