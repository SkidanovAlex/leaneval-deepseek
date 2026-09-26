import Mathlib
import Submission.Work.Smooth.JordanSeparation.frontier_eq_trace

/-!
# The two sides have the curve as common frontier

Companion to `frontier_eq_trace`: the frontier of the *bounded* side is the curve as well, and the
closures of the two sides are obtained from the sides by adjoining the curve.

* `frontier_V_eq_trace` — `frontier S.V = c.trace`;
* `closure_U_eq` — `closure S.U = S.U ∪ c.trace`;
* `closure_V_eq` — `closure S.V = S.V ∪ c.trace`.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The frontier of the bounded side is the curve.** -/
theorem frontier_V_eq_trace (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {S : PlaneSeparation c.toPlaneCurve} :
    frontier S.V = c.trace := by
  apply Set.Subset.antisymm
  · rw [S.isOpen_V.frontier_eq]
    rintro x ⟨hxcl, hxV⟩
    by_contra hxt
    have hxu : x ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hxt
    rcases hxu with h | h
    · obtain ⟨y, hyU, hyV⟩ := mem_closure_iff.mp hxcl S.U S.isOpen_U h
      exact Set.disjoint_left.mp S.disjoint_UV hyU hyV
    · exact hxV h
  · rintro x ⟨t, rfl⟩
    have hxV : c.γ t ∉ S.V := by
      intro h
      have : c.γ t ∈ c.traceᶜ := by rw [← S.union_eq]; exact Or.inr h
      exact this ⟨t, rfl⟩
    have hxcl : c.γ t ∈ closure S.V := by
      rw [mem_closure_iff]
      intro o ho hxo
      obtain ⟨ε, hε, hεo⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hxo)
      obtain ⟨δ, hδ, hjump⟩ := ind_jump_at c himm hs t
      set s : ℝ := min (δ / 2) (ε / 2) with hsdef
      have hs0 : 0 < s := lt_min (by linarith) (by linarith)
      have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hsε : s < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      obtain ⟨h1, h2, h3⟩ := hjump s hs0 hsδ
      have hside : c.γ t + s * normalField c t ∈ S.V ∨
          c.γ t - s * normalField c t ∈ S.V := by
        have hp : c.γ t + s * normalField c t ∈ c.traceᶜ := h1
        rw [← S.union_eq] at hp
        have hm : c.γ t - s * normalField c t ∈ c.traceᶜ := h2
        rw [← S.union_eq] at hm
        rcases hp with h | h
        · rcases hm with h' | h'
          · exact absurd (ind_const_on_preconnected c S.preconn_U
              (fun w hw => by rw [← S.union_eq]; exact Or.inl hw) h h') h3
          · exact Or.inr h'
        · exact Or.inl h
      have hdist : ∀ u : ℝ, ‖u * normalField c t‖ = |u| := by
        intro u
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_normalField c himm t, mul_one]
      rcases hside with hV | hV
      · refine ⟨c.γ t + s * normalField c t, hεo ?_, hV⟩
        rw [Metric.mem_ball, dist_eq_norm,
          show c.γ t + s * normalField c t - c.γ t = s * normalField c t from by ring, hdist,
          abs_of_pos hs0]
        exact hsε
      · refine ⟨c.γ t - s * normalField c t, hεo ?_, hV⟩
        rw [Metric.mem_ball, dist_eq_norm,
          show c.γ t - s * normalField c t - c.γ t = -(s * normalField c t) from by ring,
          norm_neg, hdist, abs_of_pos hs0]
        exact hsε
    rw [S.isOpen_V.frontier_eq]
    exact ⟨hxcl, hxV⟩

/-- **The closure of the unbounded side is the side together with the curve.** -/
theorem closure_U_eq (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {S : PlaneSeparation c.toPlaneCurve} :
    closure S.U = S.U ∪ c.trace := by
  rw [closure_eq_self_union_frontier, frontier_eq_trace c himm hs]

/-- **The closure of the bounded side is the side together with the curve.** -/
theorem closure_V_eq (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {S : PlaneSeparation c.toPlaneCurve} :
    closure S.V = S.V ∪ c.trace := by
  rw [closure_eq_self_union_frontier, frontier_V_eq_trace c himm hs]

end

end Work.Smooth.JordanSeparation
