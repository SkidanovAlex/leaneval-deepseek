import Mathlib.Analysis.Normed.Group.Basic

namespace Commons.Algebra.BigOperators

/-- Triangle inequality for `finsum` in a seminormed group. No finiteness hypothesis is needed on
`f`: if the support of `f` is infinite then `∑ᶠ i, f i = 0` by definition. -/
theorem norm_finsum_le_finsum_norm_aux {α : Type*} {E : Type*} [SeminormedAddCommGroup E]
    (f : α → E) : ‖∑ᶠ i, f i‖ ≤ ∑ᶠ i, ‖f i‖ := by
  by_cases hf : Function.HasFiniteSupport f
  · have hsub : Function.support f ⊆ (hf.toFinset : Set α) :=
      fun i hi => hf.mem_toFinset.mpr hi
    have hsub' : Function.support (fun i => ‖f i‖) ⊆ (hf.toFinset : Set α) := by
      intro i hi
      rw [Function.mem_support] at hi
      exact hf.mem_toFinset.mpr (fun h0 => hi (by rw [h0, norm_zero]))
    rw [finsum_eq_sum_of_support_subset f hsub,
        finsum_eq_sum_of_support_subset (fun i => ‖f i‖) hsub']
    exact norm_sum_le _ _
  · rw [finsum_of_not_hasFiniteSupport hf, norm_zero]
    exact finsum_nonneg (fun i => norm_nonneg (f i))

theorem norm_finsum_le_of_norm_le {α : Type*} {E : Type*} [SeminormedAddCommGroup E]
    {f : α → E} {g : α → ℝ} (hg : Function.HasFiniteSupport g)
    (hfg : ∀ i, ‖f i‖ ≤ g i) : ‖∑ᶠ i, f i‖ ≤ ∑ᶠ i, g i := by
  refine le_trans (norm_finsum_le_finsum_norm_aux f) ?_
  have hsub : Function.support (fun i => ‖f i‖) ⊆ (hg.toFinset : Set α) := by
    intro i hi
    rw [Function.mem_support] at hi
    have hpos : 0 < ‖f i‖ := lt_of_le_of_ne (norm_nonneg (f i)) (Ne.symm hi)
    have hgpos : 0 < g i := lt_of_lt_of_le hpos (hfg i)
    exact hg.mem_toFinset.mpr (ne_of_gt hgpos)
  rw [finsum_eq_sum_of_support_subset (fun i => ‖f i‖) hsub,
      finsum_eq_sum_of_support_subset g (fun i hi => hg.mem_toFinset.mpr hi)]
  exact Finset.sum_le_sum (fun i _ => hfg i)

end Commons.Algebra.BigOperators