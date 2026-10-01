import Mathlib

namespace Work.LinnikAreas

/-- The `tsum` of `u ↦ κ u * Φ u` differs from the `finsum` of its `S`-indicator by at
most the `tsum` of the norms of the terms outside `S`. -/
theorem norm_tsum_sub_finsum_indicator_le {κ Φ : ℂ → ℂ} {S : ℂ → Prop} [DecidablePred S]
    (hab : Summable (fun u => ‖κ u * Φ u‖))
    (hfin : Function.HasFiniteSupport (fun u => if S u then κ u * Φ u else 0)) :
    ‖(∑' u, κ u * Φ u) - (∑ᶠ u, if S u then κ u * Φ u else 0)‖
      ≤ ∑' u, if S u then 0 else ‖κ u * Φ u‖ := by
  -- The `S`-indicator is summable (finite support), and its `finsum` is its `tsum`.
  have hsum : Summable (fun u => (if S u then κ u * Φ u else 0 : ℂ)) :=
    summable_of_hasFiniteSupport hfin
  rw [← tsum_eq_finsum (f := fun u => (if S u then κ u * Φ u else 0 : ℂ))
        (L := SummationFilter.unconditional ℂ) hfin]
  -- Pull the difference inside the sum.
  rw [← Summable.tsum_sub hab.of_norm hsum]
  -- The pointwise difference has norm `if S u then 0 else ‖κ u * Φ u‖`, hence summable.
  have hsum_norm : Summable (fun u => ‖κ u * Φ u - (if S u then κ u * Φ u else 0)‖) := by
    apply Summable.of_nonneg_of_le (fun u => norm_nonneg _) _ hab
    intro u
    by_cases hs : S u
    · simp only [hs, if_true, sub_self, norm_zero]; positivity
    · simp [hs]
  -- Rewriting the sum of norms of the differences into the stated right-hand side.
  have heq : (∑' u, ‖κ u * Φ u - (if S u then κ u * Φ u else 0)‖)
      = ∑' u, (if S u then 0 else ‖κ u * Φ u‖) := by
    congr 1 with u
    by_cases hs : S u <;> simp [hs]
  exact le_trans (norm_tsum_le_tsum_norm hsum_norm) (le_of_eq heq)

end Work.LinnikAreas
