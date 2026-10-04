import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-- Newton–Leibniz on a closed interval, with the derivative hypothesis imposed only *within*
the closed interval `[0, τ]`: if `F` has (one-sided at the endpoints) derivative `G t` at every
`t ∈ [0, τ]` and `G` is continuous there, then `F s - F t = ∫ σ in t..s, G σ` for all
`s, t ∈ [0, τ]`. -/
theorem sub_eq_integral_of_hasDerivWithinAt
    {τ : ℝ} (hτ : 0 < τ) (F G : ℝ → ℝ)
    (hder : ∀ t ∈ Set.Icc (0 : ℝ) τ, HasDerivWithinAt F (G t) (Set.Icc (0 : ℝ) τ) t)
    (hG : ContinuousOn G (Set.Icc (0 : ℝ) τ)) :
    ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ t ∈ Set.Icc (0 : ℝ) τ,
      F s - F t = ∫ σ in t..s, G σ := by
  have _hτpos : (0 : ℝ) ≤ τ := hτ.le
  -- `F` is continuous on `[0, τ]`, being differentiable within it everywhere.
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) τ) := HasDerivWithinAt.continuousOn hder
  intro s hs t ht
  rcases le_total t s with hts | hst
  · -- `t ≤ s`: apply the fundamental theorem of calculus on `[t, s]`.
    have hsub : Set.Icc t s ⊆ Set.Icc (0 : ℝ) τ := Set.Icc_subset_Icc ht.1 hs.2
    have hcont : ContinuousOn F (Set.Icc t s) := hFcont.mono hsub
    -- On the open interval `(t, s)` the point is interior to `[0, τ]`, so the derivative within
    -- `[0, τ]` is an honest two-sided derivative.
    have hderiv : ∀ x ∈ Set.Ioo t s, HasDerivAt F (G x) x := by
      intro x hx
      exact (hder x ⟨le_trans ht.1 hx.1.le, le_trans hx.2.le hs.2⟩).hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt ht.1 hx.1) (lt_of_lt_of_le hx.2 hs.2))
    have hint : IntervalIntegrable G MeasureTheory.volume t s :=
      (hG.mono hsub).intervalIntegrable_of_Icc hts
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hts hcont hderiv hint).symm
  · -- `s ≤ t`: reduce to the previous case by reversing the interval.
    have hsub : Set.Icc s t ⊆ Set.Icc (0 : ℝ) τ := Set.Icc_subset_Icc hs.1 ht.2
    have hcont : ContinuousOn F (Set.Icc s t) := hFcont.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo s t, HasDerivAt F (G x) x := by
      intro x hx
      exact (hder x ⟨le_trans hs.1 hx.1.le, le_trans hx.2.le ht.2⟩).hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hs.1 hx.1) (lt_of_lt_of_le hx.2 ht.2))
    have hint : IntervalIntegrable G MeasureTheory.volume s t :=
      (hG.mono hsub).intervalIntegrable_of_Icc hst
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hcont hderiv hint
    rw [intervalIntegral.integral_symm, h]
    ring

end Work.Diff.STE.Lead
