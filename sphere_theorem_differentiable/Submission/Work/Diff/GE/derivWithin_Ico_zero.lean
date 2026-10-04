import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# One-sided derivative at the left endpoint from the interior derivative

If `f` is differentiable on `(0, T)` with derivative `L`, and both `f` and `L` are continuous
*within* `[0, T)` at `0`, then `f` has derivative `L 0` at `0` within `[0, T)`.

This is the mean value theorem plus continuity of `L`: for `0 < y < T` the finite difference
quotient `(f y - f 0) / y` equals `L c` for some `c ∈ (0, y)`, and `c → 0` as `y → 0`.

Only the value of `L` on `(0, T)` and its continuity at `0` are used; `L` need not be the
actual derivative of `f` anywhere else.
-/

namespace Work.Diff.GE

theorem derivWithin_Ico_zero
    (f L : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt f (L t) t)
    (hcontf : ContinuousWithinAt f (Set.Ico 0 T) 0)
    (hcontL : ContinuousWithinAt L (Set.Ico 0 T) 0) :
    HasDerivWithinAt f (L 0) (Set.Ico 0 T) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Ico 0 T \ {0} = Set.Ioo 0 T := Set.Ico_sdiff_left
  rw [hset]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := (Metric.continuousWithinAt_iff.mp hcontL) ε hε
  refine ⟨min δ₁ T, lt_min hδ₁pos hT, ?_⟩
  intro y hy hydist
  have hypos : (0 : ℝ) < y := hy.1
  have hyT : y < T := hy.2
  have hydist' : y < min δ₁ T := by
    have h := hydist
    rw [Real.dist_eq, sub_zero, abs_of_pos hypos] at h
    exact h
  have hyltδ₁ : y < δ₁ := lt_of_lt_of_le hydist' (min_le_left δ₁ T)
  have hcontIcc : ContinuousOn f (Set.Icc 0 y) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
    · rw [← hx0]
      exact hcontf.mono (Set.Icc_subset_Ico_right hyT)
    · exact ((hderiv x ⟨hxpos, lt_of_le_of_lt hx.2 hyT⟩).continuousAt).continuousWithinAt
  have hdiffIoo : DifferentiableOn ℝ f (Set.Ioo 0 y) := by
    intro x hx
    exact ((hderiv x ⟨hx.1, lt_trans hx.2 hyT⟩).differentiableAt).differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hypos hcontIcc hdiffIoo
  have hcT : c ∈ Set.Ioo 0 T := ⟨hc.1, lt_trans hc.2 hyT⟩
  have hcIco : c ∈ Set.Ico 0 T := ⟨le_of_lt hc.1, hcT.2⟩
  have hcdist : dist c 0 < δ₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hc.1]
    exact lt_of_lt_of_le (lt_trans hc.2 hyltδ₁) le_rfl
  have hcbound : dist (L c) (L 0) < ε := hδ₁ hcIco hcdist
  have hslope : slope f 0 y = L c := by
    rw [slope_def_field, ← hcd, (hderiv c hcT).deriv]
  rw [hslope]
  exact hcbound

end Work.Diff.GE
