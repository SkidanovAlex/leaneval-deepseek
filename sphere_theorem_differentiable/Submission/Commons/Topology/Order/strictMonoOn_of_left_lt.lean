import Mathlib.Analysis.Normed.Order.Lattice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology.Order

open Set

/-- If `f` is continuous on `[a,b]` and at every point `t ∈ [a,b]` the values of `f` just to the
left of `t` are strictly smaller than `f t`, then `f` is strictly increasing on `[a,b]`.

The proof: suppose `x < y` in `[a,b]` with `f y ≤ f x`.  By the extreme value theorem `f` attains a
minimum on the compact interval `[x,y]`, say at a point `z ∈ [x,y]`.  If `z > x`, the hypothesis at
`z` forces `f (z-ε) < f z` for small `ε > 0` while `z - ε` is still in `[x,y]`, contradicting
minimality of `z`.  Hence `z = x`; then `f x ≤ f y` together with `f y ≤ f x` gives `f y = f x`, so
`y` is also a minimizer on `[x,y]`, and the same argument at `y` gives the contradiction. -/
theorem strictMonoOn_of_left_lt {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (h : ∀ t ∈ Set.Icc a b, ∃ s : ℝ, 0 < s ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) s, f (t - ε) < f t) :
    StrictMonoOn f (Set.Icc a b) := by
  intro x hx y hy hxy
  by_contra hlt
  have hlt' : f y ≤ f x := not_lt.mp hlt
  -- A point of `[x, y]` strictly to the right of `x` cannot be a minimizer of `f` on `[x, y]`.
  obtain ⟨z, hz, hzmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hxy.le)
      (hcont.mono (Icc_subset_Icc hx.1 hy.2))
  have key : ∀ w ∈ Icc x y, x < w → IsMinOn f (Icc x y) w → False := by
    intro w hw hxw hwmin
    have hwx : x ≤ w := hw.1
    have hwy : w ≤ y := hw.2
    have hwab : w ∈ Icc a b := ⟨le_trans hx.1 hwx, le_trans hwy hy.2⟩
    obtain ⟨s, hs, hs'⟩ := h w hwab
    set ε := min s (w - x) / 2 with hεdef
    have hεpos : 0 < ε := by
      have h0 : 0 < min s (w - x) := lt_min hs (sub_pos.mpr hxw)
      simp only [hεdef]; linarith
    have hεs : ε < s := by
      have h1 : min s (w - x) ≤ s := min_le_left _ _
      simp only [hεdef]; linarith
    have hmem : w - ε ∈ Icc x y := by
      have h2 : min s (w - x) ≤ w - x := min_le_right _ _
      have h3 : ε ≤ (w - x) / 2 := by simp only [hεdef]; linarith
      exact ⟨by linarith, by linarith⟩
    have h1 : f w ≤ f (w - ε) := hwmin hmem
    have h2 : f (w - ε) < f w := hs' ε ⟨hεpos, hεs⟩
    exact absurd h1 (not_le.mpr h2)
  rcases lt_or_eq_of_le hz.1 with hxz | hxz
  · exact key z hz hxz hzmin
  · -- `z = x`: then `f y = f x`, so `y` is also a minimizer.
    have hyIcc : y ∈ Icc x y := ⟨hxy.le, le_refl y⟩
    have hzy : f z ≤ f y := hzmin hyIcc
    have hzyx : f y = f x := le_antisymm hlt' (by rw [hxz]; exact hzy)
    have hyMin : IsMinOn f (Icc x y) y := by
      intro w hw
      calc f y = f x := hzyx
        _ = f z := by rw [hxz]
        _ ≤ f w := hzmin hw
    exact key y hyIcc hxy hyMin

end Commons.Topology.Order