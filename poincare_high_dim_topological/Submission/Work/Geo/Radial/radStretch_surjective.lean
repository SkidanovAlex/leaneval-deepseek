import Mathlib
import Submission.Work.Geo.Radial.RadialDefs

set_option linter.unusedVariables false

namespace Work.Geo.Radial

/-- `radStretch ε R S s` agrees with the identity off the interval `[0, S]`: for `t ≤ 0` the
tent profile `radTent ε S t` vanishes, so `radStretch ε R S s t = t`. -/
theorem radStretch_of_nonpos {ε R S s t : ℝ} (hε : 0 < ε) (ht : t ≤ 0) :
    radStretch ε R S s t = t := by
  rw [radStretch, radTent_of_nonpos hε ht]; ring

/-- `radStretch ε R S s 0 = 0`. -/
theorem radStretch_zero {ε R S s : ℝ} (hε : 0 < ε) : radStretch ε R S s 0 = 0 :=
  radStretch_of_nonpos hε le_rfl

/-- The one-dimensional stretch is continuous in `t` for fixed parameters. -/
theorem radStretch_continuous_right (ε R S s : ℝ) :
    Continuous fun t : ℝ => radStretch ε R S s t :=
  (radStretch_continuous ε R S).comp (continuous_const.prodMk continuous_id)

/-- For `0 < ε < R < S` and `0 ≤ s ≤ 1` the one-dimensional radial stretch is surjective.

It is the identity on `(-∞, 0]` and on `[S, ∞)`, and on `[0, S]` it is continuous with
`radStretch ε R S s 0 = 0` and `radStretch ε R S s S = S`, so every value of `[0, S]` is
attained there by the intermediate value theorem. -/
theorem radStretch_surjective {ε R S s : ℝ} (hε : 0 < ε) (hεR : ε < R) (hRS : R < S)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Function.Surjective (radStretch ε R S s) := by
  have hεS : ε < S := lt_trans hεR hRS
  have hS0 : 0 ≤ S := le_of_lt (lt_trans hε hεS)
  have hcont : Continuous fun t : ℝ => radStretch ε R S s t :=
    radStretch_continuous_right ε R S s
  intro u
  rcases le_or_gt u 0 with hu | hu
  · -- `u ≤ 0`: the identity outside the tent support
    exact ⟨u, radStretch_of_nonpos hε hu⟩
  rcases le_or_gt S u with huS | huS
  · -- `S ≤ u`: again the identity outside the tent support
    exact ⟨u, radStretch_of_ge hεS huS⟩
  · -- `0 < u < S`: intermediate value theorem on `[0, S]`
    have hmem : u ∈ Set.Icc (radStretch ε R S s 0) (radStretch ε R S s S) := by
      rw [radStretch_zero hε, radStretch_S hεS]
      exact ⟨hu.le, huS.le⟩
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc hS0 hcont.continuousOn hmem
    exact ⟨t, ht⟩

end Work.Geo.Radial
