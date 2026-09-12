import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic

set_option linter.unusedVariables false

open Set Filter Metric
open scoped Topology

namespace Commons.Analysis.Interval

/-- If `p` is continuous on the open interval `(a,b)`, its image there is
bounded above, and `p t → 0` as `t → a⁺` (resp. `b⁻`), then every positive
value strictly below the supremum of the image is attained. -/
theorem surjOn_Ioo_zero_sSup {p : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hp : ContinuousOn p (Ioo a b))
    (hBdd : BddAbove (p '' Ioo a b))
    (hpa : Tendsto p (𝓝[>] a) (𝓝 0)) (hpb : Tendsto p (𝓝[<] b) (𝓝 0)) :
    ∀ x : ℝ, 0 < x → x < sSup (p '' Ioo a b) →
      ∃ t : ℝ, t ∈ Ioo a b ∧ p t = x := by
  intro x hx0 hxs
  -- The image is nonempty because `(a,b)` is nonempty.
  have hJne : (p '' Ioo a b).Nonempty := by
    obtain ⟨w, hw⟩ := Set.nonempty_Ioo.mpr hab
    exact ⟨p w, w, hw, rfl⟩
  -- A point `t₂` whose value exceeds `x` (exists by the supremum property).
  obtain ⟨z, hzJ, hxz⟩ := exists_lt_of_lt_csSup hJne hxs
  rcases hzJ with ⟨t₂, ht₂, hzt₂⟩
  have hxlt2 : x < p t₂ := by
    rw [← hzt₂] at hxz
    exact hxz
  -- A point `t₁` in `(a,b)` whose value is below `x` (exists since `p → 0`
  -- from the right at `a`, and `x > 0`).
  have hball : Metric.ball (0 : ℝ) x ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds (0 : ℝ) hx0
  have hev_lt : ∀ᶠ t in 𝓝[>] a, p t < x := by
    filter_upwards [hpa.eventually_mem hball] with t ht
    have habs : |p t| < x := by simpa [Real.dist_eq] using ht
    exact (abs_lt.mp habs).2
  have hmem_ioo : Ioo a b ∈ 𝓝[>] a := by
    refine mem_nhdsWithin.mpr ?_
    refine ⟨Iio b, isOpen_Iio, hab, ?_⟩
    intro y hy
    exact ⟨hy.2, hy.1⟩
  have hev_ioo : ∀ᶠ t in 𝓝[>] a, t ∈ Ioo a b := by
    exact hmem_ioo
  obtain ⟨t₁, hpt₁, ht₁⟩ := (hev_lt.and hev_ioo).exists
  -- Both points lie in `(a,b)`, so the whole segment between them does too.
  have hsub : uIcc t₁ t₂ ⊆ Ioo a b := by
    intro y hy
    rcases mem_uIcc.mp hy with ⟨hy₁, hy₂⟩ | ⟨hy₁, hy₂⟩
    · exact ⟨lt_of_lt_of_le ht₁.1 hy₁, lt_of_le_of_lt hy₂ ht₂.2⟩
    · exact ⟨lt_of_lt_of_le ht₂.1 hy₁, lt_of_le_of_lt hy₂ ht₁.2⟩
  have hcont : ContinuousOn p (uIcc t₁ t₂) := hp.mono hsub
  -- Intermediate value theorem on the segment from `t₁` to `t₂`.
  have hle : p t₁ ≤ p t₂ := le_of_lt (lt_trans hpt₁ hxlt2)
  have hxmem : x ∈ uIcc (p t₁) (p t₂) := by
    rw [uIcc_of_le hle]
    exact ⟨le_of_lt hpt₁, le_of_lt hxlt2⟩
  have hivt := intermediate_value_uIcc (f := p) hcont
  obtain ⟨t, ht, hpt⟩ := hivt hxmem
  exact ⟨t, hsub ht, hpt⟩

end Commons.Analysis.Interval