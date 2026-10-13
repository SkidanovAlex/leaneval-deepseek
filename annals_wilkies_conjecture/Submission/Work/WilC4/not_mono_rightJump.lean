import Mathlib
import Submission.Work.WilC4.UnifDefs

open Filter
open scoped Topology

namespace Work.WilC4

/-- A nondecreasing function on an interval cannot have a strict "right jump" at *every* point:
a monotone function has at most countably many right-discontinuity points, whereas the interval
`(a, b)` is uncountable. -/
theorem not_mono_rightJump {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hmono : ∀ x y : ℝ, a < x → x < y → y < b → g x ≤ g y)
    (hjump : ∀ x : ℝ, a < x → x < b → ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ t : ℝ, x < t → t < x + δ → g x + ε ≤ g t) :
    False := by
  -- `g` is monotone on the open interval.
  have hmonoOn : MonotoneOn g (Set.Ioo a b) := by
    intro x hx y hy hxy
    obtain ⟨hax, hxb⟩ := hx
    obtain ⟨hay, hyb⟩ := hy
    rcases lt_or_eq_of_le hxy with h | h
    · exact hmono x y hax h hyb
    · subst h; exact le_rfl
  -- Every point of `(a, b)` is a point of right-discontinuity of `g`.
  have hsub : Set.Ioo a b ⊆ {x | x ∈ Set.Ioo a b ∧
      ¬ ContinuousWithinAt g (Set.Ioo a b ∩ Set.Ioi x) x} := by
    intro x hxab
    refine ⟨hxab, ?_⟩
    obtain ⟨hax, hxb⟩ := hxab
    intro hcont
    obtain ⟨ε, δ, hεpos, hδpos, hj⟩ := hjump x hax hxb
    -- Replace continuity by its metric epsilon-delta form.
    have hcont' : Tendsto g (𝓝[Set.Ioo a b ∩ Set.Ioi x] x) (𝓝 (g x)) := hcont
    rw [Metric.tendsto_nhdsWithin_nhds] at hcont'
    obtain ⟨δ', hδ'pos, hδ'⟩ := hcont' (ε / 2) (by linarith)
    -- A point `t` to the right of `x`, close enough to fall in both windows.
    set m : ℝ := min (min δ δ') (b - x) with hmdef
    have hm_pos : 0 < m := by
      rw [hmdef]; exact lt_min (lt_min hδpos hδ'pos) (by linarith)
    have hm_le_δ : m ≤ δ := by
      rw [hmdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hm_le_δ' : m ≤ δ' := by
      rw [hmdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hm_le_b : m ≤ b - x := by rw [hmdef]; exact min_le_right _ _
    set t : ℝ := x + m / 2 with htdef
    have ht_gt : x < t := by rw [htdef]; linarith
    have ht_lt_b : t < b := by rw [htdef]; linarith
    have ht_lt_δ : t < x + δ := by rw [htdef]; linarith
    have hdist : dist t x < δ' := by
      rw [Real.dist_eq, abs_of_pos (by rw [htdef]; linarith)]
      rw [htdef]; linarith
    have htmem : t ∈ Set.Ioo a b ∩ Set.Ioi x := ⟨⟨by linarith, ht_lt_b⟩, ht_gt⟩
    -- `g t` is at once below `g x + ε/2` (continuity) and at least `g x + ε` (the jump).
    have hsmall : dist (g t) (g x) < ε / 2 := hδ' htmem hdist
    have hge : g x + ε ≤ g t := hj t ht_gt ht_lt_δ
    have hdistgt : dist (g t) (g x) = g t - g x := by
      rw [Real.dist_eq, abs_of_nonneg]; linarith
    linarith
  -- Hence `(a, b)` is countable, contradicting its uncountability.
  have hcount : (Set.Ioo a b).Countable :=
    (MonotoneOn.countable_not_continuousWithinAt_Ioi hmonoOn).mono hsub
  rw [Cardinal.Real.Ioo_countable_iff] at hcount
  exact absurd hcount (not_le.mpr hab)

end Work.WilC4
