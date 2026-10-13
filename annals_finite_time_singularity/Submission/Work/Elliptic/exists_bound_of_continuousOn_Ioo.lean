import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- A function continuous on an open interval `(a,b)` that is bounded near each endpoint
is bounded on the whole interval. -/
theorem exists_bound_of_continuousOn_Ioo {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo a b))
    (hl : ∃ C δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Ioo a (a + δ), |g x| ≤ C)
    (hr : ∃ C δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Ioo (b - δ) b, |g x| ≤ C) :
    ∃ C, ∀ x ∈ Set.Ioo a b, |g x| ≤ C := by
  obtain ⟨Cl, δl, hδl, hlb⟩ := hl
  obtain ⟨Cr, δr, hδr, hrb⟩ := hr
  have h3 : (0:ℝ) < (b - a) / 3 := by linarith
  set u : ℝ := min δl ((b - a) / 3) with hu_def
  set v : ℝ := min δr ((b - a) / 3) with hv_def
  have hu_pos : 0 < u := lt_min hδl h3
  have hv_pos : 0 < v := lt_min hδr h3
  have hu_le_dl : u ≤ δl := min_le_left _ _
  have hu_le3 : u ≤ (b - a) / 3 := min_le_right _ _
  have hv_le_dr : v ≤ δr := min_le_left _ _
  have hv_le3 : v ≤ (b - a) / 3 := min_le_right _ _
  have hL_gt : a < a + u := by linarith
  have hR_lt : b - v < b := by linarith
  have hsub : Set.Icc (a + u) (b - v) ⊆ Set.Ioo a b :=
    Set.Icc_subset_Ioo hL_gt hR_lt
  obtain ⟨Cm, hCm⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.mono hsub)
  refine ⟨max Cl (max Cr Cm), ?_⟩
  intro x hx
  obtain ⟨hxa, hxb⟩ := hx
  rcases lt_or_ge x (a + u) with hxL | hxL
  · have hmem : x ∈ Set.Ioo a (a + δl) := ⟨hxa, by linarith⟩
    exact le_trans (hlb x hmem) (le_max_left _ _)
  · by_cases hxR : x ≤ b - v
    · have hxIcc : x ∈ Set.Icc (a + u) (b - v) := ⟨hxL, hxR⟩
      exact le_trans (hCm x hxIcc) (le_trans (le_max_right _ _) (le_max_right _ _))
    · have hxR' : b - v < x := not_le.mp hxR
      have hmem : x ∈ Set.Ioo (b - δr) b := ⟨by linarith, hxb⟩
      exact le_trans (hrb x hmem) (le_trans (le_max_left _ _) (le_max_right _ _))

end Work.Elliptic
