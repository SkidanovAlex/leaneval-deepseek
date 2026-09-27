import Mathlib

namespace Work.Drive

/-- **A one-sided collar of the circle `‖z‖ = 1/2`.**

Let `x : ℂ → ℂ` be continuous and let `e : ℝ`.  Suppose `‖x ·‖ ≥ e` outside the open disk of
radius `1/2` (hypothesis `hout`) and `‖x ·‖ > e` *strictly* on the circle `‖z‖ = 1/2`
(hypothesis `hin`).  Then the strict inequality propagates to a collar of the circle: there is
`ρ < 1/2` such that `ρ ≤ ‖z‖` already forces `e ≤ ‖x z‖`.

The proof is compactness of the circle together with the thickening lemma
`IsCompact.exists_thickening_subset_open`: the set `{z | e < ‖x z‖}` is open and contains the
compact sphere `Metric.sphere 0 (1/2)`, hence contains `Metric.thickening δ` of it for some
`δ > 0`; the annulus `ρ ≤ ‖z‖ < 1/2` is contained in that thickening because the radial
projection `((1/2)/‖z‖) • z` of a point of the annulus lies on the sphere at distance
`1/2 - ‖z‖ ≤ δ/…` from it.
-/
theorem exists_collar_of_norm_eq (x : ℂ → ℂ) (hxc : Continuous x) {e : ℝ}
    (hout : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → e ≤ ‖x z‖)
    (hin : ∀ z : ℂ, ‖z‖ = 1 / 2 → e < ‖x z‖) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 2 ∧ ∀ z : ℂ, ρ ≤ ‖z‖ → e ≤ ‖x z‖ := by
  -- the open set where the strict inequality holds
  have hU : IsOpen {z : ℂ | e < ‖x z‖} := isOpen_lt continuous_const hxc.norm
  -- the circle is compact and lies in it
  have hS : IsCompact (Metric.sphere (0 : ℂ) (1 / 2)) := isCompact_sphere 0 (1/2)
  have hSU : Metric.sphere (0 : ℂ) (1 / 2) ⊆ {z : ℂ | e < ‖x z‖} := by
    intro z hz
    rw [Metric.mem_sphere] at hz
    exact hin z (by simpa [dist_eq_norm] using hz)
  obtain ⟨δ, hδpos, hδ⟩ := hS.exists_thickening_subset_open hU hSU
  -- a positive collar width, smaller than δ and than 1/4
  have hmin : 0 < min δ (1/4 : ℝ) := lt_min hδpos (by norm_num)
  have hηpos : 0 < min δ (1/4 : ℝ)/2 := by linarith
  have hηle : min δ (1/4 : ℝ)/2 ≤ 1/8 := by have := min_le_right δ (1/4:ℝ); linarith
  have hηδ : min δ (1/4 : ℝ)/2 < δ := by have := min_le_left δ (1/4:ℝ); linarith
  refine ⟨1/2 - min δ (1/4 : ℝ)/2, by linarith, by linarith, ?_⟩
  intro z hz
  by_cases h2 : (1/2 : ℝ) ≤ ‖z‖
  · exact hout z h2
  · -- `z` lies in the open disk of radius `1/2`: it is within `δ` of the circle
    rw [not_le] at h2
    have hzpos : 0 < ‖z‖ := by linarith
    have hmem : z ∈ Metric.thickening δ (Metric.sphere (0:ℂ) (1/2)) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨((1/2)/‖z‖) • z, ?_, ?_⟩
      · -- the radial projection lies on the circle
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity), div_mul_cancel₀ _ (ne_of_gt hzpos)]
      · -- and is at distance `1/2 - ‖z‖ < δ` from `z`
        rw [dist_eq_norm]
        have hrew : z - ((1/2)/‖z‖) • z = (1 - (1/2)/‖z‖) • z := by rw [sub_smul, one_smul]
        rw [hrew, norm_smul, Real.norm_eq_abs]
        have hmul : (1 - (1/2)/‖z‖) * ‖z‖ = ‖z‖ - 1/2 := by field_simp
        have hkey : |1 - (1/2)/‖z‖| * ‖z‖ = 1/2 - ‖z‖ := by
          have h1 : |1 - (1/2)/‖z‖| * ‖z‖ = |(1 - (1/2)/‖z‖) * ‖z‖| := by
            rw [abs_mul, abs_of_pos hzpos]
          rw [h1, hmul, abs_of_neg (by linarith)]
          ring
        rw [hkey]
        linarith
    exact le_of_lt (hδ hmem)

end Work.Drive
