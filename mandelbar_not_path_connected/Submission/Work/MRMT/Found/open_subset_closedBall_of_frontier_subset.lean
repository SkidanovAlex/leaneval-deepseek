import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- **Norm bound from a frontier contained in a ball.**

If `A ⊆ ℂ` is open and bounded and its frontier is contained in the closed ball of radius
`M` around `0`, then `A` itself is contained in that ball.

The proof maximises the continuous function `z ↦ ⟪z, u⟫_ℝ` (where `u` is a unit vector
with `⟪a, u⟫_ℝ = ‖a‖`, constructed from `a`) over the compact set `closure A`.  An extremal
point `q` cannot lie in `A` (being an interior point, one could step slightly in the
direction `u` and increase the value), hence `q` lies on `frontier A`, where `‖q‖ ≤ M` by
hypothesis.  Since `φ a = ‖a‖ ≤ φ q ≤ ‖q‖ ≤ M`, the result follows. -/
theorem open_subset_closedBall_of_frontier_subset {A : Set ℂ} (hA : IsOpen A)
    (hb : Bornology.IsBounded A) {M : ℝ}
    (h : frontier A ⊆ Metric.closedBall 0 M) : A ⊆ Metric.closedBall 0 M := by
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  -- A unit vector `u` with `⟪a, u⟫_ℝ = ‖a‖`.
  have hex : ∃ u : ℂ, ‖u‖ = 1 ∧ inner ℝ a u = ‖a‖ := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · exact ⟨1, by simp, by rw [ha0]; simp⟩
    · refine ⟨(‖a‖ : ℝ)⁻¹ • a, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg a)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha0)]
      · rw [real_inner_smul_right, real_inner_self_eq_norm_sq, sq, ← mul_assoc,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha0), one_mul]
  obtain ⟨u, hu1, hua⟩ := hex
  let φ : ℂ → ℝ := fun z => inner ℝ z u
  have hφcont : Continuous φ := by
    simp only [φ]; exact continuous_id.inner continuous_const
  have hKcomp : IsCompact (closure A) := by
    rw [Metric.isCompact_iff_isClosed_bounded]; exact ⟨isClosed_closure, hb.closure⟩
  have hKne : (closure A).Nonempty := ⟨a, subset_closure ha⟩
  obtain ⟨q, hqK, hqmax⟩ := hKcomp.exists_isMaxOn hKne hφcont.continuousOn
  -- The maximum point lies on the frontier.
  have hqnd : q ∉ A := by
    intro hqA
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hA q hqA
    set w : ℂ := q + (ε/2) • u with hwdef
    have hwmem : w ∈ A := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hwq : w - q = (ε/2) • u := by rw [hwdef]; abel
      rw [hwq, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hu1, mul_one]
      linarith
    have hφw : φ w = φ q + ε/2 := by
      simp only [φ]
      rw [hwdef, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu1]
      norm_num
    have hle : φ w ≤ φ q := hqmax (subset_closure hwmem)
    rw [hφw] at hle
    linarith
  have hqfront : q ∈ frontier A := by
    rw [frontier]; exact ⟨hqK, by rw [hA.interior_eq]; exact hqnd⟩
  have hqM : ‖q‖ ≤ M := by
    have hqmem := h hqfront
    rw [Metric.mem_closedBall, dist_zero_right] at hqmem
    exact hqmem
  calc ‖a‖ = φ a := hua.symm
    _ ≤ φ q := hqmax (subset_closure ha)
    _ ≤ ‖q‖ := by
        calc φ q = inner ℝ q u := rfl
          _ ≤ |inner ℝ q u| := le_abs_self _
          _ ≤ ‖q‖ * ‖u‖ := abs_real_inner_le_norm _ _
          _ = ‖q‖ := by rw [hu1, mul_one]
    _ ≤ M := hqM

end Work.MRMT.Found
