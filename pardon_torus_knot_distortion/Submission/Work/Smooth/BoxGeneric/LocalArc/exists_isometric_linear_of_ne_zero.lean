import Mathlib

namespace Work.Smooth.BoxGeneric.LocalArc

/-- For a nonzero continuous linear functional `L` on `ℝ × ℝ` (with the product, i.e. sup, norm)
there is a linear isometry `M` of `ℝ × ℝ` (equal to a signed coordinate permutation) such that
`L (M (1,0))` is positive. -/
theorem exists_isometric_linear_of_ne_zero (L : (ℝ × ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ M : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), (∀ z, ‖M z‖ = ‖z‖) ∧ Function.Surjective M ∧
      0 < L (M (1, 0)) := by
  -- the coordinate swap, an isometry of the sup norm
  let S : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hS : ∀ z : ℝ × ℝ, ‖S z‖ = ‖z‖ := by
    intro z
    simp [S, Prod.norm_def, max_comm]
  -- at least one of the two basis vectors is not killed by `L`
  have key : L (1, 0) ≠ 0 ∨ L (0, 1) ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    obtain ⟨h1, h2⟩ := h
    apply hL
    apply ContinuousLinearMap.ext
    intro z
    show L z = 0
    have hz : z = z.1 • ((1, 0) : ℝ × ℝ) + z.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
    rw [hz, map_add, map_smul, map_smul]
    simp [h1, h2]
  rcases key with h1 | h2
  · -- `L (1,0) ≠ 0`: use `±id` according to the sign
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · refine ⟨-(ContinuousLinearMap.id ℝ (ℝ × ℝ)), ?_, ?_, ?_⟩
      · intro z; simp
      · intro w; exact ⟨-w, by simp⟩
      · simp only [neg_apply, ContinuousLinearMap.id_apply, map_neg]
        linarith
    · refine ⟨ContinuousLinearMap.id ℝ (ℝ × ℝ), ?_, ?_, ?_⟩
      · intro z; simp
      · intro w; exact ⟨w, by simp⟩
      · simpa using hgt
  · -- `L (0,1) ≠ 0`: use `±S` according to the sign
    rcases lt_or_gt_of_ne h2 with hlt | hgt
    · refine ⟨-S, ?_, ?_, ?_⟩
      · intro z
        rw [neg_apply, norm_neg, hS z]
      · intro w; exact ⟨S (-w), by simp [S]⟩
      · have h0 : S (1, 0) = ((0, 1) : ℝ × ℝ) := by simp [S]
        rw [neg_apply, h0, map_neg]
        linarith
    · refine ⟨S, ?_, ?_, ?_⟩
      · intro z; exact hS z
      · intro w; exact ⟨(w.2, w.1), by simp [S]⟩
      · have h0 : S (1, 0) = ((0, 1) : ℝ × ℝ) := by simp [S]
        rw [h0]; simpa using hgt

end Work.Smooth.BoxGeneric.LocalArc
