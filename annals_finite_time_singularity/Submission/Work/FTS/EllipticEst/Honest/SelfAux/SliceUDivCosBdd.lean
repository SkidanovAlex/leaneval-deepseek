import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.SelfAux

/-- **`u / cos θ` is bounded on `(0, π/2)`.**  If `|u| ≤ B` on `(0, π/2)` and
`|u θ| ≤ M (π/2 - θ)` there, then `u / cos θ` is bounded on `(0, π/2)`.

Proof route: on `(0, π/2)` one has `Real.cos θ > 0` (`Real.cos_pos_of_mem_Ioo`) and
`Real.cos θ = Real.sin (π/2 - θ) ≥ (2/π)(π/2 - θ)` (`Real.mul_le_sin`).  So for `θ ∈ (0, π/4]`,
`cos θ ≥ (2/π)(π/4) = 1/2` and `|u θ / cos θ| ≤ 2B`; for `θ ∈ [π/4, π/2)`,
`|u θ / cos θ| ≤ M (π/2 - θ) / ((2/π)(π/2 - θ)) = (π/2) M`.  Hence
`K = max (2B) ((π/2) M)` works (both `B ≥ 0` and `M ≥ 0` follow from the hypotheses and the
non-emptiness of `(0, π/2)`, and `Real.cos θ > 0` makes the division safe).

Please declare it at the ROOT namespace (no `namespace` wrapper), so that its name is exactly
`SliceUDivCosBdd`. -/
theorem SliceUDivCosBdd (u : ℝ → ℝ) {B M : ℝ}
    (hB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ B)
    (hlin : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ M * (Real.pi / 2 - θ)) :
    ∃ K : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ / Real.cos θ| ≤ K := by
  -- `π/4` lies in `(0, π/2)`, so the bounds `B, M ≥ 0` follow from the hypotheses.
  have h4mem : (Real.pi / 4 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB _ h4mem)
  have hM0 : 0 ≤ M := by
    have h := hlin _ h4mem
    have h4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
    have h2 : 0 ≤ M * (Real.pi / 4) := by
      have h3 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
      rw [h3] at h
      exact le_trans (abs_nonneg _) h
    exact (mul_nonneg_iff_of_pos_right h4).mp h2
  refine ⟨max (2 * B) (Real.pi / 2 * M), fun θ hθ => ?_⟩
  -- `cos θ > 0` on `(0, π/2)`, so the division is safe.
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  rw [abs_div, abs_of_pos hcos]
  -- `cos θ = sin (π/2 - θ) ≥ (2/π)(π/2 - θ)`.
  have hcoslb : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
    have hx0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have hxle : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
    have h := Real.mul_le_sin hx0 hxle
    rwa [Real.sin_pi_div_two_sub] at h
  rcases le_or_gt θ (Real.pi / 4) with hθ4 | hθ4
  · -- `θ ≤ π/4`: then `cos θ ≥ 1/2`, so `|u θ| / cos θ ≤ 2B`.
    have hcos12 : (1 : ℝ) / 2 ≤ Real.cos θ := by
      have hmono : (2 / Real.pi) * (Real.pi / 4) ≤ (2 / Real.pi) * (Real.pi / 2 - θ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      have h2 : (2 / Real.pi) * (Real.pi / 4) = 1 / 2 := by field_simp; ring
      linarith [hcoslb, hmono]
    calc |u θ| / Real.cos θ ≤ B / Real.cos θ := by
          apply div_le_div_of_nonneg_right (hB θ hθ) (le_of_lt hcos)
      _ ≤ B / (1 / 2) := by
          apply div_le_div_of_nonneg_left hB0 (by norm_num) hcos12
      _ = 2 * B := by ring
      _ ≤ max (2 * B) (Real.pi / 2 * M) := le_max_left _ _
  · -- `θ > π/4`: then `|u θ| / cos θ ≤ M(π/2 - θ) / ((2/π)(π/2 - θ)) = (π/2) M`.
    have hpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hden : 0 < (2 / Real.pi) * (Real.pi / 2 - θ) := by
      apply mul_pos (by positivity) hpos
    calc |u θ| / Real.cos θ ≤ M * (Real.pi / 2 - θ) / Real.cos θ := by
          apply div_le_div_of_nonneg_right (hlin θ hθ) (le_of_lt hcos)
      _ ≤ M * (Real.pi / 2 - θ) / ((2 / Real.pi) * (Real.pi / 2 - θ)) := by
          apply div_le_div_of_nonneg_left (by positivity) hden hcoslb
      _ = Real.pi / 2 * M := by
          rw [mul_div_mul_right _ _ (by linarith : Real.pi / 2 - θ ≠ 0)]
          field_simp
      _ ≤ max (2 * B) (Real.pi / 2 * M) := le_max_right _ _

end Work.FTS.EllipticEst.Honest.SelfAux
