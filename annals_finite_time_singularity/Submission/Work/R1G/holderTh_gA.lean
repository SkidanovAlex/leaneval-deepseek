import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.R1G.AnG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- The angular factor `Tf θ = sin(2θ)` is `2`-Lipschitz on all of `ℝ`. -/
lemma Tf_lipschitz (θ θ' : ℝ) : |Tf θ - Tf θ'| ≤ 2 * |θ - θ'| := by
  have h := Real.abs_sin_sub_sin_le (2 * θ) (2 * θ')
  have h2 : |2 * θ - 2 * θ'| = 2 * |θ - θ'| := by
    rw [show 2 * θ - 2 * θ' = 2 * (θ - θ') by ring, abs_mul]
    norm_num
  rw [h2] at h
  simpa [Tf] using h

/-- The radial factor is bounded by `1` on `[0,∞)`. -/
lemma Zf_abs_le_one {z : ℝ} (hz : 0 ≤ z) : |Zf z| ≤ 1 := by
  rw [abs_of_nonneg (Zf_nonneg hz)]
  exact Zf_le_one hz

/-- For `0 ≤ t ≤ 2` and `0 < β ≤ 1`, the Hölder exponent costs at most a factor
`2^{1-β}`: `t ≤ 2^{1-β} tᵝ`. -/
lemma rpow_le_two_mul_rpow (t β : ℝ) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hβ : 0 < β) (hβ1 : β ≤ 1) : t ≤ 2 ^ (1 - β) * t ^ β := by
  rcases eq_or_lt_of_le ht with h | htpos
  · rw [← h]
    rw [Real.zero_rpow (ne_of_gt hβ)]
    simp
  · have h1 : t ^ (1 - β) ≤ 2 ^ (1 - β) := Real.rpow_le_rpow ht ht2 (by linarith)
    have h2 : t ^ β * t ^ (1 - β) ≤ t ^ β * 2 ^ (1 - β) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht β)
    have h3 : t ^ (β + (1 - β)) = t ^ β * t ^ (1 - β) := Real.rpow_add htpos β (1 - β)
    have h4 : β + (1 - β) = 1 := by ring
    rw [h4, Real.rpow_one] at h3
    calc t = t ^ β * t ^ (1 - β) := h3
      _ ≤ t ^ β * 2 ^ (1 - β) := h2
      _ = 2 ^ (1 - β) * t ^ β := by ring

/-- **Angular Hölder continuity of `gA`**: on the quadrant `z ≥ 0`, `θ ∈ [0,π/2]`,
the map `θ ↦ gA z θ` is uniformly Hölder continuous with exponent `α ∈ (0,1]`. -/
theorem holderTh_gA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |Work.R1G.gA z θ - Work.R1G.gA z θ'| ≤ L * |θ - θ'| ^ α := by
  refine ⟨2 * 2 ^ (1 - α), ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  · intro z θ θ' hz hθ hθ'
    have hZ := Zf_abs_le_one hz
    have hT := Tf_lipschitz θ θ'
    have ht2 : |θ - θ'| ≤ 2 := by
      rw [abs_sub_le_iff]
      constructor
      · linarith [hθ.2, hθ'.1, Real.pi_lt_four]
      · linarith [hθ'.2, hθ.1, Real.pi_lt_four]
    have hgap := rpow_le_two_mul_rpow |θ - θ'| α (abs_nonneg _) ht2 hα hα1
    calc |gA z θ - gA z θ'|
        = |Zf z| * |Tf θ - Tf θ'| := by
          rw [gA, gA]
          rw [show Zf z * Tf θ - Zf z * Tf θ' = Zf z * (Tf θ - Tf θ') by ring,
            abs_mul]
      _ ≤ 1 * (2 * |θ - θ'|) :=
          mul_le_mul hZ hT (abs_nonneg _) (by norm_num)
      _ = 2 * |θ - θ'| := by ring
      _ ≤ 2 * (2 ^ (1 - α) * |θ - θ'| ^ α) :=
          mul_le_mul_of_nonneg_left hgap (by norm_num)
      _ = 2 * 2 ^ (1 - α) * |θ - θ'| ^ α := by ring

end Work.R1G
