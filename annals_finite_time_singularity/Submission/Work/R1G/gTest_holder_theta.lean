import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.R1G.GTest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- The angular factor `gPsi θ = sin(2θ)` is `2`-Lipschitz on all of `ℝ`. -/
lemma gPsi_lipschitz (θ θ' : ℝ) : |gPsi θ - gPsi θ'| ≤ 2 * |θ - θ'| := by
  have h := Real.abs_sin_sub_sin_le (2 * θ) (2 * θ')
  have h2 : |2 * θ - 2 * θ'| = 2 * |θ - θ'| := by
    rw [show 2 * θ - 2 * θ' = 2 * (θ - θ') by ring, abs_mul]
    norm_num
  rw [h2] at h
  simpa [gPsi] using h

/-- The radial factor `gPhi z = z²e^{-z}` is bounded by `2` on `[0,∞)`. -/
lemma gPhi_abs_le (z : ℝ) (hz : 0 ≤ z) : |gPhi z| ≤ 2 := by
  unfold gPhi
  rw [abs_of_nonneg (by positivity)]
  have h := Real.sum_le_exp_of_nonneg hz 3
  have hsum : ∑ i ∈ Finset.range 3, z ^ i / (Nat.factorial i : ℝ) = 1 + z + z^2/2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have hz2le : z^2 / 2 ≤ Real.exp z := by linarith
  have hz2le' : z^2 ≤ 2 * Real.exp z := by linarith
  rw [Real.exp_neg]
  rw [show z^2 * (Real.exp z)⁻¹ = z^2 / Real.exp z by rw [div_eq_mul_inv]]
  rw [div_le_iff₀ (Real.exp_pos z)]
  linarith

/-- For `0 ≤ t ≤ 2` and `0 < β ≤ 1`, the Hölder exponent costs at most a factor `2^{1-β}`:
`t ≤ 2^{1-β} tᵝ`. -/
lemma rpow_gap (t β : ℝ) (ht : 0 ≤ t) (ht2 : t ≤ 2) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    t ≤ 2^(1-β) * t^β := by
  rcases eq_or_lt_of_le ht with h | htpos
  · rw [← h]
    rw [Real.zero_rpow (ne_of_gt hβ)]
    simp
  · have h1 : t^(1-β) ≤ 2^(1-β) := Real.rpow_le_rpow ht ht2 (by linarith)
    have h2 : t^β * t^(1-β) ≤ t^β * 2^(1-β) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht β)
    have h3 : t^(β + (1-β)) = t^β * t^(1-β) := Real.rpow_add htpos β (1-β)
    have h4 : β + (1-β) = 1 := by ring
    rw [h4, Real.rpow_one] at h3
    calc t = t^β * t^(1-β) := h3
      _ ≤ t^β * 2^(1-β) := h2
      _ = 2^(1-β) * t^β := by ring

theorem gTest_holder_theta {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (ε : ℝ) :
    ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |gTest ε z θ - gTest ε z θ'| ≤ Lθ * |θ - θ'| ^ β := by
  refine ⟨4 * |ε| * 2^(1-β), by positivity, ?_⟩
  intro z θ θ' hz hθ hθ'
  have hphi := gPhi_abs_le z hz
  have hpsi := gPsi_lipschitz θ θ'
  have hπ : Real.pi < 4 := Real.pi_lt_four
  have ht2 : |θ - θ'| ≤ 2 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2, hπ]
  have hgap := rpow_gap |θ - θ'| β (abs_nonneg _) ht2 hβ hβ1
  calc |gTest ε z θ - gTest ε z θ'|
      = |ε| * |gPhi z| * |gPsi θ - gPsi θ'| := by
        have heq : ε * gPhi z * gPsi θ - ε * gPhi z * gPsi θ'
            = ε * gPhi z * (gPsi θ - gPsi θ') := by ring
        rw [gTest_apply, gTest_apply, heq, abs_mul, abs_mul]
    _ ≤ |ε| * 2 * (2 * |θ - θ'|) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hphi (abs_nonneg ε)
        · exact hpsi
        · exact abs_nonneg _
        · positivity
    _ = 4 * |ε| * |θ - θ'| := by ring
    _ ≤ 4 * |ε| * (2^(1-β) * |θ - θ'|^β) := by
        apply mul_le_mul_of_nonneg_left hgap
        positivity
    _ = 4 * |ε| * 2^(1-β) * |θ - θ'|^β := by ring

end Work.R1G
