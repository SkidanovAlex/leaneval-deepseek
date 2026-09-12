import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Geometry.Euclidean

/-- Scaling a vector of norm `≥ 1` by a real number of absolute value `> 1` gives a
vector of norm `> 1`. -/
private lemma one_lt_norm_smul_of_abs {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {c : ℝ} {w : E} (hc : 1 < |c|) (hw : 1 ≤ ‖w‖) :
    1 < ‖c • w‖ := by
  rw [norm_smul]
  calc (1 : ℝ) < |c| := hc
    _ = |c| * 1 := (mul_one _).symm
    _ ≤ |c| * ‖w‖ := mul_le_mul_of_nonneg_left hw (abs_nonneg c)

/-- **Escape of disjoint segments.** Let `[x₁,x₂]` and `[x₃,x₄]` be two disjoint segments in a
real inner product space whose direction vectors `x₂ - x₁` and `x₄ - x₃` are orthogonal of
length `≥ 1`, and such that the vector joining the two midpoints lies in the span of the two
directions. Then at least one endpoint of one of the segments has perpendicular distance `> 1`
from the line through the other segment's endpoints. -/
theorem escape_of_disjoint_segments_aux {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {x₁ x₂ x₃ x₄ : E}
    (hdisj : ∀ z : E, z ∈ segment ℝ x₁ x₂ → z ∈ segment ℝ x₃ x₄ → False)
    (hdecomp : ∃ α β : ℝ,
      (1 / 2 : ℝ) • (x₁ + x₂) - (1 / 2 : ℝ) • (x₃ + x₄) = α • (x₂ - x₁) + β • (x₄ - x₃))
    (hperp : inner ℝ (x₂ - x₁) (x₄ - x₃) = 0)
    (ha : 1 ≤ ‖x₂ - x₁‖) (hb : 1 ≤ ‖x₄ - x₃‖) :
    (∃ c : ℝ, ∃ n : E, x₃ - (1 / 2 : ℝ) • (x₁ + x₂) = c • (x₂ - x₁) + n ∧
        inner ℝ n (x₂ - x₁) = 0 ∧ 1 < ‖n‖)
    ∨ (∃ c : ℝ, ∃ n : E, x₄ - (1 / 2 : ℝ) • (x₁ + x₂) = c • (x₂ - x₁) + n ∧
        inner ℝ n (x₂ - x₁) = 0 ∧ 1 < ‖n‖)
    ∨ (∃ c : ℝ, ∃ n : E, x₁ - (1 / 2 : ℝ) • (x₃ + x₄) = c • (x₄ - x₃) + n ∧
        inner ℝ n (x₄ - x₃) = 0 ∧ 1 < ‖n‖)
    ∨ (∃ c : ℝ, ∃ n : E, x₂ - (1 / 2 : ℝ) • (x₃ + x₄) = c • (x₄ - x₃) + n ∧
        inner ℝ n (x₄ - x₃) = 0 ∧ 1 < ‖n‖) := by
  obtain ⟨α, β, hαβ⟩ := hdecomp
  -- Disjointness forces one of the two coefficients to exceed `1/2` in absolute value:
  -- otherwise the two segments would meet at the point
  -- `((1/2 + α) • x₁ + (1/2 - α) • x₂) = ((1/2 - β) • x₃ + (1/2 + β) • x₄)`.
  have hkey : (1 / 2 : ℝ) < |α| ∨ (1 / 2 : ℝ) < |β| := by
    by_contra h
    simp only [not_or, not_lt] at h
    obtain ⟨hα, hβ⟩ := h
    obtain ⟨hαlo, hαhi⟩ := abs_le.mp hα
    obtain ⟨hβlo, hβhi⟩ := abs_le.mp hβ
    have hz_eq : ((1 / 2 : ℝ) + α) • x₁ + ((1 / 2 : ℝ) - α) • x₂
        = ((1 / 2 : ℝ) - β) • x₃ + ((1 / 2 : ℝ) + β) • x₄ := by
      have h1 : ((1 / 2 : ℝ) + α) • x₁ + ((1 / 2 : ℝ) - α) • x₂
            - (((1 / 2 : ℝ) - β) • x₃ + ((1 / 2 : ℝ) + β) • x₄)
          = ((1 / 2 : ℝ) • (x₁ + x₂) - (1 / 2 : ℝ) • (x₃ + x₄))
            - (α • (x₂ - x₁) + β • (x₄ - x₃)) := by
        module
      rw [← sub_eq_zero, h1, hαβ, sub_self]
    have hz1 : ((1 / 2 : ℝ) + α) • x₁ + ((1 / 2 : ℝ) - α) • x₂ ∈ segment ℝ x₁ x₂ :=
      ⟨(1 / 2 : ℝ) + α, (1 / 2 : ℝ) - α, by linarith, by linarith, by ring, rfl⟩
    have hz2 : ((1 / 2 : ℝ) + α) • x₁ + ((1 / 2 : ℝ) - α) • x₂ ∈ segment ℝ x₃ x₄ := by
      rw [hz_eq]
      exact ⟨(1 / 2 : ℝ) - β, (1 / 2 : ℝ) + β, by linarith, by linarith, by ring, rfl⟩
    exact hdisj _ hz1 hz2
  rcases hkey with hα | hβ
  · rcases lt_abs.mp hα with hαpos | hαneg
    · -- `α > 1/2`: escape at `x₂` from the line `x₃x₄`.
      refine Or.inr (Or.inr (Or.inr ⟨β, (α + 1 / 2) • (x₂ - x₁), ?_, ?_, ?_⟩))
      · have h1 : x₂ - (1 / 2 : ℝ) • (x₃ + x₄) - (β • (x₄ - x₃) + (α + 1 / 2) • (x₂ - x₁))
            = ((1 / 2 : ℝ) • (x₁ + x₂) - (1 / 2 : ℝ) • (x₃ + x₄))
              - (α • (x₂ - x₁) + β • (x₄ - x₃)) := by
          module
        rw [← sub_eq_zero, h1, hαβ, sub_self]
      · rw [real_inner_smul_left, hperp, mul_zero]
      · refine one_lt_norm_smul_of_abs ?_ ha
        rw [abs_of_pos (show (0 : ℝ) < α + 1 / 2 by linarith)]
        linarith
    · -- `α < -1/2`: escape at `x₁` from the line `x₃x₄`.
      refine Or.inr (Or.inr (Or.inl ⟨β, (α - 1 / 2) • (x₂ - x₁), ?_, ?_, ?_⟩))
      · have h1 : x₁ - (1 / 2 : ℝ) • (x₃ + x₄) - (β • (x₄ - x₃) + (α - 1 / 2) • (x₂ - x₁))
            = ((1 / 2 : ℝ) • (x₁ + x₂) - (1 / 2 : ℝ) • (x₃ + x₄))
              - (α • (x₂ - x₁) + β • (x₄ - x₃)) := by
          module
        rw [← sub_eq_zero, h1, hαβ, sub_self]
      · rw [real_inner_smul_left, hperp, mul_zero]
      · refine one_lt_norm_smul_of_abs ?_ ha
        rw [abs_of_neg (show α - 1 / 2 < (0 : ℝ) by linarith)]
        linarith
  · rcases lt_abs.mp hβ with hβpos | hβneg
    · -- `β > 1/2`: escape at `x₃` from the line `x₁x₂`.
      refine Or.inl ⟨-α, (-(β + 1 / 2)) • (x₄ - x₃), ?_, ?_, ?_⟩
      · have h1 : x₃ - (1 / 2 : ℝ) • (x₁ + x₂) - ((-α) • (x₂ - x₁) + (-(β + 1 / 2)) • (x₄ - x₃))
            = (α • (x₂ - x₁) + β • (x₄ - x₃))
              - ((1 / 2 : ℝ) • (x₁ + x₂) - (1 / 2 : ℝ) • (x₃ + x₄)) := by
          module
        rw [← sub_eq_zero, h1, ← hαβ, sub_self]
      · rw [real_inner_smul_left, real_inner_comm, hperp, mul_zero]
      · refine one_lt_norm_smul_of_abs ?_ hb
        rw [abs_of_neg (show -(β + 1 / 2) < (0 : ℝ) by linarith)]
        linarith
    · -- `β < -1/2`: escape at `x₄` from the line `x₁x₂`.
      refine Or.inr (Or.inl ⟨-α, ((1 / 2 : ℝ) - β) • (x₄ - x₃), ?_, ?_, ?_⟩)
      · have h1 : x₄ - (1 / 2 : ℝ) • (x₁ + x₂) - ((-α) • (x₂ - x₁) + ((1 / 2 : ℝ) - β) • (x₄ - x₃))
            = (α • (x₂ - x₁) + β • (x₄ - x₃))
              - ((1 / 2 : ℝ) • (x₁ + x₂) - (1 / 2 : ℝ) • (x₃ + x₄)) := by
          module
        rw [← sub_eq_zero, h1, ← hαβ, sub_self]
      · rw [real_inner_smul_left, real_inner_comm, hperp, mul_zero]
      · refine one_lt_norm_smul_of_abs ?_ hb
        rw [abs_of_pos (show (0 : ℝ) < 1 / 2 - β by linarith)]
        linarith

theorem escape_of_disjoint_segments {x₁ x₂ x₃ x₄ : EuclideanSpace ℝ (Fin 3)}
    (hdisj : ∀ z : EuclideanSpace ℝ (Fin 3), z ∈ segment ℝ x₁ x₂ → z ∈ segment ℝ x₃ x₄ → False)
    (hdecomp : ∃ α β : ℝ,
      (1 / 2 : ℝ) • (x₁ + x₂) - (1 / 2 : ℝ) • (x₃ + x₄) = α • (x₂ - x₁) + β • (x₄ - x₃))
    (hperp : inner ℝ (x₂ - x₁) (x₄ - x₃) = 0)
    (ha : 1 ≤ ‖x₂ - x₁‖) (hb : 1 ≤ ‖x₄ - x₃‖) :
    (∃ c : ℝ, ∃ n : EuclideanSpace ℝ (Fin 3), x₃ - (1 / 2 : ℝ) • (x₁ + x₂) = c • (x₂ - x₁) + n ∧
        inner ℝ n (x₂ - x₁) = 0 ∧ 1 < ‖n‖)
    ∨ (∃ c : ℝ, ∃ n : EuclideanSpace ℝ (Fin 3), x₄ - (1 / 2 : ℝ) • (x₁ + x₂) = c • (x₂ - x₁) + n ∧
        inner ℝ n (x₂ - x₁) = 0 ∧ 1 < ‖n‖)
    ∨ (∃ c : ℝ, ∃ n : EuclideanSpace ℝ (Fin 3), x₁ - (1 / 2 : ℝ) • (x₃ + x₄) = c • (x₄ - x₃) + n ∧
        inner ℝ n (x₄ - x₃) = 0 ∧ 1 < ‖n‖)
    ∨ (∃ c : ℝ, ∃ n : EuclideanSpace ℝ (Fin 3), x₂ - (1 / 2 : ℝ) • (x₃ + x₄) = c • (x₄ - x₃) + n ∧
        inner ℝ n (x₄ - x₃) = 0 ∧ 1 < ‖n‖) :=
  escape_of_disjoint_segments_aux hdisj hdecomp hperp ha hb

end Commons.Geometry.Euclidean